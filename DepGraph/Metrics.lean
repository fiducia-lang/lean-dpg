/-
# DepGraph.Metrics

Per-declaration complexity metrics, read off the compiled environment.

| column       | meaning                                                                        |
|--------------|--------------------------------------------------------------------------------|
| `lines`      | source lines of the declaration (statement + proof script)                     |
| `term_size`  | distinct subterms of the proof/definition term (DAG size, sharing respected),  |
|              | summed over the compiler-generated auxiliaries the declaration owns            |
| `term_depth` | approximate depth of the term                                                  |
| `cyclomatic` | 1 + number of eliminator applications in the term (`casesOn`, `rec`, `recOn`,  |
|              | `brecOn`, `*.elim`, `dite`, `ite`, `Decidable.byCases`, `match_N`): the        |
|              | McCabe analogue for proofs — decision points of the term                       |
| `fan_out`    | declarations in the graph this one uses                                        |
| `fan_in`     | declarations in the graph that use this one                                    |
| `term_per_line` | `term_size / lines`: high values mean the script delegates much work to     |
|              | automation, which is where proofs tend to break on library upgrades            |

Term columns are 0 for inductive types, axioms and other declarations without a written term.

Only declarations that survive the graph filters (`--to`, `--from`, `--props-only`, ...) are
reported. Fan-in/out are counted on the graph before transitive reduction.
-/
import DepGraph.Core
open Lean Meta

namespace DepGraph

structure Metrics where
  name       : Name
  kind       : Kind
  isProp     : Bool
  module     : Name
  line       : Nat
  lines      : Nat
  termSize   : Nat
  termDepth  : Nat
  cyclomatic : Nat
  fanOut     : Nat
  fanIn      : Nat
  deriving Inhabited

def Metrics.termPerLine (m : Metrics) : Float :=
  if m.lines == 0 then 0 else m.termSize.toFloat / m.lines.toFloat

private def isEliminator (c : Name) : Bool :=
  let last := match c with | .str _ s => s | _ => ""
  last == "casesOn" || last == "rec" || last == "recOn" || last == "brecOn" || last == "elim"
  || last.startsWith "match_"
  || c == ``dite || c == ``ite || c == ``Decidable.byCases || c == ``Classical.byCases

/-- DAG size and number of eliminator applications of `e`, sharing respected. -/
partial def termStats (e : Expr) : Nat × Nat := Id.run do
  let mut seen : Std.HashSet Expr := {}
  let mut stack := [e]
  let mut elims := 0
  while h : stack ≠ [] do
    let x := stack.head h
    stack := stack.tail
    if seen.contains x then continue
    seen := seen.insert x
    if x.isApp then
      if let .const c _ := x.getAppFn then
        if isEliminator c then elims := elims + 1
    stack := match x with
      | .app f a => f :: a :: stack
      | .lam _ t b _ | .forallE _ t b _ => t :: b :: stack
      | .letE _ t v b _ => t :: v :: b :: stack
      | .mdata _ b | .proj _ _ b => b :: stack
      | _ => stack
  return (seen.size, elims)

/-- Metrics for every node of the graph `build cfg` would produce. -/
def metrics (cfg : Config) : MetaM (Array Metrics) := do
  if cfg.level != .decl then throwError "DepGraph: metrics are only available at `decl` level"
  let env ← getEnv
  -- the filtered graph decides which nodes are reported; fan-in/out come from the full edge set
  let full ← extract cfg
  let shown := full.apply { cfg with keepTrans := true }
  let shownSet : Std.HashSet Name := Std.HashSet.ofList (shown.nodes.map (·.name)).toList
  let fanOut := shown.edges.foldl (fun (m : Std.HashMap Name Nat) e => m.insert e.src (m.getD e.src 0 + 1)) {}
  let fanIn  := shown.edges.foldl (fun (m : Std.HashMap Name Nat) e => m.insert e.dst (m.getD e.dst 0 + 1)) {}
  -- accumulate term statistics over each node and the auxiliaries it owns
  let mut size  : Std.HashMap Name Nat := {}
  let mut elims : Std.HashMap Name Nat := {}
  let mut depth : Std.HashMap Name Nat := {}
  let modIdxs := cfg.modules.filterMap fun m => env.header.moduleNames.findIdx? (· == m)
  for (n, ci) in env.constants.toList do
    let inScope := match env.getModuleIdxFor? n with
      | some i => modIdxs.contains i
      | none => false
    if !inScope then continue
    let some owner := rootDecl env cfg n | continue
    if !shownSet.contains owner then continue
    -- only theorems and definitions have a proof/definition term worth measuring; an inductive
    -- type's recursors and `noConfusion` machinery are generated, not written
    unless (env.find? owner).any (fun c => c matches .thmInfo _ | .defnInfo _ | .opaqueInfo _) do continue
    let some v := ci.value? (allowOpaque := true) | continue
    let (s, el) := termStats v
    size  := size.insert owner (size.getD owner 0 + s)
    elims := elims.insert owner (elims.getD owner 0 + el)
    if n == owner then depth := depth.insert owner v.approxDepth.toNat
  let mut out : Array Metrics := #[]
  for node in shown.nodes do
    let lines := match ← findDeclarationRanges? node.name with
      | some r => r.range.endPos.line - r.range.pos.line + 1
      | none   => 0
    out := out.push {
      name := node.name, kind := node.kind, isProp := node.isProp, module := node.module,
      line := node.line, lines,
      termSize := size.getD node.name 0, termDepth := depth.getD node.name 0,
      cyclomatic := if size.contains node.name then 1 + elims.getD node.name 0 else 0,
      fanOut := fanOut.getD node.name 0, fanIn := fanIn.getD node.name 0 }
  return out

private def csvField (s : String) : String :=
  if s.any (fun c => c == ',' || c == '"' || c == '\n') then "\"" ++ s.replace "\"" "\"\"" ++ "\"" else s

/-- One decimal place, without relying on `Float.toString`'s formatting. -/
private def fmt1 (x : Float) : String :=
  let t := (x * 10).round.toUInt64.toNat
  s!"{t / 10}.{t % 10}"

def metricsCsv (ms : Array Metrics) : String := Id.run do
  let mut out := "name,kind,prop,module,line,lines,term_size,term_depth,cyclomatic,fan_out,fan_in,term_per_line\n"
  for m in ms do
    out := out ++ String.intercalate "," [csvField m.name.toString, toString m.kind, toString m.isProp,
      csvField m.module.toString, toString m.line, toString m.lines, toString m.termSize,
      toString m.termDepth, toString m.cyclomatic, toString m.fanOut, toString m.fanIn,
      fmt1 m.termPerLine] ++ "\n"
  return out

/-- The `k` largest declarations by `key`, as display lines. -/
def topBy (ms : Array Metrics) (key : Metrics → Nat) (k : Nat := 5) : Array Metrics :=
  (ms.qsort (fun a b => key a > key b)).extract 0 k

end DepGraph
