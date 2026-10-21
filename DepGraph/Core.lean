/-
# DepGraph.Core

Dependency graphs for Lean 4 at three levels, in the spirit of Rocq's
`coq-dpdgraph`:

* `decl`      — declarations and the constants their types and bodies reference,
* `namespace` — the declaration graph collapsed onto namespaces,
* `module`    — modules and their imports (what `lake exe graph` shows).

Everything is read off the compiled environment, never the source text: for
each user-level declaration we collect the constants referenced by its type and
its proof/definition term, so dependencies introduced by tactics such as `simp`
or `aesop` are included.  Auxiliary declarations produced by the compiler
(`foo.match_1`, `foo.proof_1`, `foo._unary`, `Foo.rec`, `Foo.casesOn`,
structure projections, derived instances ...) are folded into the declaration
they belong to.
-/
import Lean
open Lean Meta

namespace DepGraph

inductive Kind where
  | theorem | definition | opaque | axiom | inductive | other
  | namespace | module
  deriving BEq, Repr, Inhabited, DecidableEq

def Kind.toString : Kind → String
  | .theorem    => "theorem"
  | .definition => "def"
  | .opaque     => "opaque"
  | .axiom      => "axiom"
  | .inductive  => "inductive"
  | .other      => "other"
  | .namespace  => "namespace"
  | .module     => "module"

/-- Granularity of the graph. -/
inductive Level where
  | decl | namespace | module
  deriving BEq, Repr, Inhabited, DecidableEq

def Level.ofString? : String → Option Level
  | "decl" | "declaration" | "declarations" => some .decl
  | "namespace" | "namespaces" => some .namespace
  | "module" | "modules" | "import" | "imports" => some .module
  | _ => none

instance : ToString Kind := ⟨Kind.toString⟩

structure Node where
  name   : Name
  kind   : Kind
  /-- The declaration's type is a proposition (a lemma, or a `Prop`-valued `def`). -/
  isProp : Bool
  module : Name
  line   : Nat
  /-- Number of graph edges pointing at this node. -/
  uses   : Nat := 0
  deriving Inhabited

structure Edge where
  src    : Name
  dst    : Name
  /-- How many times `dst` occurs in `src` (type + body + auxiliaries). -/
  weight : Nat
  deriving Inhabited

structure Graph where
  nodes : Array Node
  edges : Array Edge
  deriving Inhabited

structure Config where
  /-- Modules whose declarations become nodes (`decl`/`namespace`), or the roots of the import
  closure (`module`). -/
  modules   : Array Name
  level     : Level := .decl
  /-- `module` level: keep only modules under one of these prefixes. `none` (the default) means
  the top-level namespaces of the requested modules, i.e. roughly "the current package", as
  `lake exe graph` does; `some #[]` means no restriction. -/
  onlyPrefixes : Option (Array Name) := none
  /-- `module` level: drop modules under one of these prefixes. -/
  excludePrefixes : Array Name := #[`Init, `Lean, `Std, `Lake]
  /-- Keep only the declarations that `toDecl` transitively depends on. -/
  toDecl    : Option Name := none
  /-- Keep only the declarations that transitively depend on `fromDecl`. -/
  fromDecl  : Option Name := none
  /-- Keep only propositions (theorems and `Prop`-valued definitions). -/
  propsOnly : Bool := false
  /-- Do not remove transitively implied edges. -/
  keepTrans : Bool := false
  /-- Show derived/auto-generated instances as nodes. -/
  instances : Bool := false
  deriving Inhabited

/-! ## Which declarations count as "user level" -/

private def generatedSuffixes : List String :=
  ["ctorIdx", "ctorElim", "ctorElimType", "elim", "noConfusion", "noConfusionType",
   "sizeOf_spec", "injEq", "inj", "mk.injEq", "mk.inj", "below", "ibelow", "brecOn",
   "binductionOn", "casesOn", "recOn", "rec", "_sizeOf_1", "_sizeOf_inst"]

private def isGeneratedComponent (s : String) : Bool :=
  s.startsWith "match_" || s.startsWith "proof_" || s.startsWith "eq_" || s.startsWith "_"
  || s.startsWith "spec" && s.length > 4 && (s.drop 4).all Char.isDigit
  || s == "eq_def" || s == "eq_unfold" || s == "induct" || s == "mutual_induct"
  || s == "congr_simp" || s == "fun_cases"
  || generatedSuffixes.contains s

/-- Is `n` a declaration the user wrote (as opposed to one the compiler generated)? -/
def isUserDecl (env : Environment) (cfg : Config) (n : Name) : Bool :=
  match env.find? n with
  | none => false
  | some ci =>
    !n.isInternal
    && !(ci matches .ctorInfo _ | .recInfo _ | .quotInfo _)
    && !isAuxRecursor env n && !isNoConfusion env n && !env.isProjectionFn n
    && !(n.components.any fun c => isGeneratedComponent c.toString)
    && (cfg.instances || !(n.components.any fun c => c.toString.startsWith "inst"))

/-- Fold an arbitrary constant name onto the user declaration it belongs to. -/
partial def rootDecl (env : Environment) (cfg : Config) : Name → Option Name
  | n@(.str p _) => if isUserDecl env cfg n then some n else rootDecl env cfg p
  | n@(.num p _) => if isUserDecl env cfg n then some n else rootDecl env cfg p
  | .anonymous   => none

def kindOf (ci : ConstantInfo) : Kind :=
  match ci with
  | .thmInfo _    => .theorem
  | .defnInfo _   => .definition
  | .opaqueInfo _ => .opaque
  | .axiomInfo _  => .axiom
  | .inductInfo _ => .inductive
  | _             => .other

/-! ## Extraction -/

/-- Constants referenced by the type and body of `ci`, with multiplicity. -/
private def usedConstantsWithMultiplicity (ci : ConstantInfo) : Array Name :=
  let fromType := ci.type.getUsedConstants
  match ci.value? (allowOpaque := true) with
  | some v => fromType ++ v.getUsedConstants
  | none   => fromType

/-- Build the raw (unfiltered) graph of every user declaration in `cfg.modules`. -/
def extract (cfg : Config) : MetaM Graph := do
  let env ← getEnv
  let mut modIdxs : Array ModuleIdx := #[]
  for m in cfg.modules do
    match env.header.moduleNames.findIdx? (· == m) with
    | some i => modIdxs := modIdxs.push i
    | none   => throwError "DepGraph: module `{m}` is not imported"
  let inScope (n : Name) : Bool :=
    match env.getModuleIdxFor? n with
    | some i => modIdxs.contains i
    | none   => false
  -- 1. nodes
  let mut nodes : Array Node := #[]
  let mut owner : Std.HashMap Name Name := {}   -- every in-scope constant ↦ its user decl
  for (n, ci) in env.constants.toList do
    if inScope n then
      if let some r := rootDecl env cfg n then
        owner := owner.insert n r
        if r == n then
          let isProp ← try Meta.isProp ci.type catch _ => pure false
          let line := match ← findDeclarationRanges? n with
            | some r => r.range.pos.line
            | none   => 0
          let module := env.header.moduleNames[env.getModuleIdxFor? n |>.get!]!
          nodes := nodes.push { name := n, kind := kindOf ci, isProp, module, line }
  let sortedNodes := nodes.qsort (fun a b => a.line < b.line || (a.line == b.line && Name.lt a.name b.name))
  let nodeSet : Std.HashSet Name := Std.HashSet.ofList (sortedNodes.map (·.name)).toList
  -- 2. edges: for each user decl, union the constants used by it and by all auxiliaries it owns
  let mut counts : Std.HashMap (Name × Name) Nat := {}
  for (n, ci) in env.constants.toList do
    if let some src := owner[n]? then
      for u in usedConstantsWithMultiplicity ci do
        if let some dst := (owner[u]?).orElse (fun _ => rootDecl env cfg u) then
          if dst != src && nodeSet.contains dst then
            counts := counts.insert (src, dst) (counts.getD (src, dst) 0 + 1)
  let mut edges : Array Edge := #[]
  for ((src, dst), w) in counts.toList do
    edges := edges.push { src, dst, weight := w }
  let sortedEdges := edges.qsort (fun a b => Name.lt a.src b.src || (a.src == b.src && Name.lt a.dst b.dst))
  return { nodes := sortedNodes, edges := sortedEdges }

/-- The import graph: the transitive import closure of `cfg.modules`, filtered by `cfg.onlyPrefixes` and
`cfg.excludePrefixes`. An edge `A → B` means `A` imports `B` directly. -/
def extractModules (cfg : Config) : MetaM Graph := do
  let env ← getEnv
  let names := env.header.moduleNames
  let only : Array Name := cfg.onlyPrefixes.getD (cfg.modules.map (·.getRoot))
  let wanted (m : Name) : Bool :=
    (only.isEmpty || only.any (fun p => p.isPrefixOf m)) && !cfg.excludePrefixes.any (fun p => p.isPrefixOf m)
  let importsOf (m : Name) : Array Name :=
    match names.findIdx? (· == m) with
    | some i => env.header.moduleData[i]!.imports.map (·.module)
    | none   => #[]
  for m in cfg.modules do
    if names.findIdx? (· == m) |>.isNone then throwError "DepGraph: module `{m}` is not imported"
  -- BFS over imports, starting from the requested modules
  let mut seen : Std.HashSet Name := {}
  let mut queue := cfg.modules.toList
  let mut nodes : Array Node := #[]
  let mut edges : Array Edge := #[]
  while h : queue ≠ [] do
    let m := queue.head h
    queue := queue.tail
    if seen.contains m || !wanted m then continue
    seen := seen.insert m
    nodes := nodes.push { name := m, kind := .module, isProp := false, module := m, line := 0 }
    for i in importsOf m do
      if wanted i then
        edges := edges.push { src := m, dst := i, weight := 1 }
        queue := i :: queue
  let sortedNodes := nodes.qsort (fun a b => Name.lt a.name b.name)
  let sortedEdges := edges.qsort (fun a b => Name.lt a.src b.src || (a.src == b.src && Name.lt a.dst b.dst))
  return { nodes := sortedNodes, edges := sortedEdges }

/-! ## Graph transformations -/

/-- Merge nodes that `f` maps to the same name (self-loops dropped, weights summed). -/
def Graph.collapse (g : Graph) (f : Name → Name) (kind : Kind) : Graph := Id.run do
  let mut nodes : Array Node := #[]
  let mut seen : Std.HashSet Name := {}
  for n in g.nodes do
    let m := f n.name
    if !seen.contains m then
      seen := seen.insert m
      nodes := nodes.push { n with name := m, kind, isProp := false }
  let mut w : Std.HashMap (Name × Name) Nat := {}
  for e in g.edges do
    let (a, b) := (f e.src, f e.dst)
    if a != b then w := w.insert (a, b) (w.getD (a, b) 0 + e.weight)
  let edges := (w.toList.map fun ((a, b), k) => { src := a, dst := b, weight := k : Edge }).toArray
  return { nodes, edges := edges.qsort (fun a b => Name.lt a.src b.src || (a.src == b.src && Name.lt a.dst b.dst)) }

/-- The namespace a declaration lives in (`_root_` for top-level names). -/
def namespaceOf (n : Name) : Name :=
  match n.getPrefix with
  | .anonymous => `_root_
  | p => p

private def successors (g : Graph) : Std.HashMap Name (Array Name) :=
  g.edges.foldl (fun m e => m.insert e.src ((m.getD e.src #[]).push e.dst)) {}

private def predecessors (g : Graph) : Std.HashMap Name (Array Name) :=
  g.edges.foldl (fun m e => m.insert e.dst ((m.getD e.dst #[]).push e.src)) {}

/-- All nodes reachable from `start` following `adj` (excluding `start` unless on a cycle). -/
private partial def reachable (adj : Std.HashMap Name (Array Name)) (start : Name) : Std.HashSet Name :=
  let rec go (stack : List Name) (seen : Std.HashSet Name) : Std.HashSet Name :=
    match stack with
    | [] => seen
    | x :: rest =>
      let next := (adj.getD x #[]).toList.filter (fun y => !seen.contains y)
      go (next ++ rest) (next.foldl (fun s y => s.insert y) seen)
  go [start] {}

/-- Restrict to a set of node names, dropping dangling edges. -/
def Graph.restrict (g : Graph) (keep : Name → Bool) : Graph :=
  { nodes := g.nodes.filter (fun n => keep n.name)
    edges := g.edges.filter (fun e => keep e.src && keep e.dst) }

/-- Everything `root` transitively depends on (plus `root`). -/
def Graph.ancestorsOf (g : Graph) (root : Name) : Graph :=
  let r := (reachable (successors g) root).insert root
  g.restrict r.contains

/-- Everything that transitively depends on `root` (plus `root`). -/
def Graph.dependentsOf (g : Graph) (root : Name) : Graph :=
  let r := (reachable (predecessors g) root).insert root
  g.restrict r.contains

/-- Remove an edge `a → b` whenever `b` is reachable from `a` through another successor. -/
def Graph.transitiveReduction (g : Graph) : Graph :=
  let succ := successors g
  let reachCache : Std.HashMap Name (Std.HashSet Name) :=
    g.nodes.foldl (fun m n => m.insert n.name (reachable succ n.name)) {}
  let redundant (e : Edge) : Bool :=
    (succ.getD e.src #[]).any fun c =>
      c != e.dst && (reachCache.getD c {}).contains e.dst
  { g with edges := g.edges.filter (fun e => !redundant e) }

/-- Fill in the `uses` counter of every node from the current edge set. -/
def Graph.countUses (g : Graph) : Graph :=
  let pred := predecessors g
  { g with nodes := g.nodes.map fun n => { n with uses := (pred.getD n.name #[]).size } }

/-- Apply the filters in `cfg` to a raw graph. -/
def Graph.apply (g : Graph) (cfg : Config) : Graph := Id.run do
  let mut g := g
  -- a root given as a declaration name is mapped onto its namespace at `namespace` level
  let resolve (r : Name) : Name :=
    if g.nodes.any (·.name == r) then r
    else if g.nodes.any (·.name == namespaceOf r) then namespaceOf r
    else r
  if let some r := cfg.toDecl then g := g.ancestorsOf (resolve r)
  if let some r := cfg.fromDecl then g := g.dependentsOf (resolve r)
  if cfg.propsOnly then g := g.restrict (fun n => (g.nodes.find? (·.name == n)).any (·.isProp))
  g := g.countUses               -- usage counts over the full (pre-reduction) edge set
  if !cfg.keepTrans then g := g.transitiveReduction
  return g

/-- Nodes that nothing in the graph uses. With `cfg.toDecl`/`cfg.fromDecl` set this is relative to the slice. -/
def Graph.unused (g : Graph) : Array Node := g.nodes.filter (·.uses == 0)

/-! ## Output -/

private def escape (s : String) : String := s.replace "\"" "\\\""

/-- Fill colours follow `dpd2dot`: lemmas green, axioms orange, inductives violet, definitions pink. -/
private def fillColor (n : Node) : String :=
  match n.kind with
  | .theorem   => "#b8f2b8"
  | .axiom     => "#ffb347"
  | .inductive => "#d8b6f0"
  | .opaque    => "#f0c0c0"
  | .definition => if n.isProp then "#d9f5b8" else "#f7c6d9"
  | .namespace => "#fde9b8"
  | .module    => "#cfe3f7"
  | .other     => "#e5e7eb"

private def shape (n : Node) : String :=
  match n.kind with
  | .theorem   => "ellipse"
  | .inductive => "hexagon"
  | .axiom     => "octagon"
  | .module    => "component"
  | .namespace => "tab"
  | _          => if n.isProp then "ellipse" else "box"

/-- Graphviz DOT. Unused nodes are drawn with a double border, like `dpd2dot`. Arrows point from a
declaration to what it uses. -/
def Graph.toDot (g : Graph) (title : String := "deps") : String := Id.run do
  let mut out := s!"digraph \"{escape title}\" \{\n"
  out := out ++ "  rankdir=BT;\n  node [fontname=\"Helvetica\", fontsize=10, style=filled];\n  edge [color=\"#777777\", arrowsize=0.6];\n"
  let modules := g.nodes.foldl (fun (acc : Array Name) n => if acc.contains n.module then acc else acc.push n.module) #[]
  let cluster := modules.size > 1 && g.nodes.all (·.kind != Kind.module)
  for m in modules do
    if cluster then
      out := out ++ s!"  subgraph \"cluster_{escape m.toString}\" \{ label=\"{escape m.toString}\"; style=rounded; color=\"#bbbbbb\";\n"
    for n in g.nodes do
      if n.module == m then
        let per := if n.uses == 0 then ", peripheries=2" else ""
        out := out ++ s!"  \"{escape n.name.toString}\" [shape={shape n}, fillcolor=\"{fillColor n}\"{per}, tooltip=\"{n.kind} @ {n.module}:{n.line}, used by {n.uses}\"];\n"
    if cluster then out := out ++ "  }\n"
  for e in g.edges do
    let pw := if e.weight > 1 then s!" [penwidth={min 4 (1 + e.weight / 4)}, tooltip=\"×{e.weight}\"]" else ""
    out := out ++ s!"  \"{escape e.src.toString}\" -> \"{escape e.dst.toString}\"{pw};\n"
  out := out ++ "}\n"
  return out

/-- A `.dpd`-like JSON dump: `{nodes: [...], edges: [...]}`. -/
def Graph.toJson (g : Graph) : Json :=
  Json.mkObj [
    ("nodes", Json.arr <| g.nodes.map fun n => Json.mkObj [
      ("name", n.name.toString), ("kind", toString n.kind), ("prop", n.isProp),
      ("module", n.module.toString), ("line", n.line), ("uses", n.uses)]),
    ("edges", Json.arr <| g.edges.map fun e => Json.mkObj [
      ("src", e.src.toString), ("dst", e.dst.toString), ("weight", e.weight)])]

/-- Human-readable summary line. -/
def Graph.summary (g : Graph) : String :=
  let thms := g.nodes.filter (·.isProp) |>.size
  let what := match g.nodes[0]? with
    | some n => if n.kind == Kind.module then "modules" else if n.kind == Kind.namespace then "namespaces" else s!"declarations ({thms} propositions)"
    | none => "nodes"
  s!"{g.nodes.size} {what}, {g.edges.size} edges, {g.unused.size} unused"

/-- Extract at the requested level and apply the filters in one go. -/
def build (cfg : Config) : MetaM Graph := do
  let g ← match cfg.level with
    | .decl      => extract cfg
    | .namespace => pure ((← extract cfg).collapse namespaceOf .namespace)
    | .module    => extractModules cfg
  return g.apply cfg

end DepGraph
