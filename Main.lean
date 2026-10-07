/-
`lake exe dpg` — declaration dependency graphs, in the style of `coq-dpdgraph` + `dpd2dot` + `dpdusage`.

    lake exe dpg [options] Module [Module ...]

    --level L        decl (default) | namespace | module
    --only P,Q       module level: keep only modules under these prefixes
                     (default: the top-level namespaces of the given modules, i.e. the package)
    --include-deps   module level: no prefix restriction (everything that is imported)
    --exclude P,Q    module level: drop modules under these prefixes (default Init,Lean,Std,Lake)
    --to DECL        keep only what DECL transitively depends on   (Print DependGraph)
    --from DECL      keep only what transitively depends on DECL
    --props-only     keep only propositions                        (dpd2dot -without-defs)
    --keep-trans     keep transitively implied edges               (dpd2dot -keep-trans)
    --instances      show derived instances as nodes
    --unused         list unused declarations on stderr            (dpdusage)
    -o FILE          write DOT to FILE instead of stdout
    --json FILE      also write a JSON dump of nodes and edges

Build the modules first (`lake build Module`). Render with Graphviz: `dot -Tsvg out.dot -o out.svg`.
-/
import DepGraph.Core
open Lean DepGraph

def usage : String :=
"usage: lake exe dpg [--level decl|namespace|module] [--only P,Q | --include-deps] [--exclude P,Q] [--to DECL] [--from DECL] [--props-only] [--keep-trans] [--instances] [--unused] [-o FILE] [--json FILE] Module [Module ...]"

def splitNames (s : String) : Array Name := (s.splitOn ",").toArray.filter (· ≠ "") |>.map String.toName

partial def parseArgs : List String → Config → Option String → Option String → Bool →
    Except String (Config × Option String × Option String × Bool)
  | [], cfg, out, json, un => if cfg.modules.isEmpty then .error usage else .ok (cfg, out, json, un)
  | "--level" :: l :: rest, cfg, o, j, u =>
    match Level.ofString? l with
    | some lv => parseArgs rest { cfg with level := lv } o j u
    | none => .error s!"--level: expected decl, namespace or module, got {l}"
  | "--only" :: p :: rest, cfg, o, j, u => parseArgs rest { cfg with onlyPrefixes := some (splitNames p) } o j u
  | "--include-deps" :: rest, cfg, o, j, u => parseArgs rest { cfg with onlyPrefixes := some #[] } o j u
  | "--exclude" :: p :: rest, cfg, o, j, u => parseArgs rest { cfg with excludePrefixes := splitNames p } o j u
  | "--to" :: d :: rest, cfg, o, j, u => parseArgs rest { cfg with toDecl := some d.toName } o j u
  | "--from" :: d :: rest, cfg, o, j, u => parseArgs rest { cfg with fromDecl := some d.toName } o j u
  | "--props-only" :: rest, cfg, o, j, u => parseArgs rest { cfg with propsOnly := true } o j u
  | "--keep-trans" :: rest, cfg, o, j, u => parseArgs rest { cfg with keepTrans := true } o j u
  | "--instances" :: rest, cfg, o, j, u => parseArgs rest { cfg with instances := true } o j u
  | "--unused" :: rest, cfg, o, j, _ => parseArgs rest cfg o j true
  | "-o" :: f :: rest, cfg, _, j, u => parseArgs rest cfg (some f) j u
  | "--json" :: f :: rest, cfg, o, _, u => parseArgs rest cfg o (some f) u
  | "-h" :: _, _, _, _, _ => .error usage
  | "--help" :: _, _, _, _, _ => .error usage
  | m :: rest, cfg, o, j, u =>
    if m.startsWith "-" then .error s!"unknown option {m}\n{usage}"
    else parseArgs rest { cfg with modules := cfg.modules.push m.toName } o j u

def main (args : List String) : IO UInt32 := do
  match parseArgs args { modules := #[] } none none false with
  | .error e => IO.eprintln e; return 1
  | .ok (cfg, out, json, listUnused) =>
    initSearchPath (← findSysroot)
    let env ← importModules (cfg.modules.map fun m => { module := m }) {} 0
    let ctx : Core.Context := { fileName := "<depgraph>", fileMap := default }
    let (g, _) ← (build cfg |>.run' {}).toIO ctx { env }
    let title := String.intercalate "," (cfg.modules.map (·.toString)).toList
    let dot := g.toDot (title := title)
    match out with
    | some f => IO.FS.writeFile f dot
    | none   => IO.print dot
    if let some f := json then IO.FS.writeFile f (g.toJson.pretty)
    IO.eprintln g.summary
    if listUnused then
      for n in g.unused do
        IO.eprintln s!"unused: {n.name} ({n.kind}, {n.module}:{n.line})"
    return 0
