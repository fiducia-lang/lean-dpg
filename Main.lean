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
    --metrics FILE   write per-declaration complexity metrics as CSV (decl level only):
                     lines, term_size, term_depth, cyclomatic, fan_out, fan_in, term_per_line
    --top N          with --metrics: print the N largest declarations on stderr (default 5)

Build the modules first (`lake build Module`). Render with Graphviz: `dot -Tsvg out.dot -o out.svg`.
-/
import DepGraph.Core
import DepGraph.Metrics
open Lean DepGraph

def usage : String :=
"usage: lake exe dpg [--level decl|namespace|module] [--only P,Q | --include-deps] [--exclude P,Q] [--to DECL] [--from DECL] [--props-only] [--keep-trans] [--instances] [--unused] [-o FILE] [--json FILE] [--metrics FILE [--top N]] Module [Module ...]"

def splitNames (s : String) : Array Name := (s.splitOn ",").toArray.filter (· ≠ "") |>.map String.toName

structure Opts where
  cfg        : Config := { modules := #[] }
  out        : Option String := none
  json       : Option String := none
  metrics    : Option String := none
  top        : Nat := 5
  listUnused : Bool := false

partial def parseArgs : List String → Opts → Except String Opts
  | [], o => if o.cfg.modules.isEmpty then .error usage else .ok o
  | "--level" :: l :: rest, o =>
    match Level.ofString? l with
    | some lv => parseArgs rest { o with cfg.level := lv }
    | none => .error s!"--level: expected decl, namespace or module, got {l}"
  | "--only" :: p :: rest, o => parseArgs rest { o with cfg.onlyPrefixes := some (splitNames p) }
  | "--include-deps" :: rest, o => parseArgs rest { o with cfg.onlyPrefixes := some #[] }
  | "--exclude" :: p :: rest, o => parseArgs rest { o with cfg.excludePrefixes := splitNames p }
  | "--to" :: d :: rest, o => parseArgs rest { o with cfg.toDecl := some d.toName }
  | "--from" :: d :: rest, o => parseArgs rest { o with cfg.fromDecl := some d.toName }
  | "--props-only" :: rest, o => parseArgs rest { o with cfg.propsOnly := true }
  | "--keep-trans" :: rest, o => parseArgs rest { o with cfg.keepTrans := true }
  | "--instances" :: rest, o => parseArgs rest { o with cfg.instances := true }
  | "--unused" :: rest, o => parseArgs rest { o with listUnused := true }
  | "-o" :: f :: rest, o => parseArgs rest { o with out := some f }
  | "--json" :: f :: rest, o => parseArgs rest { o with json := some f }
  | "--metrics" :: f :: rest, o => parseArgs rest { o with metrics := some f }
  | "--top" :: n :: rest, o =>
    match n.toNat? with
    | some k => parseArgs rest { o with top := k }
    | none => .error s!"--top: expected a number, got {n}"
  | "-h" :: _, _ => .error usage
  | "--help" :: _, _ => .error usage
  | m :: rest, o =>
    if m.startsWith "-" then .error s!"unknown option {m}\n{usage}"
    else parseArgs rest { o with cfg.modules := o.cfg.modules.push m.toName }

def main (args : List String) : IO UInt32 := do
  match parseArgs args {} with
  | .error e => IO.eprintln e; return 1
  | .ok o =>
    let cfg := o.cfg
    if o.metrics.isSome && cfg.level != .decl then
      IO.eprintln "--metrics is only available at decl level"; return 1
    initSearchPath (← findSysroot)
    let env ← importModules (cfg.modules.map fun m => { module := m }) {} 0
    let ctx : Core.Context := { fileName := "<depgraph>", fileMap := default, maxHeartbeats := 0 }
    let run {α} (x : MetaM α) : IO α := do
      let (a, _) ← (x.run' {}).toIO ctx { env }
      return a
    let g ← run (build cfg)
    let title := String.intercalate "," (cfg.modules.map (·.toString)).toList
    let dot := g.toDot (title := title)
    match o.out with
    | some f => IO.FS.writeFile f dot
    | none   => if o.metrics.isNone then IO.print dot
    if let some f := o.json then IO.FS.writeFile f (g.toJson.pretty)
    IO.eprintln g.summary
    if o.listUnused then
      for n in g.unused do
        IO.eprintln s!"unused: {n.name} ({n.kind}, {n.module}:{n.line})"
    if let some f := o.metrics then
      let ms ← run (metrics cfg)
      IO.FS.writeFile f (metricsCsv ms)
      IO.eprintln s!"wrote metrics for {ms.size} declarations to {f}"
      if o.top > 0 then
        IO.eprintln s!"largest by term_size:"
        for m in topBy ms (·.termSize) o.top do
          IO.eprintln s!"  {m.name}  lines={m.lines} term_size={m.termSize} cyclomatic={m.cyclomatic} fan_out={m.fanOut}"
    return 0
