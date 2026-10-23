/-
# `#depgraph` — the Lean counterpart of Rocq's `Print DependGraph` / `Print FileDependGraph`.

```
#depgraph Parser.Parser2                       -- graph of a whole module, DOT written to depgraph.dot
#depgraph Parser.Parser2 to mkFirstMap         -- only what mkFirstMap depends on
#depgraph Parser.Parser2 from pairsOf          -- only what depends on pairsOf
#depgraph Parser.Parser2 props                 -- propositions only (dpd2dot -without-defs)
#depgraph Parser.Parser2 keep_trans            -- keep transitively implied edges
#depgraph Parser.Parser2 into "first.dot"      -- choose the output file
#depgraph Parser.Parser2 unused                -- also list unused declarations
#depgraph A.B, C.D to foo                      -- several modules, comma separated
#depgraph Parser.Parser2 metrics "metrics.csv" -- also write per-declaration complexity metrics
#depgraph Parser.Parser2 level namespace       -- collapse declarations onto namespaces
#depgraph Parser.Parser2 level module          -- the import graph within the `Parser` package
#depgraph Parser.Parser2 level module include_deps exclude Init, Lean, Std, Lake, Mathlib
#depgraph Parser.Parser2 level module only Parser, Mathlib.Data exclude Mathlib.Data.List
```
At `level module` the graph is restricted to the top-level namespaces of the given modules
(roughly: the current package) unless `only` or `include_deps` says otherwise; `Init`, `Lean`,
`Std` and `Lake` are excluded unless `exclude` is given explicitly.
The file is written relative to the working directory of the Lean process (the project root
when run under `lake`).
-/
import DepGraph.Core
import DepGraph.Metrics
open Lean Elab Command Meta

namespace DepGraph

syntax depTo    := &"to" ident
syntax depFrom  := " from " ident
syntax depInto  := &"into" str
syntax depProps := &"props"
syntax depKeep  := &"keep_trans"
syntax depInst  := &"instances"
syntax depUnused := &"unused"
syntax depLevel := &"level" (&"decl" <|> "namespace" <|> "module")
syntax depOnly   := "only" ident,*
syntax depAllDeps := &"include_deps"
syntax depExclude := &"exclude" ident,+
syntax depMetrics := &"metrics" str
syntax depOpt := depTo <|> depFrom <|> depInto <|> depProps <|> depKeep <|> depInst <|> depUnused
  <|> depLevel <|> depOnly <|> depAllDeps <|> depExclude <|> depMetrics

syntax (name := depgraphCmd) "#depgraph " ident,+ depOpt* : command

@[command_elab depgraphCmd] def elabDepgraph : CommandElab := fun stx => do
  let mods := stx[1].getSepArgs.map fun s => s.getId
  let mut cfg : Config := { modules := mods }
  let mut file := "depgraph.dot"
  let mut listUnused := false
  let mut metricsFile : Option String := none
  for o in stx[2].getArgs do
    match o[0] with
    | `(depTo| to $d:ident)     => cfg := { cfg with toDecl := some (← liftCoreM <| realizeGlobalConstNoOverloadWithInfo d) }
    | `(depFrom| from $d:ident) => cfg := { cfg with fromDecl := some (← liftCoreM <| realizeGlobalConstNoOverloadWithInfo d) }
    | `(depInto| into $f:str)   => file := f.getString
    | `(depProps| props)        => cfg := { cfg with propsOnly := true }
    | `(depKeep| keep_trans)    => cfg := { cfg with keepTrans := true }
    | `(depInst| instances)     => cfg := { cfg with instances := true }
    | `(depUnused| unused)      => listUnused := true
    | `(depLevel| level decl)        => cfg := { cfg with level := .decl }
    | `(depLevel| level namespace)   => cfg := { cfg with level := .namespace }
    | `(depLevel| level module)      => cfg := { cfg with level := .module }
    | `(depOnly| only $ms:ident,*)    => cfg := { cfg with onlyPrefixes := some (ms.getElems.map (·.getId)) }
    | `(depAllDeps| include_deps)     => cfg := { cfg with onlyPrefixes := some #[] }
    | `(depExclude| exclude $ms:ident,*) => cfg := { cfg with excludePrefixes := ms.getElems.map (·.getId) }
    | `(depMetrics| metrics $f:str)   => metricsFile := some f.getString
    | _ => throwErrorAt o "unknown #depgraph option"
  let g ← liftTermElabM <| build cfg
  IO.FS.writeFile file (g.toDot (title := String.intercalate "," (mods.map (·.toString)).toList))
  let mut msg := m!"{g.summary}\nwrote {file}"
  if listUnused then
    for n in g.unused do
      msg := msg ++ m!"\n  unused: {n.name} ({n.kind}, line {n.line})"
  if let some f := metricsFile then
    let ms ← liftTermElabM <| metrics cfg
    IO.FS.writeFile f (metricsCsv ms)
    msg := msg ++ m!"\nwrote metrics for {ms.size} declarations to {f}"
    for m in topBy ms (·.termSize) 5 do
      msg := msg ++ m!"\n  {m.name}: lines {m.lines}, term size {m.termSize}, cyclomatic {m.cyclomatic}"
  logInfo msg

end DepGraph
