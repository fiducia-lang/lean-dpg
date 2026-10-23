# lean-dpg — dependency graphs for Lean 4

A Lean 4 counterpart of Rocq's [`coq-dpdgraph`](https://github.com/proofengineering/coq-dpdgraph)
(`Print DependGraph`, `Print FileDependGraph`, `dpd2dot`, `dpdusage`), with one entry point for
three levels of granularity:

| level       | nodes                                   | edges                              |
|-------------|-----------------------------------------|------------------------------------|
| `decl`      | declarations you wrote                  | "the type or body references …"    |
| `namespace` | namespaces (the `decl` graph collapsed) | summed declaration edges           |
| `module`    | modules                                 | direct imports                     |

Everything is read off the **compiled environment**, never the source text. At `decl` level the
tool collects the constants referenced by each declaration's type and its proof or definition
term, so dependencies introduced by tactics (`simp [foo]`, `aesop`, `omega`, …) are included.
Compiler-generated auxiliaries (`foo.match_1`, `foo.proof_1`, `foo._unary`, `Foo.rec`,
`Foo.casesOn`, structure projections, derived instances, …) are folded into the declaration they
belong to, so the graph shows only what you wrote.

Depends on Lean core only; no Mathlib.

## Installation

Add to your `lakefile.toml`:

```toml
[[require]]
name = "dpg"
git = "https://github.com/fiducia-lang/lean-dpg"
rev = "main"
```

then `lake update dpg`. Both the executable and the `#depgraph` command become available.

## Command line

The module must be compiled first (`lake build My.Module`).

```sh
lake exe dpg My.Module -o deps.dot                       # whole module          (Print FileDependGraph)
lake exe dpg --to my_theorem My.Module -o t.dot          # what my_theorem rests on  (Print DependGraph)
lake exe dpg --from my_def My.Module -o d.dot            # what depends on my_def
lake exe dpg --props-only My.Module -o lemmas.dot        # propositions only     (dpd2dot -without-defs)
lake exe dpg --unused My.Module -o deps.dot              # list unused declarations (dpdusage)
lake exe dpg --level namespace My.Module -o ns.dot       # collapse onto namespaces
lake exe dpg --level module My.Module -o imports.dot     # import graph of the package
lake exe dpg --level module --include-deps --exclude Init,Lean,Std,Lake,Mathlib My.Module
lake exe dpg --json deps.json My.Module -o deps.dot      # also dump nodes/edges as JSON
dot -Tsvg deps.dot -o deps.svg                           # render with Graphviz
```

| option                | meaning                                                                 |
|-----------------------|-------------------------------------------------------------------------|
| `--level L`           | `decl` (default), `namespace` or `module`                               |
| `--to DECL`           | keep only what `DECL` transitively depends on                           |
| `--from DECL`         | keep only what transitively depends on `DECL`                           |
| `--props-only`        | keep only propositions (theorems and `Prop`-valued definitions)         |
| `--keep-trans`        | keep transitively implied edges (removed by default, like `dpd2dot`)    |
| `--instances`         | show derived instances as nodes                                         |
| `--unused`            | list declarations nothing in the graph uses, on stderr                  |
| `--only P,Q`          | module level: keep only modules under these prefixes (default: the top-level namespaces of the given modules, i.e. the package) |
| `--include-deps`      | module level: no prefix restriction                                     |
| `--exclude P,Q`       | module level: drop these prefixes (default `Init,Lean,Std,Lake`)        |
| `-o FILE`             | write DOT to `FILE` instead of stdout                                   |
| `--json FILE`         | also write a JSON dump of nodes and edges                               |
| `--metrics FILE`      | write per-declaration complexity metrics as CSV (see below)             |
| `--top N`             | with `--metrics`: print the N largest declarations (default 5)          |

Several modules may be given.

## Inside a Lean file

```lean
import My.Module
import DepGraph

#depgraph My.Module
#depgraph My.Module to my_theorem props unused into "t.dot"
#depgraph My.Module from my_def keep_trans instances
#depgraph My.Module level namespace
#depgraph My.Module level module include_deps exclude Init, Lean, Std, Lake, Mathlib
#depgraph A.B, C.D to foo
#depgraph My.Module to my_theorem props metrics "metrics.csv"
```

The command writes the DOT file (default `depgraph.dot`, relative to the working directory of the
Lean process) and reports a summary in the infoview.

## Reading the picture

Arrows point from a declaration to what it uses. Colours follow `dpd2dot`: green ellipses are
theorems, pink boxes definitions, violet hexagons inductive types, orange octagons axioms; modules
are blue components and namespaces yellow tabs. A double border marks a node nothing else in the
graph uses. Thick edges mean the dependency occurs many times. Nodes are ordered by source line and
clustered by module when more than one module is shown at `decl` level.

## Complexity metrics

`--metrics FILE` (or `metrics "FILE"` in `#depgraph`) writes one CSV row per declaration in the
graph, after the `--to`/`--from`/`--props-only` filters. Available at `decl` level only.

| column          | meaning                                                                    |
|-----------------|----------------------------------------------------------------------------|
| `lines`         | source lines of the declaration (statement and proof script)               |
| `term_size`     | distinct subterms of the elaborated proof or definition term, sharing respected, including compiler-generated auxiliaries the declaration owns |
| `term_depth`    | approximate depth of that term                                             |
| `cyclomatic`    | 1 + eliminator applications in the term (`casesOn`, `rec`, `recOn`, `brecOn`, `*.elim`, `match_N`, `ite`, `dite`, `Decidable.byCases`): McCabe's cyclomatic complexity, read as the number of case-analysis decision points in the proof |
| `fan_out`, `fan_in` | declarations in the graph this one uses, and that use it (before transitive reduction) |
| `term_per_line` | `term_size / lines`: how much of the proof is produced by automation rather than written |

Script length measures what was written; term size and cyclomatic complexity measure what the
kernel checks, including everything `simp`, `aesop` and `omega` generated. On a 98-theorem
development the term measures agree closely with each other (Spearman ρ ≈ 0.95) and with line
count (ρ ≈ 0.9); fan-out measures something different (ρ ≈ 0.7). The useful outliers are proofs
with high `term_per_line`: short scripts with large terms depend on automation behaving the same way
in future library versions. Term columns are 0 for inductive types and axioms.

## Library API

```lean
open DepGraph
let g ← build { modules := #[`My.Module], level := .decl, toDecl := some `my_theorem }   -- MetaM Graph
g.toDot, g.toJson, g.unused, g.summary
let ms ← metrics { modules := #[`My.Module] }      -- MetaM (Array Metrics)
metricsCsv ms
```

`Graph` is a plain `{ nodes, edges }` record; `Graph.restrict`, `ancestorsOf`, `dependentsOf`,
`collapse`, `transitiveReduction` and `countUses` are available for your own analyses.

## Related tools

* [`importGraph`](https://github.com/leanprover-community/import-graph) (`lake exe graph`): module
  level only. lean-dpg's `--level module` covers the same ground without the dependency.
* [NodeGraph](https://github.com/adamtopaz/NodeGraph): interactive declaration graphs in the
  infoview, for declarations you tag by hand.
* `#print axioms`, Batteries' `#print dependents`: which axioms a declaration transitively uses.
