# Power of two choices proof blueprint

Open the [interactive proof graph](https://milind-prabhu.github.io/power-of-two-choices-general-graphs-lean/) or
`generated/Graph_Choices_Blueprint.html` locally. The viewer is self-contained.
Its default overview contains 12 key declarations and 10 dependency arrows.
The menu provides the full ancestor graphs for Theorems 1.1 and 1.2 and all
799 public source-named declarations. Hover or keyboard-focus a node for a
larger summary; click for its compiled statement, source proof, and dependencies.

The toolbar, neutral colors, optional details panel, and sparse overview follow
the online carpooling repository. Ellipses denote proved results; boxes denote
definitions. Double borders mark the two main theorems. The static preview uses
green for checked declarations. SVG, PNG, and PDF overview exports are included.

## Rebuild

With the pinned Lean/mathlib dependencies and Graphviz installed, run from the
repository root:

```sh
python3 blueprint/index_sources.py
lake env lean blueprint/Extract.lean
python3 blueprint/build_graph.py
python3 blueprint/check_graph.py
```

`index_sources.py` identifies public named declarations in the source.
`Extract.lean` reads `ConstantInfo.getUsedConstantsAsSet` from the compiled Lean
environment, including generated and private helpers. The main upper-bound
statement is unfolded from `MainTheorem` so its quantifiers are visible.

Every arrow runs from prerequisite to result. Paths through omitted compiled
helpers are collapsed to the nearest displayed declarations; transitive
reduction removes redundant arrows in acyclic views. Every displayed arrow has
a witnessed path in `generated/graph_data.json`. `check_graph.py` verifies these
paths, source locations, compiled statements, and the 578 audited theorem names.
This is a standalone renderer, not a Lean Blueprint deployment.

`overview.json` contains the curated overview labels and explanations.
`descriptions.json` supplies hover text for every node, using source docstrings
where available and brief topic labels for remaining supporting declarations.
These explanations are exposition; the compiled statements are authoritative.
Use `python3 blueprint/build_graph.py --overview-only` to refresh just the
sparse view while retaining the detailed layouts.

## Scope and verification

The full view contains public source-named project declarations, not all
compiler-generated constants or mathlib. The original 101-module file-import
viewer remains in [dependency-graph](../dependency-graph/index.html).

The Lean proofs are unchanged. All 578 named proved results passed the build
and axiom audit, allowing only `propext`, `Classical.choice`, and `Quot.sound`.
The graph does not claim that every auxiliary statement or running-time bound
in the paper has been formalized; see [STATUS.md](../STATUS.md).
