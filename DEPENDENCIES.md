# PFR-style file dependency graph

Open the [hosted viewer](https://milind-prabhu.github.io/power-of-two-choices-general-graphs-lean/),
or open **dependency-graph/index.html** locally in a browser.
Everything needed by the viewer is local; it needs no web server or connection.

The layout and green status convention are inspired by the
[PFR Lean Blueprint graph](https://teorth.github.io/pfr/blueprint/dep_graph_document.html).
This artifact is a file-import graph, rather than a Lean Blueprint theorem graph.

## Read and explore

- Each rounded green node is one of the 101 project Lean source files.
- The dark green double-bordered nodes are MainProof and GreedyLowerBound.
- An arrow A → B means B imports A. External Mathlib imports are omitted.
- All 141 direct local imports are available in the full view.
- The 137-edge reduced view drops transitively redundant arrows and preserves
  the full graph's reachability. It is not a change to the Lean sources.
- Click a node to highlight its prerequisites and inspect its description,
  declarations, imports and importing files. Follow source links to exact lines.
- Search by file name; use a theorem-file focus or a selected neighborhood.
  Drag to pan, scroll to zoom, or use the +, − and Fit buttons.

Green records the packaged successful build and axiom audit for all 578 named
proved results. It does not assert that every auxiliary statement in the paper
has a corresponding formal declaration. Those remaining statements are listed
in STATUS.md. A file may import another file without using its main theorem;
file-import edges should not be interpreted as individual proof dependencies.

## Included artifacts

| Path | Content |
| --- | --- |
| dependency-graph/index.html | Offline interactive viewer |
| dependency-graph/dependencies.svg | Reduced vector graph |
| dependency-graph/dependencies-full.svg | All direct imports, vector graph |
| dependency-graph/dependencies.dot | Reproducible reduced Graphviz source |
| dependency-graph/dependencies-full.dot | Full Graphviz source |
| dependency-graph/dependencies.json | Import edges, declaration inventory, source hashes |
| dependency-graph/sources/ | Linked, line-numbered source pages for every module |
| tools/generate_dependency_graph.py | Generator (Python standard library + Graphviz) |
| tools/dependency_graph_template.html | Viewer template |

## Regenerate

From the project directory, with Lean/mathlib installed and Graphviz `dot` on
PATH:

```sh
bash check.sh
python3 tools/generate_dependency_graph.py
```

The graph generator reads the actual `import GraphChoices.…` lines and source
declarations, checks the module DAG, records SHA-256 hashes and checks that the
packaged verification count matches the source inventory. Rerun the proof
verification after editing Lean files before regenerating the graph.
