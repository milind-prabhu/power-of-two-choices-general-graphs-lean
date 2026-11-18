# Online Graph Balancing and the Power of Two Choices

The two main theorems—**Theorems 1.1 and 1.2**—are formalized in Lean.

[Paper](https://arxiv.org/abs/2604.04159v1) by Nikhil Bansal, Milind Prabhu,
Sahil Singla, and Siddharth M. Sundaram.

## Explore the proof

View the [interactive Lean dependency graph](https://milind-prabhu.github.io/power-of-two-choices-general-graphs-lean/).
Click the image below to open it, then select a module to see its Lean
statements, proofs, and imports. Use the view menu to focus on either main theorem.

[![Lean file dependency graph](dependency-graph/dependencies.svg)](https://milind-prabhu.github.io/power-of-two-choices-general-graphs-lean/)

The graph shows file-import dependencies across 101 modules and 578 named proved
results. See [graph documentation](DEPENDENCIES.md) for details and offline use.

## Build and verify

Install [elan](https://github.com/leanprover/elan), clone this repository, and run:

```bash
bash bootstrap.sh
bash check.sh
```

The project pins Lean 4.24.0 and mathlib 4.24.0. The check builds the proofs,
checks source/audit coverage, and rejects admitted proofs or nonstandard axioms.
[Build status](https://github.com/milind-prabhu/power-of-two-choices-general-graphs-lean/actions/workflows/lean.yml).

See the [formalization notes](FORMALIZATION.md) for precise theorem statements,
assumptions, and correspondence with the paper, and [proof status](STATUS.md)
for auxiliary results and complexity guarantees outside the formalization.
