#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")"
lake exe cache get \
  Mathlib.Algebra.BigOperators.Fin \
  Mathlib.Algebra.Order.BigOperators.Ring.Finset \
  Mathlib.Analysis.Complex.Exponential \
  Mathlib.Analysis.Complex.ExponentialBounds \
  Mathlib.Analysis.Convex.Jensen \
  Mathlib.Analysis.Convex.SpecificFunctions.Basic \
  Mathlib.Analysis.SpecialFunctions.Log.Basic \
  Mathlib.Analysis.SpecialFunctions.Pow.Real \
  Mathlib.Combinatorics.Enumerative.Catalan \
  Mathlib.Combinatorics.Hall.Finite \
  Mathlib.Combinatorics.SimpleGraph.Acyclic \
  Mathlib.Combinatorics.SimpleGraph.Bipartite \
  Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected \
  Mathlib.Data.Fin.Tuple.Basic \
  Mathlib.Data.Finset.Card \
  Mathlib.Data.Finset.Lattice.Fold \
  Mathlib.Data.Finset.Powerset \
  Mathlib.Data.Finset.Sort \
  Mathlib.Data.Fintype.BigOperators \
  Mathlib.Data.Fintype.Pi \
  Mathlib.Data.Fintype.Prod \
  Mathlib.Data.Fintype.Sigma \
  Mathlib.Data.Fintype.Sum \
  Mathlib.Data.List.Forall2 \
  Mathlib.Data.List.Nodup \
  Mathlib.Data.List.OfFn \
  Mathlib.Data.List.Range \
  Mathlib.Data.Nat.Choose.Bounds \
  Mathlib.Data.Nat.Find \
  Mathlib.Data.Nat.Log \
  Mathlib.Data.Real.Archimedean \
  Mathlib.Data.Real.Basic \
  Mathlib.Tactic.FieldSimp \
  Mathlib.Tactic.Linarith \
  Mathlib.Tactic.NormNum \
  Mathlib.Tactic.Positivity \
  Mathlib.Tactic.Ring
