# Proof status

**Both main theorems (Theorems 1.1 and 1.2) are proved.**
`GraphChoices.mainTheorem` proves the exact `MainTheorem` specification from
`Targets.lean`. The stronger `exists_competitive_policy` result covers every
finite nonempty simple base graph and every natural horizon T, with

```text
E[cost(G,T)] ≤ 120000 L(|V|) E[OPT(G,T)],
L(n) = 1 + log(1 + log(max(2,n))).
```

The theorem constructs a deterministic policy of type `List E → E → Bool`.
The policy may know G and T. It receives only preceding labels and the current
label at each online step. Small graphs and T=0 are included. No asserted
preprocessing certificate, skewness lower bound, probability estimate, or
policy-performance conclusion is an assumption of this theorem.

## End-to-end dependency chain

1. Exact finite i.i.d. sampling; occurrence-preserving loads and optimum;
   density/orientation identity with integer ceiling.
2. Maximum source density and its rounded capacity comparison with the
   expected optimum.
3. Source relabeling and exact policy pullback; a once-per-base-edge instance
   identifies rounded base density with an attained orientation optimum.
4. Original-graph oriented vertex-copy construction, edge-label bijection,
   derived left-degree bound and factor-two online-policy collapse.
5. Concrete graph log-skewness, Hall expansion, terminating peeling and the
   exact doubly exponential decomposition into skew-biregular pieces.
6. Exact block sampling, pairwise occupancy covariance, second moment and a
   concrete dense induced subgraph; `sigma ≤ 8 E[OPT]` at the actual rate when
   `log N ≤ T`, with all threshold and block-length rounding proved.
7. Executable Threshold-Greedy, actual replay and policy load identities,
   canonical tree coverage, source/piece degree bounds and component shattering.
8. Explicit automatic threshold budget, its log-log growth and component-local
   Greedy bound, all for the same constructed policy.
9. Rate-adjusted reference capacity `ceil(maxBaseDensity)+ceil(d/16)` with
   proved density, sampling-mass and size bounds.
10. Complete horizon regimes: short-horizon Greedy on at most 2T active
    vertices; rate-adapted threshold policy for intermediate horizons; the
    left-endpoint policy for large maximum mean or high-load horizons; direct
    total-density comparison for small graphs.
11. Final label pullback, vertex collapse and log-log size comparison, proving
    `exists_competitive_policy` and the exact `mainTheorem` specification.

The horizon proof uses the actual sampling rate and does not require the
paper's random auxiliary clique augmentation. Its expected maximum-degree
bound uses an exact exponential moment and finite Jensen, avoiding a
horizon-dependent exceptional-sample term.

## Greedy lower bound — completed

`GraphChoices.LowerBound.greedyLowerBound` constructs an explicit infinite
family of simple graphs with arbitrarily large actual vertex count N. At
exactly N sampled arrivals, ordinary Greedy with independent fair tie coins
has the competitive-ratio lower bound

```text
E[Greedy] ≥ log(N)/(30000 (log(log(N)))²) E[OPT].
```

The supporting theorems also prove the paper's more specific conclusions:

- `family_greedy_logarithmic_high_probability`: load at least
  `log(N)/(26 log(log(N)))` except with probability at most `N⁻²`.
- `family_optimum_loglog`: expected optimum at most `500 log(log(N))`.
- `family_degree_range`: every actual vertex degree lies in
  `[sqrt(N), sqrt(N) log(N)³]`.
- `size_eq_vertices`: N is exactly the cardinality of the constructed vertex
  type. `size_eq_batches` proves exact divisibility into b batches.
- `graph_isSimple`: no loops and no repeated unordered base edges.
- `fair_tie_probability`: tie probability exactly 1/2 for every fixed state
  and arriving edge. `coin_expectedOpt`: coins preserve the edge-sampling
  offline benchmark.

Parameters are integral: `b ≥ 16`, `t=(16b)³`, `m=2 t^b`, layers `m t^i`
for `0 ≤ i ≤ b`, and complete bipartite blocks `K(m,tm)` between consecutive
layers. The source alphabet preserves every base edge and each occurrence.

The propagation proof counts marked arrivals (an upward edge with a coin
favoring the lower vertex). A deterministic forcing lemma and an exact
binomial lower tail prove the full batch success probability. The offline
bound counts every pair of nonempty left/right vertex subsets in every block,
cancels their count against a binomial density upper tail, and proves an
actual capacity bound by the orientation/density identity. Each vertex belongs
to at most one left block and one right block. No stochastic propagation,
expected optimum, or competitive-ratio conclusion is assumed.

## Remaining paper results

The entire paper is not claimed formalized. Remaining statements include:

- The literal edge-multiplicity concentration formulas in Claims 2.3 and 4.5.
  The main upper bound uses a different proved route and does not assume them.
- The literal paper alpha formula. The implementation uses explicit rounded
  automatic thresholds with the required proved asymptotic budget.
- The standalone skew-biregular Greedy guarantee of Lemma 3.5, and any cited
  external matching competitive-ratio lower bound.
- Almost-linear preprocessing running time and computational complexity.

## Validation and trust boundary

`Audit.lean` lists all 578 named proved results, including
`GraphChoices.exists_competitive_policy`, `GraphChoices.mainTheorem`, and
`GraphChoices.LowerBound.greedyLowerBound`.
`verify.py` verifies exact source/audit coverage, builds the full project and
checks theorem axiom dependencies. Only standard `propext`, `Classical.choice`
and `Quot.sound` are permitted. No admitted proofs, custom axioms or native
computation trust steps are used.
