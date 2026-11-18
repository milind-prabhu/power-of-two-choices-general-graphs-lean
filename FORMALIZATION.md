# Online Graph Balancing and the Power of Two Choices — Lean

Both **main theorems are kernel-checked**: the online upper bound for every
nonempty simple graph and every horizon, and the Greedy lower bound with fair
random tie-breaking on an explicit infinite family. Some auxiliary statements
and computational-complexity guarantees remain outside the formalization.

Source paper: Nikhil Bansal, Milind Prabhu, Sahil Singla, Siddharth M. Sundaram,
[arXiv:2604.04159v1](https://arxiv.org/abs/2604.04159v1), April 5, 2026.
The theorem numbering below follows that version.

## Interactive dependency graph

Open the [hosted dependency graph](https://milind-prabhu.github.io/graph-choices-lean/)
or [dependency-graph/index.html](dependency-graph/index.html) locally. It works offline and includes search, pan/zoom, prerequisite
highlighting, theorem-file focus and linked source pages. The two main theorem
files have dark green nodes.

The graph has **101 file nodes and 141 direct project-import edges**. Its
default reduced view has 137 edges and preserves all import reachability.
These are file-import dependencies, not theorem-level proof-reference edges.
SVG, DOT and JSON exports and a regeneration script are included. See
[DEPENDENCIES.md](DEPENDENCIES.md).

## Build and audit

Requires Lean **4.24.0** and mathlib **v4.24.0**, pinned in the included toolchain
and Lake manifest. From this directory:

```sh
lake exe cache get
python3 verify.py
```

`verify.py` runs `lake build`, asks Lean for the axiom dependencies of every named
proved result in `Audit.lean`, and rejects `sorryAx` or nonstandard axioms.
Only Lean's standard `propext`, `Classical.choice`, and `Quot.sound` occur.
There are no admitted proofs, custom axioms, native-decider proofs, or external
solver trust steps. The main specification is a definition of a proposition, and
`GraphChoices.mainTheorem` proves it. No proof assumes the specification.

The supplied validation records cover **578 named proved results** in 101 modules.

## Main theorem

`GraphChoices.mainTheorem` in `GraphChoices/MainProof.lean` proves the exact
`MainTheorem` specification. Its stronger general-purpose theorem
`exists_competitive_policy` establishes that, for every finite nonempty simple
base graph G on n vertices and every natural arrival horizon T, there exists a
deterministic online policy satisfying

```text
E[cost(G,T)] ≤ 120000 L(n) E[OPT(G,T)],
L(n) = 1 + log(1 + log(max(2,n))).
```

The policy receives only previous edge labels and the current label. No
preprocessing, skewness, probability, benchmark, or performance conclusion is
assumed. The construction includes the original vertex-copy transformation,
all arrival regimes, small graphs and zero arrivals. The numerical constant
is explicit and is not optimized. This is an existence and performance proof;
an almost-linear preprocessing running time is not formalized.

## Greedy lower bound

`GraphChoices.LowerBound.greedyLowerBound` in
`GraphChoices/GreedyLowerBound.lean` proves an explicit infinite family of
simple base graphs with arbitrarily many vertices N for which

```text
E[Greedy] ≥ (1/30000) log(N)/(log(log(N)))² E[OPT].
```

The Greedy process uses independent uniformly sampled edge labels and fair
Bool coins, with the coin used only when the endpoint loads tie. This is
proved directly in the finite product sample space. `fair_tie_probability`
proves the tie probability is exactly 1/2, and `coin_expectedOpt` proves that
adding the coins preserves the offline benchmark.

The same concrete graph family satisfies the quantitative forms of the
paper's Lemmas 5.1 and 5.2:

```text
P[Greedy maximum load < log(N)/(26 log(log(N)))] ≤ 1/N²,
E[OPT] ≤ 500 log(log(N)),
sqrt(N) ≤ degree(v) ≤ sqrt(N) log(N)³ for every vertex v.
```

All samples have exactly N arrivals, where N is the actual vertex count.
Integer parameters are `b ≥ 16`, `t=(16b)³`, and `m=2 t^b`, with layers of
sizes `m t^i`, for `0 ≤ i ≤ b`. Consecutive layers use disjoint complete
bipartite blocks `K(m,tm)`. The width is divisible by b, so the batches have
exact integer length N/b. The construction is proved simple, and N ≥ b
supplies arbitrary growth. The random-tie propagation and offline density
estimates are derived; neither is assumed as a hypothesis of the lower-bound
theorem.

## What is proved

| Paper location | Checked result | Module |
|---|---|---|
| Definition 2.1 | Indexed edge-arrival sequences, legal orientations, loads, optimum attainment, exact mass conservation | `Model` |
| Section 2.2 | Every induced-subgraph density lower bound; every edge-multiplicity lower bound `multiplicity ≤ 2 OPT` | `Model` |
| Section 2.2, classical density identity | An orientation of capacity `c` exists iff every induced subset has at most `c |S|` arrivals; consequently `OPT = ceil(maxDensity)` | `Density` |
| Lemma 2.4, performance comparison | Split and collapse orientations; samplewise optimum inequalities; factor-two transfer of expected competitiveness, including explicit online policies | `Bipartite`, `Preprocessing`, `Targets` |
| Preprocessing, bounded left degree | Existence of a reference orientation whose copied graph has maximum left degree at most `ceil(maxDensity)` | `Preprocessing` |
| Claims 2.3 and 4.5, density part | For every fixed subset and every horizon: `T |E(S)| / |E| ≤ |S| E[OPT]`, with the i.i.d. distribution explicitly constructed | `Uniform` |
| Fact 3.6 | For any Greedy orientation and positive horizon, `maxLoad < 2 OPT (floor(log₂ |V|) + 1)`; includes both legal tie choices | `Greedy` |
| Lemma 3.7, structural existence | Maximum log-skewness over concrete subgraphs; hereditary Hall expansion; terminating peeling; exact partition at doubly exponential scales with explicit log-log piece count and real degree bounds, under preprocessing hypotheses | `Peeling`, `GraphSkew`, `Decomposition`, `SkewDecomposition` |
| Algorithm 1 | Executable Threshold-Greedy, bounded class counters, total threshold budget, residual-edge saturation and necessary prior-incidence condition, legal residual Greedy updates | `ThresholdGreedy` |
| Section 4.2, threshold sum | Rounded thresholds satisfy `sum ceil(K (L/2^i + 1)) ≤ K (2 L + h) + h` | `ThresholdBudget` |
| Execution and benchmark bridge | Residual replay satisfies indexed `IsGreedy`; execution loads equal occurrence counts; residual optimum is at most the full optimum | `ResidualReplay`, `GreedyExecution`, `ReplayGreedyAdapter`, `ResidualOptimum` |
| Component-local Greedy bound | Edge-closed layer counting, actual connected components, full-instance benchmark, and the exact multiplier `4 (log₂ ell + 1)` for components of at most `ell²` vertices | `ComponentGreedy`, `ResidualComponents` |
| Claim 4.3, deterministic reduction | Component spanning trees; deletion of right leaves preserves a tree; the retained tree is left-heavy and has at least a `1/(D+1)` fraction of the vertices under left-degree bound `D` | `ComponentTrees`, `TreePruning` |
| Claim 4.3, sampling bridge | Residual distinct left neighborhoods are bounded by full-sample bucket hits; exact exponential degree union tail | `ResidualDegree` |
| Actual component pruning | Replay graph degrees equal the implementation's distinct neighborhoods; every nontrivial replay component contains the proved large left-heavy tree, with a right root when its size exceeds one | `ListArrivalGraph`, `ComponentPruning` |
| Necessary threshold witnesses | Each residual arrival forces distinct earlier threshold occurrences, disjoint from all residual occurrence times | `ThresholdWitnesses` |
| Sampling upper tails | Exact combinatorial and exponential binomial tail bounds, plus finite-family degree union bounds | `SamplingTail` |
| Section 4.2.2, actual fixed-tree probability | Actual residual occurrences force a collision-free joint witness; the raw exponential bound (12) follows | `ExecutionIndex`, `WitnessEncoding`, `ResidualTreeBound` |
| Fixed-pattern embedding count | Prefix-dependent assignment count; concrete base-edge embeddings inject into vertex assignments; the count underlying (8) | `AssignmentCount`, `PatternEmbeddingCount`, `PatternEventBound` |
| Fixed-pattern geometric decay | Branching/threshold cancellation, including explicit sufficient logarithmic threshold conditions | `BalancedProduct`, `PatternDecay`, `ThresholdDecay` |
| Canonical tree-shape union | Plane rooted patterns from binary forests; Catalan shape bound; labelled-shape union and inverse-polynomial failure bounds | `ShapePatterns`, `ShatteringBounds` |
| Union over tree sizes | Canonical trees with edge counts from `k` through `k+B` have combined tail at most `2 |R| / 2^k` when each fixed-size tail is at most `|R| / 2^m` | `LargeShapeTail` |
| Concrete sufficient thresholds | An explicit rounded integer formula satisfies both local threshold inequalities and gives geometric canonical-pattern decay; the implemented automatic vector has the budget proved in later modules | `ExplicitThresholds` |
| Geometric pattern coverage | Actual residual adjacency supplies original times and labels; injective vertex embeddings force distinct edge labels; any canonical geometric embedding forces its counted shape event, with classes constructed from execution | `ResidualAdjacency`, `PatternCoverage`, `ShapeCoverage` |
| Concrete decay parameters and quantitative budget | `r=1/(8h)` and `b=r²/(Dz+1)` discharge all local decay conditions; the explicit threshold sum has a finite bound derived from the decomposition's real degree bounds | `AutomaticThresholds`, `ExplicitThresholdBudget` |
| Shattering assembly | Actual large components force a degree exception or a geometric heavy tree; the earlier conditional assembly is now supplied with a proof of canonical coverage | `ComponentTreeEvents`, `PolynomialShattering`, `CanonicalCoverage` |
| Canonical coverage — proved | Every finite connected graph has a nonrepeating spanning labelled forest; its preorder gives a canonical shape and a vertex bijection with exact parent, side and left-count identities | `LabelledForest`, `ForestIndices`, `CanonicalForest` |
| Concrete component shattering | Actual component failure at most `3/N^c` and expected-load error `3T/N^c` for automatic thresholds, without a coverage or per-pattern probability premise | `CanonicalCoverage`, `ConcreteShattering` |
| Lemma 4.2, finite preprocessed version | For `T ≤ N`, `M ≤ d log N`, `2|E|=Nd`, and `c ≥ 5`, component size exceeds `3 ((c+1)(floor(log₂ N)+1)+1)²` with probability at most `3/N^c`, under the stated source/piece degree bounds | `PreprocessedShattering` |
| Operational graph decomposition | Exact partition gives actual edge classes, a simple source encoding and proved bucket bounds; maximum piece degrees satisfy the decomposition's real scale bounds | `PieceEncoding`, `PreparedDecomposition` |
| Actual online-policy interface | The policy uses only past labels and the current edge; its indexed loads equal the full implementation state, and its benchmark equals the original sampled optimum | `ThresholdPolicy` |
| Budget for the policy's exact thresholds | Finite class indexing and automatic rate/branch parameters match the implementation; at `T=N`, the needed mass condition follows from average-degree consistency and the reference cap | `AutomaticBudget`, `PreparedDecomposition` |
| Finite preprocessed expected-cost theorem | Constructs the partition and an actual online policy from graph-level preprocessing assumptions; expected cost at `T=N` is bounded by the explicit threshold budget, a component logarithm times `E[OPT]`, and `3N/N^c` | `DecomposedAlgorithm` |
| Expected maximum-density comparison | Maximized source density gives an expected-optimum lower bound; the rounded reference capacity satisfies `B T/|E| ≤ 3 E[OPT]`, including the ceiling cost | `ExpectedDensity` |
| Log-log budget and component multiplier | The exact budget is at most `320 (B N/|E| + sigma + 1) Q(N)`, and the residual Greedy multiplier is at most `20 Q(N)`, where `Q(N)=floor(log₂(floor(log₂ N)+1))+1` | `BudgetSimplification`, `IteratedLogBounds` |
| Preprocessed real log-log comparison | Constructs an actual online policy with `E[cost] ≤ 4200 L(N) (E[OPT] + sigma)` under the stated graph-level preprocessing assumptions; `L` is the main target's real log-log factor | `PreprocessedComparison`, `RealLoglogComparison` |
| Expectation reduction | Full implemented maximum load is bounded by threshold budget plus component-local Greedy; exceptional samples contribute at most `T` times the actual large-component probability | `ComponentExpectation` |
| Lemma 3.3, preprocessed large-size regime | `Skew(G) ≤ 8 E[OPT]` for `log N ≥ 2`, derived from exact independent-block probabilities, pairwise occupancy covariance and sampled induced-subgraph density | `BlockSampling`, `OccupancySecondMoment`, `BlockDensity`, `SubgraphOccupancy`, `SkewBlockArithmetic`, `SkewLowerBound` |
| Preprocessed competitive theorem at `T=N` | Constructs an actual online policy with `E[cost] ≤ 37800 L(N) E[OPT]`, including small sizes, without a skewness, coverage, or performance premise | `SampleRestriction`, `PreprocessedCompetitive` |
| Theorem 1.1, complete | Exact `MainTheorem` specification and a stronger finite-type result: an actual deterministic online policy for every nonempty simple graph and every horizon, with `E[cost] ≤ 120000 L(n) E[OPT]` | `MainProof` |
| Original-graph preprocessing | Once-per-base-edge optimum equals rounded maximum source density; an actual oriented bipartite edge set, label bijection, reference-cap transfer and derived left-degree certificate | `SourceRelabel`, `OriginalGraphPreprocessing` |
| All arrival horizons | Rate-adapted skewness, decomposition and thresholds; short-horizon Greedy on at most `2T` active vertices; high-load and small-size bounds; complete bipartite guarantee | `SkewHorizonLower`, `HorizonDecomposition`, `RateCompetitive`, `ShortHorizonGreedy`, `BipartiteAllHorizons` |
| Expected maximum degree | Exact exponential moment and finite Jensen give `E[max bucket hits] ≤ 2 (log bucketCount + maxMean)` for arbitrary horizons, and hence the left-endpoint policy bound | `ExpectedMaxHits`, `LeftEndpointPolicy` |
| Theorem 1.2, complete | Explicit infinite family with fair random tie-breaking, competitive gap at least `log N/(30000 (log log N)²)` and every degree in `[sqrt N, sqrt N log³ N]` | `GreedyLowerBound`, `LowerGraphDegrees` |
| Lemma 5.1 | A deterministic marked-arrival propagation theorem; proved binomial lower tail and batch union bound; actual load at least `log N/(26 log log N)` except with probability `N⁻²` | `RandomGreedy`, `GreedyCoinMarginals`, `BinomialLowerTail`, `GreedyBatchPropagation`, `GreedyPropagationProbability` |
| Lemma 5.2 | Complete-block subset counts and binomial density tails; per-block density gives the full sample capacity; expected offline optimum at most `500 log log N` | `CompleteBlockDensity`, `BlockDensityTailArithmetic`, `CompleteBlockTail`, `LowerOfflineOptimum` |
| Explicit lower-bound construction | Finite layer and block types, simple edge labels, vertex and edge counts, exact integral batches and logarithmic parameter comparisons | `LayeredLowerGraph`, `LowerFamilyParameters`, `LowerFamilyLogBounds` |
| Regression examples | Three parallel arrivals have optimum two; threshold one followed by three Greedy arrivals produces the specified loads | `Examples` |

For example, the Greedy bound is proved from a stronger layer inequality:

```text
d · |{v : load(v) ≥ k+d}| ≤ OPT · |{v : load(v) ≥ k}|.
```

The proof counts late arrivals into high-load vertices, uses the Greedy rule to
force both endpoints into the lower layer, and applies the offline density bound.
Setting `d = 2 OPT` gives geometric decay of the layer sizes.

## Model decisions

- Every occurrence has its own time index. Repeated arrivals are never collapsed.
- A base edge label is sampled independently and uniformly at each time, with
  replacement. The sample space is the full finite function space `Fin T → E`.
- Expectations are exact finite real averages. This is mathematically the same
  finite i.i.d. law, without introducing a separate measure-theoretic interface.
- The deterministic lemmas work for labelled multigraphs and loops too. The main theorem restricts base graphs to loopless simple graphs, as in the paper.
- Greedy is specified relationally to include both legal tie choices. The
  Threshold-Greedy implementation uses the paper's deterministic right tie rule.
- Threshold counts and residual Greedy loads are separate. A threshold counter
  freezes at its threshold; residual loads are shared across all classes.
- The density identity keeps the ceiling. Dropping it, as the paper later does
  for asymptotic estimates, is not silently treated as an exact equality.
- `OnlinePolicy E` has type `List E → E → Bool`: only the preceding arrivals and
  current edge are inputs. The main target allows a known horizon.

## Remaining scope

Theorems 1.1 and 1.2 and the quantitative forms of Lemmas 5.1 and 5.2 are
complete. Some auxiliary statements, including the paper's specific
edge-multiplicity concentration formula, literal threshold expression and
standalone skew-biregular Greedy lemma, are not claimed formalized. The main
proofs use proved alternatives where appropriate. Almost-linear preprocessing
running time is not formalized.

The horizon argument also differs from the paper's presentation. For
`log N ≤ T ≤ N`, sampling is analyzed at the actual rate `d=2|E|/T`, and the
reference capacity is enlarged by `ceil(d/16)`. Its expected cost is bounded
by the proved density comparison. Thus no random auxiliary clique
augmentation is needed. Intermediate larger horizons use `N=max(n,T)`;
very large horizons use the left-endpoint policy. For short horizons, Greedy
is compared on the sampled graph's at most `2T` active vertices. The exact
finite expectation and history-only online-policy interfaces are retained
through all reductions.

See [STATUS.md](STATUS.md) for the precise remaining scope.

See [CHANGELOG.md](CHANGELOG.md) for the new proofs in this continuation.

The end-to-end specification is `GraphChoices.MainTheorem` in
`GraphChoices/Targets.lean`; its proof is `GraphChoices.mainTheorem` in
`GraphChoices/MainProof.lean`.
