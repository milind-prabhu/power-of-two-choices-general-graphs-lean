# Continuation 1

The checked result count increased from 84 to 163. There are now 22 source
modules, with 2,361 lines of Lean source.

## Structural decomposition

- Added finite bipartite edge sets, degrees, and an extraction theorem that
  terminates after at most D capacitated matching rounds.
- Defined maximum log-skewness over finite, concrete subgraph witnesses with
  explicit admissibility conditions.
- Proved hereditary Hall expansion from that graph parameter, rather than
  assuming the expansion conclusion.
- Proved exact edge-disjoint decomposition for any valid schedule ending at
  degree zero.
- Instantiated the schedule at scales f_i = 2^(2^(i+1)), including integer
  rounding, explicit termination, and exact degree bounds.
- Proved a partition with exactly
  floor(log_2(floor(log_2(16 B)) + 1)) pieces under the stated preprocessing
  degree hypotheses. Every indexed piece has left degree at most 16 B / f_i
  and right degree at most 16 B (f_i log n)^(2 sigma).

The almost-linear running time is not proved. Identifying all preprocessing
parameters with the paper's original graph interface remains separate work.

## Execution and occurrence witnesses

- Added an execution log retaining a distinct time label for every arrival.
- Proved exact replay of the residual arrivals by a single ordinary Greedy
  process, shared across all classes.
- Proved that threshold counters count the actual threshold occurrences.
- Proved uniqueness of time labels, the threshold/residual partition, and
  disjointness of threshold and residual time labels.
- Proved that every residual arrival forces alpha_i distinct earlier threshold
  occurrences in its bucket, disjoint from the full execution's residual log.

The indexed `IsGreedy` adapter and the component-restriction bridge remain open.

## Sampling and joint witness probability

- Proved P[Bin(T,p) >= k] <= choose(T,k) p^k directly in the finite i.i.d. space.
- Derived the exponential bound (e T p / k)^k and a finite-family maximum-degree
  union bound.
- Proved exact product probabilities for injectively assigned time slots.
- Encoded tree slots and unordered threshold time sets; rejected every witness
  with a collision before using independence.
- Proved the generic joint witness bound

  P[witness event] <= (T/|E|)^m product_j
      choose(T,alpha_j) (|A_j|/|E|)^(alpha_j),

  and its exponential version. This is the raw counting/probability structure
  of Equations (10)--(12).

The containment of each fixed residual-tree event in this abstract witness
event, the pattern-embedding count, and the final parameter simplification
have not yet been proved. Neither the component-shattering lemma nor the main
O(log log n) competitive theorem is claimed complete.


# Continuation 2

The checked result count increased from 163 to 228. There are now 36 source
modules, with 3,575 lines of Lean source.

## Actual execution to fixed-tree probability

- Linked each logged event to its original input position and edge label.
- Proved a residual occurrence saturates its bucket in the full execution.
- Constructed finite threshold time sets with exact cardinalities, and proved
  that distinct buckets have disjoint time sets.
- Encoded those time sets and the selected residual edges into the abstract
  joint witness event, proving global injectivity of all required time slots.
- Proved the raw exponential fixed-tree probability bound for the actual
  Threshold-Greedy execution.

## Embedding counts and geometric decay

- Counted sequential assignments with arbitrary prefix-dependent menus.
- Defined parent-before-child patterns and concrete edge-labelled embeddings.
- Proved uniqueness of edge labels from vertex assignments for a simple
  bipartite source, and bounded embeddings by the degree-product formula.
- Combined the embedding count with the actual residual-tree probability bound.
- Proved the left-heavy branching cancellation and explicit logarithmic
  threshold conditions sufficient for geometric per-pattern decay.

These are conditional quantitative theorems: the paper's chosen alpha_i values
have not yet been shown to satisfy the sufficient threshold inequalities.

## Shapes and probability tails

- Constructed canonical plane rooted patterns from binary forests with m nodes.
- Used the checked Catalan enumeration to bound shape codes by 4^m |C|^m.
- Proved a class-labelled canonical shape union bound, geometric decay, and an
  explicit inverse-polynomial failure bound.

The arbitrary-component-to-canonical-witness coverage and leaf-pruning argument
are still open; these shape tails are not claimed as full component shattering.

## Residual replay and benchmark

- Proved that state increments equal indexed prefix occurrence counts.
- Constructed an indexed orientation of ordinary Greedy replay and proved
  `IsGreedy` and exact agreement of final loads.
- Applied the checked deterministic Greedy bound to the implementation's actual
  residual left and right loads.
- Proved optimum monotonicity under deleting arrival occurrences, and bounded
  the residual Greedy load against the full sample's offline optimum.

The component-local vertex restriction and the main O(log log n) competitive
theorem remain open.


# Continuation 3

The checked result count increased from 228 to 279. There are now 44 source
modules, with 4,371 lines of Lean source.

## Component-local execution and expectation

- Localized the Greedy layer inequality to arbitrary edge-closed vertex sets.
- Defined the actual arrival graph and proved that each component is closed,
  including loop and repeated-occurrence handling.
- Proved the component-local logarithmic bound against the full optimum.
- Applied it to the implemented residual state, including empty residual runs.
- Combined residual and threshold loads into the full implemented maximum.
- Proved the exact multiplier `4 (floor(log₂ ell)+1)` for component sizes at most
  ell squared.
- Defined the actual large-component event and proved the expectation reduction
  with additive exceptional cost `T P[large component]`.

## Spanning trees and right-leaf pruning

- Extracted spanning trees from actual arrival components, preserving their
  vertex count and the existence of an original occurrence for every edge.
- Proved that internal vertices of a simple path have degree at least two.
- Proved that retaining all left vertices and right vertices of degree at least
  two preserves connectivity and the tree property.
- Proved that retained right degrees are unchanged, and that the pruned tree
  has strictly more left than right vertices by the exact degree-sum identity.
- Proved the size guarantee `|V| ≤ (D+1) |V_pruned|` and a combined extraction
  theorem for arbitrary connected bipartite graphs with bounded left degree.
- Bounded actual residual left neighborhoods by full-sample bucket hits and
  proved their exponential union tail.

The remaining coverage problem is representational and probabilistic: connect
these graph reductions to canonical shape codes, right roots, class labels,
and actual residual pattern events. That integration is not assumed proved.

## Concrete thresholds and all-size canonical tails

- Gave an explicit ceil-and-increment threshold formula satisfying the two
  sufficient local inequalities; geometric shape decay follows without leaving
  either threshold inequality as a premise.
- Proved a union bound over every canonical tree size from k through k+B,
  giving tail at most `2 |R| / 2^k` from the corresponding fixed-size tails.

The explicit thresholds have not been shown to fit the paper's asymptotic
budget. Neither component shattering, the log-skewness lower bound, nor the
main O(log log n) theorem is claimed complete.


# Continuation 4

The checked result count increased from 279 to 324. There are now 53 source
modules, with 5,269 lines of Lean source.

## Actual components to geometric heavy trees

- Proved exact agreement between replay graph adjacency and arrival-list
  membership, and between left graph degree and distinct list neighborhoods.
- Proved that component restriction preserves every vertex degree.
- Applied spanning-tree extraction and pruning to an actual replay component,
  constructing a large left-heavy tree and a right root whenever its size is
  greater than one.
- Defined the actual large-left-degree and geometric-heavy-tree events.
- Proved that a component larger than `(D+1)(k+1)` forces a left-degree
  exception above D or a geometric left-heavy tree larger than k+1.

## Geometric canonical embeddings to counted events

- Proved that residual-list membership is equivalent to an original residual
  occurrence time, and derived the corresponding graph-adjacency equivalence.
- Proved that injective parent-before-child vertex data force distinct edge
  labels, including edges pointing in opposite bipartite directions.
- Proved assignment-menu validity from geometric edge data.
- Turned injective labelled embeddings with actual residual occurrences into
  membership in the exact previously bounded pattern event.
- For an unlabelled canonical geometric embedding, constructed edge classes and
  globally distinct occurrence witnesses from execution, proving membership
  in the counted class-labelled shape event.

The canonical enumeration of every abstract extracted tree is still open.
These results do not assume or claim that enumeration theorem.

## Threshold instantiation and finite budget

- Instantiated decay parameters as `r=1/(8h)` and `b=r²/(Dz+1)`.
- Proved all positivity, branching-cancellation, and class-count inequalities.
- Obtained canonical geometric shape tails for a concrete integer threshold
  vector without local numerical decay premises.
- Derived the threshold's logarithmic requirement from a multiplicative right
  branching bound, including zero right degree.
- Summed reciprocal logarithms at doubly exponential scales.
- Proved the exact threshold-budget bound
  `h (16 e B z+2 sigma+2) + (log(16 B z/b)+2 sigma log L)/log 2`
  directly from the decomposition's real degree bounds, including rounding.

The final asymptotic comparison and preprocessing-parameter integration remain
open; the finite budget is not asserted to prove the main competitive theorem.

## Conditional quantitative shattering and expectation

- Combined actual component pruning, the degree tail, and the canonical shape
  union bound with an explicit remaining `hcoverage` containment premise.
- Defined the logarithmic cutoff `(c+1)(floor(log₂ N)+1)` and proved its power
  inequality, removing an otherwise uninstantiated exponent condition.
- Proved conditional actual-component failure at most `3/N^c` and expected-load
  error at most `3T/N^c`.
- Instantiated those conditional statements for the concrete automatic
  thresholds, so no canonical probability bound is left as an assumption.

The remaining deterministic canonical-coverage premise is visible in every
such theorem. Neither unconditional shattering nor the main competitive
theorem has been postulated or claimed proved.


# Continuation 5

The checked result count increased from 324 to 351. There are now 59 source
modules, with 5,933 lines of Lean source.

## Canonical coverage completed

- Defined labelled first-child/next-sibling forests with recursive actual
  graph edges and preorder labels.
- Proved insertion of a fresh adjacent vertex at any visited vertex.
- Used bounded maximal node count and connectivity to construct a spanning
  forest whose external root and node labels are nonrepeating.
- Proved exact node count, agreement of labelled and erased preorder parent
  indices, and agreement of bipartite side annotations.
- Constructed a canonical shape and a bijection from its vertex indices to the
  original connected graph, preserving the root and every parent edge.
- Proved that the non-root left-index count equals the original left-vertex
  count exactly.
- Proved `largeHeavyTree_subset_largeShape`, discharging the previously open
  canonical-coverage containment for actual residual executions.

## Finite component shattering without a coverage premise

- Applied the proved containment to the existing canonical pattern probability
  bounds and automatic integer thresholds.
- Obtained actual-component failure at most `3/N^c` and expected-load error at
  most `3T/N^c`, without a coverage or per-pattern probability premise.
- Chose the sampled-degree cutoff from an actual source-bucket degree bound,
  removing the previously assumed numerical mean inequality.
- Proved the explicit log-squared component threshold
  `3 ((c+1)(floor(log₂ N)+1)+1)²` under the stated expected-degree bound.
- Derived that mean bound from the preprocessing-scale assumptions
  `M ≤ d log N`, `2|E|=Nd`, `T ≤ N`, and `c ≥ 5`.

These are concrete finite results for the automatic threshold vector under
explicit graph and degree inputs. The paper's main asymptotic competitive
theorem remains open: the lower bounds and complete original-graph parameter
integration still need to be combined with the threshold budget. The
log-skewness lower bound, general-horizon reductions and Greedy lower-bound
construction are not claimed complete.


# Continuation 6

The checked result count increased from 351 to 393. There are now 64 source
modules, with 6,451 lines of Lean source.

## Actual partition to execution data

- Constructed an edge-class map from the proved exact partition, using the
  graph's concrete endpoint pairs as the source-edge labels.
- Proved simplicity, class-piece membership, class-bucket bounds and full
  left-bucket bounds by explicit injections into graph neighborhoods.
- Defined actual maximum piece degrees and transferred the decomposition's
  real scale bounds to those maxima.
- Constructed `PreparedDecomposition` from the proved peeling partition under
  the original finite preprocessing hypotheses; no partition-existence or
  per-piece degree conclusion is assumed.

## Implementation as an actual online policy

- Defined the policy using only preceding source-edge labels and the current
  edge, running the existing threshold/Greedy implementation on that prefix.
- Proved the full threshold-plus-residual state increment for each choice.
- Proved exact agreement between implemented final vertex loads and the
  original indexed policy orientation, hence equality of maximum costs.
- Proved full-sample offline optima and expected optima agree across the list
  and original sampling interfaces.

## Exact automatic threshold budget

- Converted the scale budget to the actual finite class index set.
- Applied it to the same automatic threshold vector, rate and branching target
  used by the implementation and component-tail theorem.
- Derived the required positive class count and reference cap from a nonempty
  concrete base graph.
- At `T=N`, derived the budget's mass inequality from `2|E|=Nd` and `d ≤ 16B`.

## Quantitative preprocessed online-policy theorem

- Applied the proved component tail using only the prepared graph's certified
  degrees and edge classes.
- Proved `PreparedDecomposition.expected_cost_at_vertex_horizon`, with the
  original indexed expected cost and offline optimum at `T=N`.
- Proved `exists_decomposed_online_policy`: constructs a partition and an
  actual online policy from graph-level preprocessing assumptions, and bounds
  its expected cost by the explicit threshold budget, the component-logarithm
  multiplier times `E[OPT]`, and `3N/N^c`.

The full competitive theorem remains open. In particular, the log-skewness
lower bound, asymptotic comparison of the finite threshold budget, complete
original-graph preprocessing and general-horizon reductions are not claimed
proved by this quantitative preprocessed result.


# Continuation 7

The checked result count increased from 393 to 425. There are now 69 source
modules, with 6,992 lines of Lean source.

## Density lower bounds with integer rounding

- Defined maximum density directly over the actual finite source-edge model.
- Maximized the proved subset-density lower bound for the sampled optimum.
- Proved that one source label's expected occurrence count is at most twice
  the expected optimum using its at-most-two endpoint vertices.
- Proved `referenceCap T/|E| ≤ 3 E[OPT]`, retaining the capacity ceiling.
- Bounded the rounded reference capacity by the source edge count and derived
  the average-degree comparison from the whole-vertex density obstruction.

## Simplified automatic budget

- Expanded the exact automatic branching target inside its logarithm.
- Proved a universal scalar bound reducing the budget to
  `64 (Bz+sigma+1)(h+log log N+1)`.
- Bounded the actual class count by an integer log-log scale, using the proved
  source reference-cap and simple bipartite edge-count bounds.
- Obtained the explicit bound `320 (Bz+sigma+1) Q(N)` for the exact thresholds.

## Preprocessed asymptotic comparison

- Bounded the component-local Greedy multiplier by `20 Q(N)` and absorbed the
  exceptional-sample error using the proved `E[OPT] ≥ 1`.
- Constructed an actual preprocessed online policy with expected cost at most
  `1400 Q(N) (E[OPT]+sigma)`.
- Proved `Q(N) ≤ 3 L(N)` for the main target's real log-log factor and obtained
  `E[cost] ≤ 4200 L(N) (E[OPT]+sigma)`.
- Removed the average-degree reference-cap hypothesis from the graph-level
  existence theorem by proving it from the density obstruction.

The skewness lower bound is still open. The competitive corollaries state
`sigma ≤ K E[OPT]` explicitly as an assumption and are labelled conditional.
The new graph-level bound itself does not assume that lower bound; sigma is
retained on its right-hand side. Original-graph preprocessing, small-size and
general-horizon reductions and the Greedy lower-bound construction remain
unfinished.

# Continuation 8

The checked result count increased from 425 to 470. There are now 77 source
modules, with 7,801 lines of Lean source.

## Log-skewness benchmark lower bound

- Proved exact block-hit probabilities and the lower bound `sp/(1+sp)`.
- Proved pairwise nonpositive covariance for disjoint left buckets successful
  in every independent block, without assuming negative association.
- Derived the occupancy second moment and an expected-density lower bound
  through a quadratic minorant; a separate concentration theorem is unnecessary.
- Constructed a concrete dense sampled induced subgraph, with distinct
  occurrences for every successful left-vertex/block pair.
- Proved uniform prefix restriction and expected-optimum horizon monotonicity.
- Verified the logarithmic threshold and rounded block-length comparisons.
- Maximized over actual skewness witnesses to prove `Skew(G) ≤ 8 E[OPT]`
  under the preprocessed hypotheses and `log N ≥ 2`.

## Completed preprocessed competitive guarantee

- Applied that proved benchmark bound to the existing actual online policy.
- Covered smaller N by the deterministic horizon bound.
- Proved `exists_preprocessed_competitive_policy`, with no minimum-size or
  skewness-lower-bound premise, giving `E[cost] ≤ 37800 L(N) E[OPT]` at `T=N`.
- The full original-graph main theorem is still open: original preprocessing
  and arbitrary-horizon reductions remain. The Greedy lower-bound construction
  is also unfinished.

# Continuation 9 — main upper-bound proof completed

The checked result count increased from 470 to 509. There are now 87 source
modules, with 8,726 lines of Lean source.

- Extended the skewness lower bound and decomposition policy to the actual
  arrival rate, separating the vertex-count bound from the sampling horizon.
- Proved a finite Jensen/exponential-moment maximum occupancy bound, yielding
  the expected left-endpoint cost for every horizon.
- Enlarged the reference capacity by `ceil(d/16)` and proved all sampling-mass,
  density-cost and reference-size bounds needed for the rate-adapted proof.
- Constructed a history-only ordinary Greedy policy and bounded its performance
  on the at-most-2T active sampled vertices for short horizons.
- Proved all arrival regimes for every left-degree-bounded bipartite graph,
  with guarantee `30000 L(N) E[OPT]` and no degree-reduction premise.
- Proved source-label/policy relabeling invariance, the once-per-base-edge
  density optimum, the actual original-graph split and its left-degree bound.
- Completed the source pullback, vertex collapse and size comparison to prove
  `exists_competitive_policy`: `E[cost] ≤ 120000 L(|V|) E[OPT]` for every
  nonempty simple graph and every horizon.
- Proved the exact original target as `GraphChoices.mainTheorem : MainTheorem`.

The main upper bound is complete. The Greedy lower-bound construction and
other remaining paper statements are listed separately in STATUS.md.

# Continuation 10 — Greedy lower bound completed

The checked result count increased from 509 to 578. There are now 101 source
modules, with 10,077 lines of Lean source.

- Defined an ordinary history-dependent Greedy process with independent fair
  tie coins, proved its Greedy rule and prefix-load invariant, and certified
  exact fair tie probabilities and preservation of the offline benchmark.
- Constructed the concrete layered graph from complete bipartite blocks,
  proved its simplicity and exact vertex and source-edge counts.
- Proved a deterministic marked-arrival batch forcing and layer propagation
  theorem, an exact finite binomial lower tail, and the full batch union bound.
- Proved subset-count/binomial-density cancellation for complete blocks,
  polynomially small dense-block failure and the resulting global optimum
  capacity bound. The expected optimum includes exceptional samples.
- Instantiated integral parameters `b ≥ 16`, `t=(16b)³`, `m=2t^b`, with exactly
  N vertex-horizon samples and exact batch lengths N/b.
- Obtained failure at most `N⁻²` for load below
  `log(N)/(26 log(log(N)))`, and `E[OPT] ≤ 500 log(log(N))`.
- Proved the literal degree interval `[sqrt(N), sqrt(N) log(N)³]`.
- Proved an actual infinite family with competitive gap at least
  `log(N)/(30000 (log(log(N)))²)` as `LowerBound.greedyLowerBound`.

Both main theorems are now proved. Auxiliary statements not used by these
proofs and running-time guarantees remain separately listed in STATUS.md.

# Dependency graph package

Added an offline PFR-style file-import dependency viewer, covering all 101
modules and 578 checked results. It includes 141 direct imports and a
reachability-preserving 137-edge reduced graph, interactive highlighting,
search, focus, pan/zoom, linked line-numbered source pages, SVG/DOT/JSON exports,
and a Python/Graphviz regeneration script. The graph is explicitly labelled
as file imports rather than individual theorem proof dependencies.

No Lean proof sources changed; the existing successful full build and axiom
audit remain the validation record for the formalization.
