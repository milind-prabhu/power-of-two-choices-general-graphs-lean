import GraphChoices.PreparedDecomposition

/-! A quantitative expected-cost theorem for an actual online policy built
from the proved decomposition of a concrete preprocessed bipartite graph.
No per-piece degree, sampling-tail, or tree-coverage premise is assumed.
The final asymptotic lower-bound comparison remains separate.
-/
namespace GraphChoices.Peeling
open Finset
open ThresholdGreedy
open Patterns
variable {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
  {G : Graph L R} {B N : ℕ} {d : ℝ} [Nonempty G]

theorem PreparedDecomposition.component_tail (P : PreparedDecomposition G B N d) (T c : ℕ)
    (hT : 0 < T) (hTN : T ≤ N) (hc : 5 ≤ c)
    (hvertices : Fintype.card (L ⊕ R) ≤ N)
    (haverage : 2*(G.card : ℝ) = (N:ℝ)*d) :
    eventProbability (largeComponentEvent P.encode (P.thresholds T) T
      (3*(polynomialCutoff N c+1)^2)) ≤ 3/(N:ℝ)^c := by
  have hv : Fintype.card L + Fintype.card R ≤ N := by simpa only [Fintype.card_sum] using hvertices
  have hLN : Fintype.card L ≤ N := by omega
  have hRN : Fintype.card R ≤ N := by omega
  exact preprocessed_log_squared_component_tail P.pieces.get P.encode P.DL P.DR
    (4*B) (maxLeftDegree G) T N c (fun i => scaleNat i.val) d P.simple P.source
    P.bucket_bound P.piece_left_cap P.piece_right_cap P.global_bucket_bound
    hT hTN P.scale_gt_one P.vertex_count_pos hLN hRN hc P.max_degree_preprocessing
    (by simpa only [Fintype.card_coe] using haverage)

/-- Concrete finite form of the preprocessed T=N algorithmic guarantee.
The policy is nonanticipating by construction, and its cost and benchmark
are the original indexed sampling definitions. The threshold budget is the
explicit formula derived from this exact decomposition's real degree bounds. -/
theorem PreparedDecomposition.expected_cost_at_vertex_horizon (P : PreparedDecomposition G B N d)
    (c : ℕ) (hc : 5 ≤ c) (hvertices : Fintype.card (L ⊕ R) ≤ N)
    (haverage : 2*(G.card : ℝ) = (N:ℝ)*d) :
    expectedCost (graphBase G) (onlineOrientation (T := N) (P.policy N)) ≤
      P.budget N + (2*(Nat.log 2 (3*(polynomialCutoff N c+1)^2)+1) : ℕ)*
        expectedOpt (graphBase G) N + 3*N/(N:ℝ)^c := by
  have ht := P.component_tail N c P.vertex_count_pos le_rfl hc hvertices haverage
  have h := expected_load_of_component_tail P.encode (P.thresholds N) N _ _ ht
  rw [expectedTotalMaxLoad_eq_expectedCost, expectedReplayOpt_eq_expectedOpt] at h
  change expectedCost (graphBase G) (onlineOrientation (T := N) (P.policy N)) ≤
    (∑ i, (P.thresholds N i : ℝ)) + (2*(Nat.log 2 (3*(polynomialCutoff N c+1)^2)+1) : ℕ)*
      expectedOpt (graphBase G) N + N*(3/(N:ℝ)^c) at h
  have hb := P.threshold_budget N (P.mass_at_vertex_horizon haverage)
  calc
    _ ≤ _ := h
    _ ≤ P.budget N + (2*(Nat.log 2 (3*(polynomialCutoff N c+1)^2)+1) : ℕ)*
        expectedOpt (graphBase G) N + N*(3/(N:ℝ)^c) := add_le_add_right (add_le_add_right hb _) _
    _ = _ := by ring

/-- Existence of an actual source-edge online policy from the graph-level
preprocessing assumptions. The decomposition is constructed by the proved
peeling theorem; it is not an input existence hypothesis. -/
theorem exists_decomposed_online_policy (G : Graph L R) [Nonempty G] (B N : ℕ) (d : ℝ)
    (hd : 0 < d) (hlog : 1 < Real.log (N:ℝ))
    (hleft : ∀ u, (leftDegree G u : ℝ) ≤ d*Real.log (N:ℝ))
    (hB : d ≤ 16*B) (hD : ∀ u, leftDegree G u ≤ 4*B)
    (hvertices : Fintype.card (L ⊕ R) ≤ N)
    (haverage : 2*(G.card : ℝ) = (N:ℝ)*d) (c : ℕ) (hc : 5 ≤ c) :
    ∃ P : PreparedDecomposition G B N d, ∃ p : OnlinePolicy G,
      p = P.policy N ∧
      expectedCost (graphBase G) (onlineOrientation (T := N) p) ≤ P.budget N +
        (2*(Nat.log 2 (3*(polynomialCutoff N c+1)^2)+1) : ℕ)*expectedOpt (graphBase G) N +
          3*N/(N:ℝ)^c := by
  obtain ⟨P⟩ := exists_preparedDecomposition G B N d hd hlog hleft hB hD
  exact ⟨P, P.policy N, rfl, P.expected_cost_at_vertex_horizon c hc hvertices haverage⟩

end GraphChoices.Peeling
