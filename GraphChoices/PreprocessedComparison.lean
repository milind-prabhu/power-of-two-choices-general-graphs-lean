import GraphChoices.IteratedLogBounds
import GraphChoices.ExpectedDensity

/-! The finite preprocessed online policy has log-log expected cost times
E[OPT] plus the actual graph log-skewness. The subsequent SkewLowerBound module proves the benchmark comparison needed
to absorb that last graph parameter into E[OPT] in the preprocessed regime. -/
namespace GraphChoices.Peeling
open Finset
variable {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]

theorem graph_card_le_square (G : Graph L R) (N : ℕ)
    (hvertices : Fintype.card (L ⊕ R) ≤ N) : G.card ≤ N^2 := by
  have hsum : Fintype.card L + Fintype.card R ≤ N := by simpa only [Fintype.card_sum] using hvertices
  have hL : Fintype.card L ≤ N := by omega
  have hR : Fintype.card R ≤ N := by omega
  calc
    _ ≤ Fintype.card (L × R) := card_le_card (subset_univ _)
    _ = Fintype.card L*Fintype.card R := Fintype.card_prod _ _
    _ ≤ N*N := Nat.mul_le_mul hL hR
    _ = _ := by ring

theorem average_le_two_referenceCap (G : Graph L R) [Nonempty G] (N : ℕ) (d : ℝ)
    (hN : 0 < N) (hvertices : Fintype.card (L ⊕ R) ≤ N)
    (haverage : 2*(G.card : ℝ) = (N:ℝ)*d) : d ≤ 2*(graphBase G).referenceCap := by
  have hNr : (0:ℝ) < N := by exact_mod_cast hN
  have hcard : (Fintype.card (L ⊕ R) : ℝ) ≤ N := by exact_mod_cast hvertices
  have he := (graphBase G).total_edges_le_card_mul_referenceCap
  rw [Fintype.card_coe] at he
  have hcap : (0:ℝ) ≤ (graphBase G).referenceCap := Nat.cast_nonneg _
  have hbound := mul_le_mul_of_nonneg_right hcard hcap
  apply (mul_le_mul_left hNr).mp
  nlinarith

variable {G : Graph L R} {B N : ℕ} {d : ℝ} [Nonempty G]

theorem PreparedDecomposition.reference_cap_le_square (P : PreparedDecomposition G B N d)
    (hB : B = (graphBase G).referenceCap) (hvertices : Fintype.card (L ⊕ R) ≤ N) : B ≤ N^2 := by
  have he : B ≤ G.card := by
    rw [hB]
    simpa only [Fintype.card_coe] using (graphBase G).referenceCap_le_edges
  exact he.trans (graph_card_le_square G N hvertices)

theorem PreparedDecomposition.reference_density_bound (P : PreparedDecomposition G B N d)
    (hB : B = (graphBase G).referenceCap) :
    (B:ℝ)*((N:ℝ)/Fintype.card G) ≤ 3*expectedOpt (graphBase G) N := by
  rw [hB]
  exact expected_reference_cap_bound (graphBase G) N

/-- A fully quantified preprocessed guarantee with explicit universal constant.
No lower bound on log-skewness is assumed: it remains visibly additive to
the expected optimum on the right-hand side. -/
theorem PreparedDecomposition.expected_cost_density_skew (P : PreparedDecomposition G B N d)
    (hB : B = (graphBase G).referenceCap) (hvertices : Fintype.card (L ⊕ R) ≤ N)
    (haverage : 2*(G.card : ℝ) = (N:ℝ)*d) :
    expectedCost (graphBase G) (onlineOrientation (T := N) (P.policy N)) ≤
      1400*(iteratedLog N : ℝ)*(expectedOpt (graphBase G) N+graphLogSkewness G d (N:ℝ)) := by
  let q : ℝ := iteratedLog N
  let optE : ℝ := expectedOpt (graphBase G) N
  let σ : ℝ := graphLogSkewness G d (N:ℝ)
  have hq : 1 ≤ q := by
    change (1:ℝ) ≤ (iteratedLog N : ℝ)
    exact_mod_cast (show 1 ≤ iteratedLog N by have := iteratedLog_pos N; omega)
  have hopt : 1 ≤ optE := expectedOpt_ge_one _ _ P.vertex_count_pos
  have hs : 0 ≤ σ := graphLogSkewness_nonneg G d (N:ℝ)
  have hM := P.reference_density_bound hB
  have hbudget := P.budget_loglog (P.reference_cap_le_square hB hvertices) haverage
  have hbudget' : P.budget N ≤ 320*(4*optE+σ)*q := by
    apply hbudget.trans
    apply mul_le_mul_of_nonneg_right _ (by linarith)
    dsimp only [optE, σ]
    nlinarith
  have hcoeff : ((2*(Nat.log 2 (3*(polynomialCutoff N 5+1)^2)+1) : ℕ) : ℝ) ≤ 20*q := by
    change ((2*(Nat.log 2 (3*(polynomialCutoff N 5+1)^2)+1) : ℕ) : ℝ) ≤ 20*(iteratedLog N : ℝ)
    exact_mod_cast greedy_multiplier_le_iteratedLog N
  have hgreedy := mul_le_mul_of_nonneg_right hcoeff (show 0 ≤ optE by linarith)
  have hprod : 1 ≤ q*optE := by nlinarith
  have herror : 3*(N:ℝ)/(N:ℝ)^5 ≤ 3*q*optE := by
    apply (exceptional_error_le_three N P.vertex_count_pos).trans
    nlinarith
  have hcost := P.expected_cost_at_vertex_horizon 5 (by decide) hvertices haverage
  calc
    _ ≤ _ := hcost
    _ ≤ 320*(4*optE+σ)*q + (20*q)*optE + 3*q*optE :=
      add_le_add (add_le_add hbudget' hgreedy) herror
    _ ≤ _ := by nlinarith [mul_nonneg (show 0 ≤ q by linarith) hs,
      mul_nonneg (show 0 ≤ q by linarith) (show 0 ≤ optE by linarith)]

/-- Explicitly conditional corollary: the log-skewness benchmark comparison
is still an input here, rather than a postulated or claimed proved lemma. -/
theorem PreparedDecomposition.competitive_of_skew_lower_bound (P : PreparedDecomposition G B N d)
    (hB : B = (graphBase G).referenceCap) (hvertices : Fintype.card (L ⊕ R) ≤ N)
    (haverage : 2*(G.card : ℝ) = (N:ℝ)*d) (K : ℝ)
    (hskew : graphLogSkewness G d (N:ℝ) ≤ K*expectedOpt (graphBase G) N) :
    expectedCost (graphBase G) (onlineOrientation (T := N) (P.policy N)) ≤
      1400*(1+K)*(iteratedLog N : ℝ)*expectedOpt (graphBase G) N := by
  apply (P.expected_cost_density_skew hB hvertices haverage).trans
  calc
    _ ≤ 1400*(iteratedLog N : ℝ)*(expectedOpt (graphBase G) N+K*expectedOpt (graphBase G) N) :=
      mul_le_mul_of_nonneg_left (add_le_add_left hskew _) (by positivity)
    _ = _ := by ring

theorem exists_preprocessed_density_skew_policy (G : Graph L R) [Nonempty G] (N : ℕ) (d : ℝ)
    (hd : 0 < d) (hlog : 1 < Real.log (N:ℝ))
    (hleft : ∀ u, (leftDegree G u : ℝ) ≤ d*Real.log (N:ℝ))
    (hD : ∀ u, leftDegree G u ≤ 4*(graphBase G).referenceCap)
    (hvertices : Fintype.card (L ⊕ R) ≤ N)
    (haverage : 2*(G.card : ℝ) = (N:ℝ)*d) :
    ∃ p : OnlinePolicy G, expectedCost (graphBase G) (onlineOrientation (T := N) p) ≤
      1400*(iteratedLog N : ℝ)*(expectedOpt (graphBase G) N+graphLogSkewness G d (N:ℝ)) := by
  have hN : 0 < N := by
    by_contra hn
    have hz : N = 0 := by omega
    norm_num [hz] at hlog
  have hcap := average_le_two_referenceCap G N d hN hvertices haverage
  have hB : d ≤ 16*(graphBase G).referenceCap := by
    have hp : (0:ℝ) ≤ (graphBase G).referenceCap := Nat.cast_nonneg _
    linarith
  obtain ⟨P⟩ := exists_preparedDecomposition G (graphBase G).referenceCap N d hd hlog hleft hB hD
  exact ⟨P.policy N, P.expected_cost_density_skew rfl hvertices haverage⟩

end GraphChoices.Peeling
