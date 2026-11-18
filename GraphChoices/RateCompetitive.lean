import GraphChoices.HorizonDecomposition

namespace GraphChoices.Peeling
open Finset
variable {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]

noncomputable def rateReference (G : Graph L R) (d : ℝ) : ℕ :=
  (graphBase G).referenceCap+⌈d/16⌉₊

theorem rateReference_bounds (G : Graph L R) [Nonempty G] (N T : ℕ) (d : ℝ)
    (hT : 0 < T) (hd : 0 < d) (hvertices : Fintype.card (L ⊕ R) ≤ N)
    (haverage : 2*(G.card:ℝ) = (T:ℝ)*d) :
    d ≤ 16*(rateReference G d:ℝ) ∧ rateReference G d ≤ N^2 ∧
      (rateReference G d:ℝ)*((T:ℝ)/G.card) ≤ 6*expectedOpt (graphBase G) T := by
  have hTr : (1:ℝ) ≤ T := by exact_mod_cast hT
  have hM : (0:ℝ) < G.card := by
    exact_mod_cast (show 0 < G.card by simpa only [← Fintype.card_coe] using Fintype.card_pos (α := G))
  have hdM : d ≤ 2*(G.card:ℝ) := by nlinarith
  have hceilM : ⌈d/16⌉₊ ≤ G.card := Nat.ceil_le.mpr (by linarith)
  have hbaseM : (graphBase G).referenceCap ≤ G.card := by simpa only [Fintype.card_coe] using (graphBase G).referenceCap_le_edges
  have hBM : rateReference G d ≤ 2*G.card := by unfold rateReference; omega
  have hMprod : G.card ≤ Fintype.card L*Fintype.card R := by simpa only [Fintype.card_prod] using card_le_univ G
  have hsum : Fintype.card L+Fintype.card R ≤ N := by simpa only [Fintype.card_sum] using hvertices
  have hM2 : 2*G.card ≤ N^2 := by nlinarith [Nat.mul_self_le_mul_self hsum]
  have hc := Nat.le_ceil (d/16)
  have hcap : d ≤ 16*(rateReference G d:ℝ) := by
    unfold rateReference
    push_cast
    have hbase : (0:ℝ) ≤ (graphBase G).referenceCap := Nat.cast_nonneg _
    linarith
  refine ⟨hcap, hBM.trans hM2, ?_⟩
  have hceil : (⌈d/16⌉₊:ℝ) ≤ d/16+1 := (Nat.ceil_lt_add_one (by linarith : 0 ≤ d/16)).le
  have hz : 0 ≤ (T:ℝ)/G.card := by positivity
  have hh := mul_le_mul_of_nonneg_right hceil hz
  have heq : (d/16)*((T:ℝ)/G.card) = 1/8 := by
    apply (eq_div_iff (by norm_num : (8:ℝ) ≠ 0)).mpr
    field_simp
    nlinarith
  have hb := expected_reference_cap_bound (graphBase G) T
  have he := expected_edge_rate_le_two_opt (graphBase G) T
  rw [Fintype.card_coe] at hb he
  have ho := expectedOpt_ge_one (graphBase G) T hT
  unfold rateReference
  push_cast
  rw [add_mul]
  nlinarith

theorem exists_rate_competitive_policy (G : Graph L R) [Nonempty G] (N T : ℕ) (d : ℝ)
    (hT : 0 < T) (hd : 0 < d) (hlog : 2 ≤ Real.log (N:ℝ))
    (hlogT : Real.log (N:ℝ) ≤ T) (hTN : T ≤ N)
    (hleft : ∀ u, (leftDegree G u:ℝ) ≤ d*Real.log (N:ℝ))
    (hD : ∀ u, leftDegree G u ≤ 4*(graphBase G).referenceCap)
    (hvertices : Fintype.card (L ⊕ R) ≤ N)
    (haverage : 2*(G.card:ℝ) = (T:ℝ)*d) :
    ∃ p : OnlinePolicy G, expectedCost (graphBase G) (onlineOrientation (T := T) p) ≤
      15000*loglogFactor N*expectedOpt (graphBase G) T := by
  obtain ⟨hcap,hBsquare,hBmean⟩ := rateReference_bounds G N T d hT hd hvertices haverage
  have hBbase : (graphBase G).referenceCap ≤ rateReference G d := by unfold rateReference; omega
  obtain ⟨P⟩ := exists_preparedDecomposition G (rateReference G d) N d hd (by linarith) hleft hcap
    (fun u => (hD u).trans (Nat.mul_le_mul_left 4 hBbase))
  refine ⟨P.policy T, ?_⟩
  have hh := P.expected_cost_horizon T hT hTN hvertices haverage hBsquare
  have hs := graphLogSkewness_le_eight_expectedOpt_horizon G N T d hd hlog hlogT hleft hvertices haverage
  have ho := expectedOpt_ge_one (graphBase G) T hT
  have hQ : (1:ℝ) ≤ iteratedLog N := by exact_mod_cast iteratedLog_pos N
  have hsum : (rateReference G d:ℝ)*((T:ℝ)/G.card)+graphLogSkewness G d (N:ℝ)+1 ≤
      15*expectedOpt (graphBase G) T := by linarith
  have hcost : expectedCost (graphBase G) (onlineOrientation (T := T) (P.policy T)) ≤
      5000*(iteratedLog N:ℝ)*expectedOpt (graphBase G) T := by
    have hm := mul_le_mul_of_nonneg_right hsum (by positivity : 0 ≤ 320*(iteratedLog N:ℝ))
    have hqe : 1 ≤ (iteratedLog N:ℝ)*expectedOpt (graphBase G) T := by nlinarith
    nlinarith
  apply hcost.trans
  have hcomp := iteratedLog_le_real_factor N (by linarith)
  have hm := mul_le_mul_of_nonneg_right hcomp (show 0 ≤ 5000*expectedOpt (graphBase G) T by positivity)
  nlinarith

end GraphChoices.Peeling
