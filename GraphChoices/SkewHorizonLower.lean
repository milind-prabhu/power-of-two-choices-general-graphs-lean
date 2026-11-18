import GraphChoices.SkewLowerBound

/-! The skewness benchmark at an arbitrary sampling horizon T, provided
log N ≤ T and N bounds the base vertex count. -/
namespace GraphChoices.Peeling
open Finset
variable {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]

theorem skewValue_le_eight_expectedOpt_horizon (G F : Graph L R) [Nonempty G]
    (hF : F ⊆ G) (A : Finset L) (N T : ℕ) (d : ℝ)
    (hd : 0 < d) (hlog : 2 ≤ Real.log (N:ℝ)) (hlogT : Real.log (N:ℝ) ≤ T)
    (hleft : ∀ u, (leftDegree G u:ℝ) ≤ d*Real.log (N:ℝ))
    (hvertices : Fintype.card (L ⊕ R) ≤ N)
    (haverage : 2*(G.card:ℝ) = (T:ℝ)*d)
    (hadm : SkewAdmissible F A d (N:ℝ)) :
    skewValue F A d (N:ℝ) ≤ 8*expectedOpt (graphBase G) T := by
  let a : ℝ := A.card
  let b : ℝ := (neighborSet F A).card
  let δ : ℝ := minLeftDegree F A
  let σ := skewValue F A d (N:ℝ)
  let k : ℕ := ⌊σ/2⌋₊
  have ha : 0 < a := by dsimp only [a]; exact_mod_cast hadm.1.card_pos
  have hb : 1 ≤ b := by
    dsimp only [b]
    exact_mod_cast (show 1 ≤ (neighborSet F A).card from hadm.2.1.card_pos)
  have hδ : 0 < δ := by dsimp only [δ]; exact_mod_cast hadm.2.2.2.1
  have han : a ≤ N := by
    have hh : A.card ≤ N := (card_le_univ A).trans
      ((by simp only [Fintype.card_sum]; omega : Fintype.card L ≤ Fintype.card (L ⊕ R)).trans hvertices)
    dsimp only [a]
    exact_mod_cast hh
  obtain ⟨u,hu⟩ := hadm.1
  have hdeg : δ ≤ d*Real.log (N:ℝ) := by
    apply le_trans _ (hleft u)
    dsimp only [δ]
    exact_mod_cast (minLeftDegree_le F hu).trans (leftDegree_mono hF u)
  have hσ : 0 ≤ σ := by
    apply div_nonneg
    · apply Real.log_nonneg
      apply (one_le_div (by linarith : 0 < b)).mpr
      dsimp only [b]
      exact_mod_cast hadm.2.2.1
    · exact (Real.log_pos hadm.2.2.2.2).le
  have hkfloor : 2*(k:ℝ) ≤ σ := by
    have hh := Nat.floor_le (by linarith : 0 ≤ σ/2)
    change (⌊σ/2⌋₊:ℝ) ≤ σ/2 at hh
    dsimp only [k]
    linarith
  have hσk : σ < 2*((k:ℝ)+1) := by
    have hh := Nat.lt_floor_add_one (σ/2)
    change σ/2 < (k:ℝ)+1 at hh
    linarith
  have hN : 0 < N := by
    by_contra h
    have hh : N = 0 := by omega
    norm_num [hh] at hlog
  have hT : 0 < T := by
    have hh : (0:ℝ) < T := by linarith
    exact_mod_cast hh
  have hopt := expectedOpt_ge_one (graphBase G) T hT
  by_cases hk : k = 0
  · have hh : (k:ℝ) = 0 := by simp [hk]
    change σ ≤ _
    linarith
  have hkpos : 0 < k := Nat.pos_of_ne_zero hk
  have hkr : (0:ℝ) < k := by exact_mod_cast hkpos
  have hklog : (k:ℝ) ≤ Real.log (N:ℝ) :=
    skew_threshold_le_log ha hb han hδ hd hlog hdeg k hkfloor
  have hkT : k ≤ T := by exact_mod_cast hklog.trans hlogT
  let x := min 1 (δ/d)/(k:ℝ)
  have hx : 0 ≤ x := div_nonneg (le_min (by norm_num) (div_nonneg hδ.le hd.le)) hkr.le
  have hx1 : x ≤ 1 := by
    apply (div_le_one hkr).mpr
    have hh : (1:ℝ) ≤ k := by exact_mod_cast hkpos
    exact (min_le_left _ _).trans hh
  have hmean : x ≤ ((T/k : ℕ):ℝ)*(δ/G.card) :=
    block_length_mean T k hkpos hkT δ d G.card hδ.le hd
      (by exact_mod_cast (show 0 < G.card by simpa only [← Fintype.card_coe] using Fintype.card_pos (α := G))) haverage
  have hpop : b ≤ a*(x/2)^k :=
    skew_block_population ha hb han hδ hd hlog hdeg k hkpos hkfloor
  have hlower := expectedOpt_subgraph_blocks G F hF A hadm.2.1 k (T/k) x hx hx1 hmean hpop
  have hmon := expectedOpt_mono_horizon (graphBase G) (by simpa only [Nat.mul_comm] using Nat.div_mul_le_self T k)
  have hlow : (k:ℝ)/3 ≤ expectedOpt (graphBase G) T := hlower.trans hmon
  change σ ≤ _
  linarith

/-- Concrete graph log-skewness is absorbed into the actual expected
offline optimum; no skewness-lower-bound premise remains. -/
theorem graphLogSkewness_le_eight_expectedOpt_horizon (G : Graph L R) [Nonempty G]
    (N T : ℕ) (d : ℝ) (hd : 0 < d) (hlog : 2 ≤ Real.log (N:ℝ)) (hlogT : Real.log (N:ℝ) ≤ T)
    (hleft : ∀ u, (leftDegree G u:ℝ) ≤ d*Real.log (N:ℝ))
    (hvertices : Fintype.card (L ⊕ R) ≤ N)
    (haverage : 2*(G.card:ℝ) = (T:ℝ)*d) :
    graphLogSkewness G d (N:ℝ) ≤ 8*expectedOpt (graphBase G) T := by
  classical
  unfold graphLogSkewness
  apply (sup'_le_iff _ _).mpr
  intro y hy
  rcases mem_insert.mp hy with rfl | hy
  · have hh := expectedOpt_nonneg (graphBase G) T
    dsimp only [id]
    linarith
  · obtain ⟨⟨F,A⟩,hFA,rfl⟩ := mem_image.mp hy
    have hh := mem_filter.mp hFA
    have hF : F ⊆ G := mem_powerset.mp (mem_product.mp hh.1).1
    exact skewValue_le_eight_expectedOpt_horizon G F hF A N T d hd hlog hlogT hleft hvertices haverage hh.2

end GraphChoices.Peeling
