import GraphChoices.BlockDensityTailArithmetic

namespace GraphChoices.LowerBound
open Finset
variable {C : Type*} [Fintype C] [DecidableEq C] [Nonempty C]

noncomputable def sizeDensityEvent (m r T k : ℕ) (c : C) (a b : ℕ) :
    Finset (Fin T → C × (Fin m × Fin r)) := by
  classical
  exact ((univ.powersetCard a) ×ˢ (univ.powersetCard b)).biUnion
    (fun p => hitTailEvent (blockAllowed c p.1 p.2) T (k*(a+b)))

theorem sizeDensityEvent_probability (m t T k : ℕ) (c : C) (a b : ℕ)
    (hm : 0 < m) (ht : 1 ≤ t) (ha : 0 < a) (hb : 0 < b)
    (ham : a ≤ m) (hbtm : b ≤ t*m) (hk : 16 ≤ k)
    (hrate : (T:ℝ)*(m:ℝ) ≤ 2*(Fintype.card (C × (Fin m × Fin (t*m))):ℝ))
    (hscale : Real.exp 1*(t:ℝ)*(2*Real.exp 1/(k:ℝ))^k ≤ 1/256) :
    eventProbability (sizeDensityEvent m (t*m) T k c a b) ≤ 1/(m:ℝ)^8 := by
  classical
  letI : Nonempty (Fin m) := ⟨⟨0,hm⟩⟩
  letI : Nonempty (Fin (t*m)) := ⟨⟨0,by positivity⟩⟩
  let E := C × (Fin m × Fin (t*m))
  have hE : (0:ℝ) < Fintype.card E := by exact_mod_cast Fintype.card_pos
  have hmr : (0:ℝ) < m := by exact_mod_cast hm
  have hkr : (0:ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  let tail := (2*Real.exp 1*(a:ℝ)*b/((m:ℝ)*k*(a+b)))^(k*(a+b))
  have heach (p : Finset (Fin m) × Finset (Fin (t*m)))
      (hp : p ∈ (univ.powersetCard a) ×ˢ (univ.powersetCard b)) :
      eventProbability (hitTailEvent (blockAllowed c p.1 p.2) T (k*(a+b))) ≤ tail := by
    have hcards := mem_product.mp hp
    have hA := (mem_powersetCard.mp hcards.1).2
    have hB := (mem_powersetCard.mp hcards.2).2
    apply (hitTail_probability_le_exp _ T (k*(a+b))).trans
    apply pow_le_pow_left₀ (by positivity)
    rw [blockAllowed_card,hA,hB]
    push_cast
    have hr : (T:ℝ)/Fintype.card E ≤ 2/(m:ℝ) :=
      (div_le_div_iff₀ hE hmr).mpr hrate
    have hh := mul_le_mul_of_nonneg_right hr
      (show 0 ≤ Real.exp 1*(a:ℝ)*b/((k:ℝ)*(a+b)) by positivity)
    convert hh using 1 <;> field_simp <;> ring
  apply (witness_union_bound _ _).trans
  apply (sum_le_sum heach).trans
  have heq : (∑ _p ∈ ((univ : Finset (Fin m)).powersetCard a) ×ˢ ((univ : Finset (Fin (t*m))).powersetCard b), tail) =
      (m.choose a:ℝ)*((t*m).choose b:ℝ)*tail := by
    simp only [sum_const, card_product, card_powersetCard, card_univ,
      Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul]
  rw [heq]
  exact block_size_pair_bound m t a b k hm ht ha hb ham hbtm hk hscale

noncomputable def badBlockDensity (m r T k : ℕ) : Finset (Fin T → C × (Fin m × Fin r)) := by
  classical
  exact univ.biUnion fun p : C × (Fin m × Fin r) =>
    sizeDensityEvent m r T k p.1 (p.2.1.val+1) (p.2.2.val+1)

theorem badBlockDensity_probability (m t T k : ℕ) (hm : 0 < m) (ht : 1 ≤ t) (hk : 16 ≤ k)
    (hrate : (T:ℝ)*(m:ℝ) ≤ 2*(Fintype.card (C × (Fin m × Fin (t*m))):ℝ))
    (hscale : Real.exp 1*(t:ℝ)*(2*Real.exp 1/(k:ℝ))^k ≤ 1/256) :
    eventProbability (badBlockDensity (C := C) m (t*m) T k) ≤
      (Fintype.card C:ℝ)*m*(t*m)/(m:ℝ)^8 := by
  apply (witness_union_bound _ _).trans
  have hh := sum_le_sum (fun p (_ : p ∈ (univ : Finset (C × (Fin m × Fin (t*m))))) =>
    sizeDensityEvent_probability m t T k p.1 (p.2.1.val+1) (p.2.2.val+1)
      hm ht (by omega) (by omega) (by omega) (by omega) hk hrate hscale)
  convert hh using 1 <;> simp only [sum_const, card_univ, Fintype.card_prod,
    Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul] <;> ring

theorem not_badBlockDensity (m r T k : ℕ) (ω : Fin T → C × (Fin m × Fin r))
    (hω : ω ∉ badBlockDensity m r T k) :
    ∀ c A B, A.Nonempty → B.Nonempty → hitCount (blockAllowed c A B) ω ≤ k*(A.card+B.card) := by
  classical
  intro c A B hA hB
  by_contra h
  have ha : A.card-1 < m := by have hh := card_le_univ A; have hp := hA.card_pos; simp only [Fintype.card_fin] at hh; omega
  have hb : B.card-1 < r := by have hh := card_le_univ B; have hp := hB.card_pos; simp only [Fintype.card_fin] at hh; omega
  apply hω
  apply mem_biUnion.mpr
  refine ⟨(c,⟨A.card-1,ha⟩,⟨B.card-1,hb⟩),mem_univ _,?_⟩
  apply mem_biUnion.mpr
  refine ⟨(A,B),mem_product.mpr ⟨mem_powersetCard.mpr ⟨subset_univ _,by change A.card = A.card-1+1; have := hA.card_pos; omega⟩,
    mem_powersetCard.mpr ⟨subset_univ _,by change B.card = B.card-1+1; have := hB.card_pos; omega⟩⟩,?_⟩
  apply mem_filter.mpr
  refine ⟨mem_univ _,?_⟩
  have hsum : (A.card-1+1)+(B.card-1+1) = A.card+B.card := by have := hA.card_pos; have := hB.card_pos; omega
  change k*((A.card-1+1)+(B.card-1+1)) ≤ hitCount (blockAllowed c A B) ω
  rw [hsum]
  omega

end GraphChoices.LowerBound
