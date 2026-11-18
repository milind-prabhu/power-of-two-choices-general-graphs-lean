import GraphChoices.BlockDensity

/-! Uniform sampling is preserved by a prefix restriction; the offline
optimum is monotone when arrivals are added. -/
namespace GraphChoices
open Finset

def Instance.restrict {V : Type*} {M N : ℕ} (I : Instance V N) (f : Fin M ↪ Fin N) :
    Instance V M where
  left t := I.left (f t)
  right t := I.right (f t)

theorem opt_restrict_le {V : Type*} [Fintype V] [DecidableEq V] {M N : ℕ}
    (I : Instance V N) (f : Fin M ↪ Fin N) : opt (I.restrict f) ≤ opt I := by
  obtain ⟨a,ha⟩ := exists_exact_opt I
  apply (opt_le_maxLoad (I.restrict f) (fun t => a (f t))).trans
  rw [← ha]
  apply (maxLoad_le_iff _ _ _).mpr
  intro v
  apply le_trans _ (load_le_maxLoad I a v)
  apply card_le_card_of_injOn f
  · intro t ht
    change t ∈ univ.filter (fun t => destination (I.restrict f) (fun t => a (f t)) t = v) at ht
    change f t ∈ univ.filter (fun t => destination I a t = v)
    simpa only [mem_filter, mem_univ, true_and, destination, Instance.restrict] using ht
  · exact fun _ _ _ _ h => f.injective h

theorem average_product_fst {Ω Ω' : Type*} [Fintype Ω] [Fintype Ω'] [Nonempty Ω']
    (f : Ω → ℝ) : average (fun p : Ω × Ω' => f p.1) = average f := by
  simp only [average, Fintype.sum_prod_type, sum_const, card_univ, nsmul_eq_mul,
    ← mul_sum, Fintype.card_prod, Nat.cast_mul]
  have h : (Fintype.card Ω' : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  by_cases hΩ : Fintype.card Ω = 0
  · simp [hΩ]
  · have hΩ' : (Fintype.card Ω : ℝ) ≠ 0 := by exact_mod_cast hΩ
    field_simp

def appendSamples {E : Type*} (M Q : ℕ) :
    (Fin M → E) × (Fin Q → E) ≃ (Fin (M+Q) → E) :=
  (Equiv.sumArrowEquivProdArrow (Fin M) (Fin Q) E).symm.trans
    (Equiv.arrowCongr finSumFinEquiv (Equiv.refl E))

theorem appendSamples_left {E : Type*} (M Q : ℕ)
    (p : (Fin M → E) × (Fin Q → E)) (t : Fin M) :
    appendSamples M Q p (Fin.castAdd Q t) = p.1 t := by
  change appendSamples M Q p (finSumFinEquiv (Sum.inl t)) = p.1 t
  simp only [appendSamples, Equiv.trans_apply, Equiv.arrowCongr_apply, Function.comp_apply, Equiv.refl_apply, Equiv.symm_apply_apply]
  rcases p with ⟨p,q⟩
  rfl

theorem average_prefix {E : Type*} [Fintype E] [Nonempty E] (M Q : ℕ)
    (f : (Fin M → E) → ℝ) :
    average (fun ω : Fin (M+Q) → E => f (fun t => ω (Fin.castAdd Q t))) = average f := by
  rw [← average_equiv (appendSamples M Q)]
  simp_rw [appendSamples_left]
  exact average_product_fst f

theorem expectedOpt_mono_horizon {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [Nonempty E] (G : BaseGraph V E) {M N : ℕ} (hMN : M ≤ N) :
    expectedOpt G M ≤ expectedOpt G N := by
  obtain ⟨Q,rfl⟩ := Nat.exists_eq_add_of_le hMN
  unfold expectedOpt
  rw [← average_prefix M Q (fun ω => (opt (G.sample ω):ℝ))]
  apply average_mono
  intro ω
  have hh := opt_restrict_le (G.sample ω) ⟨Fin.castAdd Q, Fin.castAdd_injective M Q⟩
  exact_mod_cast hh

end GraphChoices
