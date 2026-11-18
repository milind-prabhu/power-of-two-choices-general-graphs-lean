import GraphChoices.PatternWitnessBound

/-! Deterministic encoding of disjoint tree and threshold occurrence times into
the finite witness family used by the proved joint probability bound. -/
namespace GraphChoices
open Finset
variable {E J : Type*} [Fintype E] [DecidableEq E] [Nonempty E]
  [Fintype J] [DecidableEq J] {T m : ℕ} {α : J → ℕ}

 theorem witnessTime_injective (w : TimeWitness J T m α)
    (htree : Function.Injective w.1)
    (hsep : ∀ i j, w.1 i ∉ (w.2 j).val)
    (hdisj : ∀ j j', j ≠ j' → Disjoint (w.2 j).val (w.2 j').val) :
    Function.Injective (witnessTime w) := by
  intro a b hab
  cases a with
  | inl i =>
    cases b with
    | inl i' => exact congrArg Sum.inl (htree hab)
    | inr p =>
      obtain ⟨j,k⟩ := p
      have hk := (w.2 j).val.orderEmbOfFin_mem ((mem_powersetCard.mp (w.2 j).property).2) k
      simp only [witnessTime] at hab
      exact False.elim (hsep i j (hab.symm ▸ hk))
  | inr p =>
    obtain ⟨j,k⟩ := p
    cases b with
    | inl i =>
      have hk := (w.2 j).val.orderEmbOfFin_mem ((mem_powersetCard.mp (w.2 j).property).2) k
      simp only [witnessTime] at hab
      exact False.elim (hsep i j (hab ▸ hk))
    | inr p' =>
      obtain ⟨j',k'⟩ := p'
      by_cases hj : j = j'
      · subst j'
        have hk : k = k' := ((w.2 j).val.orderEmbOfFin ((mem_powersetCard.mp (w.2 j).property).2)).injective hab
        subst k'
        rfl
      · have hk := (w.2 j).val.orderEmbOfFin_mem ((mem_powersetCard.mp (w.2 j).property).2) k
        have hk' := (w.2 j').val.orderEmbOfFin_mem ((mem_powersetCard.mp (w.2 j').property).2) k'
        simp only [witnessTime] at hab
        exact False.elim (Finset.disjoint_left.mp (hdisj j j' hj) hk (hab.symm ▸ hk'))

/-- Exhibiting actual, globally disjoint occurrence times is sufficient for
membership in the abstract pattern witness event. -/
 theorem mem_patternWitnessEvent_of_times (ω : Fin T → E) (tree : Fin m → E)
    (bucket : J → Finset E) (τ : Fin m → Fin T) (K : J → Finset (Fin T))
    (hcard : ∀ j, (K j).card = α j)
    (htree : Function.Injective τ) (hlabel : ∀ i, ω (τ i) = tree i)
    (hsep : ∀ i j, τ i ∉ K j)
    (hdisj : ∀ j j', j ≠ j' → Disjoint (K j) (K j'))
    (hbucket : ∀ j t, t ∈ K j → ω t ∈ bucket j) :
    ω ∈ patternWitnessEvent T m α tree bucket := by
  classical
  let w : TimeWitness J T m α := (τ, fun j => ⟨K j,mem_powersetCard.mpr ⟨subset_univ _,hcard j⟩⟩)
  have hinj : Function.Injective (witnessTime w) := witnessTime_injective w htree hsep hdisj
  unfold patternWitnessEvent
  apply mem_biUnion.mpr
  refine ⟨w,mem_univ _,?_⟩
  rw [if_pos hinj]
  simp only [requirementsEvent, mem_filter, mem_univ, true_and]
  intro s
  cases s with
  | inl i => simpa [slotAllowed, witnessTime, w] using hlabel i
  | inr p =>
    obtain ⟨j,k⟩ := p
    apply hbucket j
    exact (K j).orderEmbOfFin_mem (hcard j) k

end GraphChoices
