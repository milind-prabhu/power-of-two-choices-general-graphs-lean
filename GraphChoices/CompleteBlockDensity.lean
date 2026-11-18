import GraphChoices.GreedyPropagationProbability

namespace GraphChoices.LowerBound
open Finset
variable {V C : Type*} [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C]
  {m r T : ℕ}

def blockBase (left : C × Fin m → V) (right : C × Fin r → V) : BaseGraph V (C × (Fin m × Fin r)) where
  left e := left (e.1,e.2.1)
  right e := right (e.1,e.2.2)

def blockAllowed (c : C) (A : Finset (Fin m)) (B : Finset (Fin r)) : Finset (C × (Fin m × Fin r)) :=
  {c} ×ˢ (A ×ˢ B)

theorem blockAllowed_card (c : C) (A : Finset (Fin m)) (B : Finset (Fin r)) :
    (blockAllowed c A B).card = A.card*B.card := by simp [blockAllowed]

def blockLeftSet (left : C × Fin m → V) (S : Finset V) (c : C) : Finset (Fin m) :=
  univ.filter fun a => left (c,a) ∈ S
def blockRightSet (right : C × Fin r → V) (S : Finset V) (c : C) : Finset (Fin r) :=
  univ.filter fun a => right (c,a) ∈ S

theorem sum_block_sets_le (f : C × Fin m → V) (hf : Function.Injective f) (S : Finset V) :
    (∑ c, (univ.filter fun a : Fin m => f (c,a) ∈ S).card) ≤ S.card := by
  have heq : (∑ c, (univ.filter fun a : Fin m => f (c,a) ∈ S).card) =
      (univ.filter fun p : C × Fin m => f p ∈ S).card := by
    simp only [card_eq_sum_ones, sum_filter, Fintype.sum_prod_type]
  rw [heq]
  apply card_le_card_of_injOn f
  · intro p hp
    exact (mem_filter.mp hp).2
  · exact fun _ _ _ _ h => hf h

theorem internalCount_block_sum (left : C × Fin m → V) (right : C × Fin r → V)
    (ω : Fin T → C × (Fin m × Fin r)) (S : Finset V) :
    internalCount ((blockBase left right).sample ω) S =
      ∑ c, hitCount (blockAllowed c (blockLeftSet left S c) (blockRightSet right S c)) ω := by
  have heq (c : C) : hitCount (blockAllowed c (blockLeftSet left S c) (blockRightSet right S c)) ω =
      ((univ.filter fun j => (blockBase left right).left (ω j) ∈ S ∧
        (blockBase left right).right (ω j) ∈ S).filter fun j => (ω j).1 = c).card := by
    unfold hitCount
    congr 1
    ext j
    simp only [blockAllowed, blockLeftSet, blockRightSet, hitCount, mem_filter,
      mem_univ, true_and, mem_product, mem_singleton, blockBase]
    constructor
    · rintro ⟨h,hl,hr⟩
      subst c
      exact ⟨⟨hl,hr⟩,rfl⟩
    · rintro ⟨⟨hl,hr⟩,h⟩
      subst c
      exact ⟨rfl,hl,hr⟩
  simp_rw [heq]
  exact card_eq_sum_card_fiberwise (fun _ _ => mem_univ _)

/-- Each vertex belongs to at most one left block and at most one right
block. Density bounds within every complete bipartite block therefore add. -/
theorem opt_le_of_block_density (left : C × Fin m → V) (right : C × Fin r → V)
    (hl : Function.Injective left) (hr : Function.Injective right)
    (ω : Fin T → C × (Fin m × Fin r)) (k : ℕ)
    (hblock : ∀ c A B, A.Nonempty → B.Nonempty →
      hitCount (blockAllowed c A B) ω ≤ k*(A.card+B.card)) :
    opt ((blockBase left right).sample ω) ≤ 2*k := by
  apply (opt_le_iff_density _ _).mpr
  intro S
  rw [internalCount_block_sum]
  have heach (c : C) :
      hitCount (blockAllowed c (blockLeftSet left S c) (blockRightSet right S c)) ω ≤
        k*((blockLeftSet left S c).card+(blockRightSet right S c).card) := by
    by_cases hA : (blockLeftSet left S c).Nonempty
    · by_cases hB : (blockRightSet right S c).Nonempty
      · exact hblock c _ _ hA hB
      · have hz := not_nonempty_iff_eq_empty.mp hB
        simp [blockAllowed, hz, hitCount]
    · have hz := not_nonempty_iff_eq_empty.mp hA
      simp [blockAllowed, hz, hitCount]
  have hh := sum_le_sum (fun c (_ : c ∈ (univ : Finset C)) => heach c)
  rw [← mul_sum, sum_add_distrib] at hh
  have hL := sum_block_sets_le left hl S
  have hR := sum_block_sets_le right hr S
  change (∑ c, (blockLeftSet left S c).card) ≤ S.card at hL
  change (∑ c, (blockRightSet right S c).card) ≤ S.card at hR
  nlinarith

end GraphChoices.LowerBound
