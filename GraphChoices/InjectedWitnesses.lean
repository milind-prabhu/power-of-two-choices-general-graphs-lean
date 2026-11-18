import GraphChoices.SamplingTail

/-! Exact probabilities for injectively assigned witness time steps. This is
the independence step in the pattern bound: every required occurrence must
have a distinct time, including repeated labels of the same base edge. -/
namespace GraphChoices
open Finset
variable {E J : Type*} [Fintype E] [DecidableEq E] [Nonempty E]
  [Fintype J] [DecidableEq J] {T : ℕ}

def requirementsEvent (τ : J → Fin T) (A : J → Finset E) : Finset (Fin T → E) :=
  univ.filter fun ω => ∀ j, ω (τ j) ∈ A j

noncomputable def constraintsAt (τ : J → Fin T) (A : J → Finset E) (t : Fin T) : Finset E := by
  classical
  exact if h : ∃ j, τ j = t then A (Classical.choose h) else univ

 theorem constraintsAt_selected (τ : J → Fin T) (A : J → Finset E)
    (hτ : Function.Injective τ) (j : J) : constraintsAt τ A (τ j) = A j := by
  classical
  unfold constraintsAt
  rw [dif_pos (show ∃ k, τ k = τ j from ⟨j,rfl⟩)]
  congr 1
  exact hτ (Classical.choose_spec (show ∃ k, τ k = τ j from ⟨j,rfl⟩))

 theorem requirementsEvent_eq_pi (τ : J → Fin T) (A : J → Finset E)
    (hτ : Function.Injective τ) :
    requirementsEvent τ A = Fintype.piFinset (constraintsAt τ A) := by
  classical
  ext ω
  simp only [requirementsEvent, mem_filter, mem_univ, true_and, Fintype.mem_piFinset]
  constructor
  · intro h t
    unfold constraintsAt
    split_ifs with ht
    · have hchoose := Classical.choose_spec ht
      simpa [hchoose] using h (Classical.choose ht)
    · exact mem_univ _
  · intro h j
    have ht := h (τ j)
    simpa [constraintsAt_selected τ A hτ j] using ht

/-- Injective assignment of all witness slots makes the probability a product
of the permitted fractions of base-edge labels. -/
 theorem requirements_probability (τ : J → Fin T) (A : J → Finset E)
    (hτ : Function.Injective τ) :
    eventProbability (requirementsEvent τ A) =
      ∏ j, ((A j).card : ℝ) / Fintype.card E := by
  classical
  rw [requirementsEvent_eq_pi τ A hτ, probability_coordinate_constraints]
  let S : Finset (Fin T) := univ.image τ
  have hm : (Fintype.card E : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  calc
    _ = ∏ t ∈ S, ((constraintsAt τ A t).card : ℝ) / Fintype.card E := by
      symm
      apply prod_subset (subset_univ _)
      intro t ht hnot
      have hnone : ¬∃ j, τ j = t := by
        rintro ⟨j,hj⟩
        exact hnot (mem_image.mpr ⟨j,mem_univ _,hj⟩)
      simp [constraintsAt, hnone, hm]
    _ = ∏ j, ((constraintsAt τ A (τ j)).card : ℝ) / Fintype.card E := by
      exact prod_image hτ.injOn
    _ = _ := by simp only [constraintsAt_selected τ A hτ]

/-- A finite family of injective time witnesses can be union-bounded without
assuming independence between the different witness events. -/
 theorem injected_witness_union_bound {W : Type*} [Fintype W] [DecidableEq W]
    (τ : W → J → Fin T) (A : J → Finset E) :
    eventProbability (univ.biUnion fun w : W =>
      if Function.Injective (τ w) then requirementsEvent (τ w) A else ∅) ≤
      Fintype.card W * (∏ j, ((A j).card : ℝ) / Fintype.card E) := by
  classical
  calc
    _ ≤ ∑ w : W, eventProbability
        (if Function.Injective (τ w) then requirementsEvent (τ w) A else ∅) := witness_union_bound _ _
    _ ≤ ∑ _w : W, ∏ j, ((A j).card : ℝ) / Fintype.card E := by
      apply sum_le_sum
      intro w _
      split_ifs with h
      · rw [requirements_probability _ _ h]
      · have hp : (0:ℝ) ≤ ∏ j : J, ((A j).card : ℝ) / Fintype.card E :=
          prod_nonneg (fun _ _ => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
        simpa [eventProbability] using hp
    _ = _ := by simp

end GraphChoices
