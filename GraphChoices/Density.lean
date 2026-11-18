import GraphChoices.CapacityMatching
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Real.Archimedean

/-! Exact integer density characterization of the offline optimum, Section 2.2.
The upper bound is proved by capacitated Hall, rather than assumed. -/
namespace GraphChoices
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V] {T : ℕ}

/-- An orientation of capacity c exists iff all induced subgraphs have at most
c times as many edge occurrences as vertices. This includes multiplicities. -/
 theorem exists_orientation_iff_density (I : Instance V T) (c : ℕ) :
    (∃ a : Orientation T, maxLoad I a ≤ c) ↔
      ∀ S : Finset V, internalCount I S ≤ S.card * c := by
  constructor
  · rintro ⟨a, ha⟩ S
    exact (density_obstruction I a S).trans (Nat.mul_le_mul_left _ ha)
  · intro hdensity
    let r (t : Fin T) (v : V) := v = I.left t ∨ v = I.right t
    have hexpand (A : Finset (Fin T)) : A.card ≤ c * (neighbors r A).card := by
      have hsub : A ⊆ univ.filter (fun t => I.left t ∈ neighbors r A ∧ I.right t ∈ neighbors r A) := by
        intro t ht
        simp only [mem_filter, mem_univ, true_and, neighbors]
        exact ⟨⟨t, ht, Or.inl rfl⟩, ⟨t, ht, Or.inr rfl⟩⟩
      exact (card_le_card hsub).trans (by simpa [mul_comm] using hdensity (neighbors r A))
    obtain ⟨f, hf, hcap⟩ := exists_capacity_matching r c hexpand
    let a : Orientation T := fun t => decide (f t = I.left t)
    have hdest (t : Fin T) : destination I a t = f t := by
      by_cases h : f t = I.left t
      · simp [destination, a, h]
      · have hr : f t = I.right t := (hf t).resolve_left h
        simp only [destination, a, decide_eq_true_eq, if_neg h]
        exact hr.symm
    refine ⟨a, (maxLoad_le_iff I a c).2 ?_⟩
    intro v
    simpa only [load, hdest] using hcap v

 theorem opt_le_iff_density (I : Instance V T) (c : ℕ) :
    opt I ≤ c ↔ ∀ S : Finset V, internalCount I S ≤ S.card * c := by
  constructor
  · intro hc S
    exact (density_le_opt I S).trans (Nat.mul_le_mul_left _ hc)
  · intro h
    obtain ⟨a, ha⟩ := (exists_orientation_iff_density I c).2 h
    exact (opt_le_maxLoad I a).trans ha

noncomputable def density (I : Instance V T) (S : Finset V) : ℝ :=
  internalCount I S / (S.card : ℝ)

noncomputable def maxDensity (I : Instance V T) : ℝ :=
  (univ.powerset).sup' (by simp) (density I)

omit [Fintype V] in
 theorem density_nonneg (I : Instance V T) (S : Finset V) : 0 ≤ density I S := by
  exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

omit [Fintype V] in
 theorem density_le_nat_iff (I : Instance V T) (S : Finset V) (c : ℕ) :
    density I S ≤ c ↔ internalCount I S ≤ S.card * c := by
  by_cases hS : S.card = 0
  · have hs : S = ∅ := card_eq_zero.mp hS
    simp [hs, density, internalCount]
  · have hp : (0:ℝ) < S.card := by exact_mod_cast Nat.pos_of_ne_zero hS
    rw [density, div_le_iff₀ hp]
    norm_cast
    rw [mul_comm]

 theorem maxDensity_le_nat_iff (I : Instance V T) (c : ℕ) :
    maxDensity I ≤ c ↔ ∀ S : Finset V, internalCount I S ≤ S.card * c := by
  simp only [maxDensity, sup'_le_iff, mem_powerset, subset_univ, forall_true_left,
    density_le_nat_iff]

 theorem maxDensity_nonneg (I : Instance V T) : 0 ≤ maxDensity I := by
  exact (density_nonneg I ∅).trans (le_sup' (density I) (by simp))

/-- The ceiling in the paper's exact density identity is retained. -/
 theorem opt_eq_ceil_maxDensity (I : Instance V T) : opt I = ⌈maxDensity I⌉₊ := by
  apply Nat.le_antisymm
  · apply (opt_le_iff_density I _).2
    apply (maxDensity_le_nat_iff I _).1
    exact Nat.le_ceil _
  · apply Nat.ceil_le.mpr
    exact (maxDensity_le_nat_iff I _).2 (density_le_opt I)

end GraphChoices
