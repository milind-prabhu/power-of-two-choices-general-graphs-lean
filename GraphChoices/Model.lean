import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Pi
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Samplewise graph balancing (Definition 2.1)

An instance is an indexed sequence of pairs. Parallel occurrences are kept
separate. Loops are allowed in this general model, so all the lemmas also apply
to the loopless simple base graphs in the paper.
-/
namespace GraphChoices
open Finset

structure Instance (V : Type*) (T : ℕ) where
  left : Fin T → V
  right : Fin T → V

theorem Instance.ext {V : Type*} {T : ℕ} {I J : Instance V T}
    (hl : I.left = J.left) (hr : I.right = J.right) : I = J := by
  cases I
  cases J
  cases hl
  cases hr
  rfl

variable {V : Type*} [Fintype V] [DecidableEq V] {T : ℕ}

abbrev Orientation (T : ℕ) := Fin T → Bool

def destination (I : Instance V T) (a : Orientation T) (t : Fin T) : V :=
  if a t then I.left t else I.right t

def load (I : Instance V T) (a : Orientation T) (v : V) : ℕ :=
  (univ.filter fun t => destination I a t = v).card

def maxLoad (I : Instance V T) (a : Orientation T) : ℕ :=
  univ.sup (load I a)

def internalCount (I : Instance V T) (S : Finset V) : ℕ :=
  (univ.filter fun t => I.left t ∈ S ∧ I.right t ∈ S).card

def assignedCount (I : Instance V T) (a : Orientation T) (S : Finset V) : ℕ :=
  (univ.filter fun t => destination I a t ∈ S).card

omit [Fintype V] [DecidableEq V] in
 theorem destination_endpoint (I : Instance V T) (a : Orientation T) (t : Fin T) :
    destination I a t = I.left t ∨ destination I a t = I.right t := by
  simp only [destination]; split <;> simp_all

 theorem load_le_maxLoad (I : Instance V T) (a : Orientation T) (v : V) :
    load I a v ≤ maxLoad I a := by
  exact le_sup (f := load I a) (mem_univ v)

 theorem maxLoad_le_iff (I : Instance V T) (a : Orientation T) (c : ℕ) :
    maxLoad I a ≤ c ↔ ∀ v, load I a v ≤ c := by
  simp [maxLoad]

omit [Fintype V] in
 theorem load_le_length (I : Instance V T) (a : Orientation T) (v : V) :
    load I a v ≤ T := by
  simpa [load] using card_filter_le (univ : Finset (Fin T))
    (fun t => destination I a t = v)

 theorem maxLoad_le_length (I : Instance V T) (a : Orientation T) :
    maxLoad I a ≤ T :=
  (maxLoad_le_iff I a T).2 (load_le_length I a)

omit [Fintype V] in
 theorem assignedCount_eq_sum (I : Instance V T) (a : Orientation T) (S : Finset V) :
    assignedCount I a S = ∑ v ∈ S, load I a v := by
  classical
  simp only [assignedCount, load, card_eq_sum_ones, sum_filter]
  rw [sum_comm]
  apply sum_congr rfl
  intro t ht
  simp

 theorem total_load (I : Instance V T) (a : Orientation T) :
    ∑ v, load I a v = T := by
  rw [← assignedCount_eq_sum I a univ]
  simp [assignedCount]

omit [Fintype V] in
 theorem internalCount_le_assignedCount (I : Instance V T) (a : Orientation T)
    (S : Finset V) : internalCount I S ≤ assignedCount I a S := by
  apply card_le_card
  intro t ht
  simp only [mem_filter, mem_univ, true_and] at ht ⊢
  rcases destination_endpoint I a t with h | h <;> simp [h, ht.1, ht.2]

/-- The exact, ceiling-sensitive density obstruction used in Section 2.2. -/
 theorem density_obstruction (I : Instance V T) (a : Orientation T) (S : Finset V) :
    internalCount I S ≤ S.card * maxLoad I a := by
  calc
    internalCount I S ≤ assignedCount I a S := internalCount_le_assignedCount I a S
    _ = ∑ v ∈ S, load I a v := assignedCount_eq_sum I a S
    _ ≤ ∑ _v ∈ S, maxLoad I a := sum_le_sum fun v _ => load_le_maxLoad I a v
    _ = S.card * maxLoad I a := by simp

/-- Existence is constructive at the level of a finite search space. -/
def opt (I : Instance V T) : ℕ :=
  Nat.find (show ∃ c, ∃ a : Orientation T, maxLoad I a ≤ c from
    ⟨T, (fun _ => false), maxLoad_le_length I (fun _ => false)⟩)

 theorem exists_opt_orientation (I : Instance V T) :
    ∃ a : Orientation T, maxLoad I a ≤ opt I := by
  unfold opt
  exact Nat.find_spec (p := fun c => ∃ a : Orientation T, maxLoad I a ≤ c) _

 theorem opt_le_maxLoad (I : Instance V T) (a : Orientation T) :
    opt I ≤ maxLoad I a := Nat.find_min' _ ⟨a, le_rfl⟩

 theorem exists_exact_opt (I : Instance V T) :
    ∃ a : Orientation T, maxLoad I a = opt I := by
  obtain ⟨a, ha⟩ := exists_opt_orientation I
  exact ⟨a, Nat.le_antisymm ha (opt_le_maxLoad I a)⟩

 theorem opt_le_length (I : Instance V T) : opt I ≤ T :=
  (opt_le_maxLoad I (fun _ => false)).trans (maxLoad_le_length I _)

 theorem density_le_opt (I : Instance V T) (S : Finset V) :
    internalCount I S ≤ S.card * opt I := by
  obtain ⟨a, ha⟩ := exists_exact_opt I
  simpa [ha] using density_obstruction I a S

 theorem total_le_card_mul_opt (I : Instance V T) : T ≤ Fintype.card V * opt I := by
  simpa [internalCount] using density_le_opt I univ

 theorem opt_pos (I : Instance V T) (hT : 0 < T) : 0 < opt I := by
  have h := total_le_card_mul_opt I
  by_contra hn
  have : opt I = 0 := Nat.eq_zero_of_not_pos hn
  simp [this] at h
  omega

/-- Every occurrence of a fixed pair must be assigned to one of two vertices. -/
 theorem multiplicity_le_two_opt (I : Instance V T) (u v : V) :
    (univ.filter fun t => I.left t = u ∧ I.right t = v).card ≤ 2 * opt I := by
  calc
    _ ≤ internalCount I {u, v} := by
      apply card_le_card
      intro t ht
      simp only [mem_filter, mem_univ, true_and] at ht ⊢
      simp [ht.1, ht.2]
    _ ≤ ({u, v} : Finset V).card * opt I := density_le_opt I _
    _ ≤ 2 * opt I := Nat.mul_le_mul_right _ (card_insert_le _ _ |>.trans (by simp))

end GraphChoices
