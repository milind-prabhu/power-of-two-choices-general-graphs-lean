import GraphChoices.Model
import Mathlib.Data.Fintype.Sum

/-! Samplewise orientation and optimum comparisons for the vertex-copy
construction in Lemma 2.4. The comparisons hold for every reference orientation,
not just a density-minimizing one. -/
namespace GraphChoices
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V] {T : ℕ}

def flip (a : Orientation T) : Orientation T := fun t => !(a t)

def splitInstance (I : Instance V T) (b : Orientation T) : Instance (V ⊕ V) T where
  left t := Sum.inl (destination I b t)
  right t := Sum.inr (destination I (flip b) t)

/-- Orientations on the copied graph and original graph are in bijection. -/
def transport (b a : Orientation T) : Orientation T := fun t =>
  if b t then a t else !(a t)

 theorem transport_involutive (b a : Orientation T) : transport b (transport b a) = a := by
  funext t
  simp only [transport]
  cases b t <;> cases a t <;> rfl

omit [Fintype V] [DecidableEq V] in
 theorem collapse_destination (I : Instance V T) (b a : Orientation T) (t : Fin T) :
    Sum.elim id id (destination (splitInstance I b) a t) = destination I (transport b a) t := by
  cases hb : b t <;> cases ha : a t <;>
    simp [destination, splitInstance, transport, flip, hb, ha]

omit [Fintype V] in
 theorem collapse_load (I : Instance V T) (b a : Orientation T) (v : V) :
    load I (transport b a) v =
      load (splitInstance I b) a (Sum.inl v) + load (splitInstance I b) a (Sum.inr v) := by
  simp only [load, card_eq_sum_ones, sum_filter, ← sum_add_distrib]
  apply sum_congr rfl
  intro t _
  rw [← collapse_destination]
  cases h : destination (splitInstance I b) a t with
  | inl x => simp
  | inr x => simp

 theorem split_maxLoad_le (I : Instance V T) (b a : Orientation T) :
    maxLoad (splitInstance I b) a ≤ maxLoad I (transport b a) := by
  apply (maxLoad_le_iff _ _ _).2
  intro w
  cases w with
  | inl v =>
    have h := collapse_load I b a v
    have hmax := load_le_maxLoad I (transport b a) v
    omega
  | inr v =>
    have h := collapse_load I b a v
    have hmax := load_le_maxLoad I (transport b a) v
    omega

 theorem collapse_maxLoad_le (I : Instance V T) (b a : Orientation T) :
    maxLoad I (transport b a) ≤ 2 * maxLoad (splitInstance I b) a := by
  apply (maxLoad_le_iff _ _ _).2
  intro v
  rw [collapse_load]
  have hl := load_le_maxLoad (splitInstance I b) a (Sum.inl v)
  have hr := load_le_maxLoad (splitInstance I b) a (Sum.inr v)
  omega

 theorem split_opt_le (I : Instance V T) (b : Orientation T) :
    opt (splitInstance I b) ≤ opt I := by
  obtain ⟨a, ha⟩ := exists_exact_opt I
  calc
    _ ≤ maxLoad (splitInstance I b) (transport b a) := opt_le_maxLoad _ _
    _ ≤ maxLoad I (transport b (transport b a)) := split_maxLoad_le _ _ _
    _ = opt I := by rw [transport_involutive, ha]

 theorem opt_le_two_split_opt (I : Instance V T) (b : Orientation T) :
    opt I ≤ 2 * opt (splitInstance I b) := by
  obtain ⟨a, ha⟩ := exists_exact_opt (splitInstance I b)
  calc
    _ ≤ maxLoad I (transport b a) := opt_le_maxLoad _ _
    _ ≤ 2 * maxLoad (splitInstance I b) a := collapse_maxLoad_le _ _ _
    _ = _ := by rw [ha]

/-- Pointwise competitive transfer; expectation preserves these inequalities. -/
 theorem competitive_transfer (I : Instance V T) (b a : Orientation T) (c : ℕ)
    (hc : maxLoad (splitInstance I b) a ≤ c * opt (splitInstance I b)) :
    maxLoad I (transport b a) ≤ (2*c) * opt I := by
  calc
    _ ≤ 2 * maxLoad (splitInstance I b) a := collapse_maxLoad_le _ _ _
    _ ≤ 2 * (c * opt (splitInstance I b)) := Nat.mul_le_mul_left _ hc
    _ ≤ 2 * (c * opt I) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left c (split_opt_le I b))
    _ = _ := by ring

end GraphChoices
