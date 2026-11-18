import GraphChoices.ReplayGreedyAdapter
import GraphChoices.Density
import Mathlib.Algebra.BigOperators.Fin

/-! Removing arrival occurrences cannot increase the offline optimum. This is
proved via the exact density criterion and applied to the extracted residual
sequence, completing the benchmark bridge for ordinary residual Greedy. -/
namespace GraphChoices
open Finset

 theorem countP_ofFn_eq_sum {A : Type*} {n : ℕ} (f : Fin n → A) (P : A → Bool) :
    (List.ofFn f).countP P = ∑ i, if P (f i) then 1 else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.ofFn_succ, List.countP_cons, ih, Fin.sum_univ_succ]
    simp only [Nat.add_comm]

 theorem card_filter_list_indices {A : Type*} (es : List A) (P : A → Bool) :
    (univ.filter fun i : Fin es.length => P (es.get i) = true).card = es.countP P := by
  have hh := countP_ofFn_eq_sum es.get P
  rw [List.ofFn_get] at hh
  simp only [card_eq_sum_ones, sum_filter]
  exact hh.symm

 theorem opt_le_of_internalCount_le {V : Type*} [Fintype V] [DecidableEq V]
    {S T : ℕ} (J : Instance V S) (I : Instance V T)
    (h : ∀ A, internalCount J A ≤ internalCount I A) : opt J ≤ opt I := by
  apply (opt_le_iff_density J _).2
  intro A
  exact (h A).trans (density_le_opt I A)

end GraphChoices

namespace GraphChoices.ThresholdGreedy
open Finset
variable {L R C : Type*} [Fintype L] [Fintype R]
  [DecidableEq L] [DecidableEq R] [DecidableEq C]

 theorem replay_internalCount (es : List (Arrival L R C)) (A : Finset (L ⊕ R)) :
    internalCount (replayInstance es) A =
      es.countP (fun e => decide (Sum.inl e.left ∈ A ∧ Sum.inr e.right ∈ A)) := by
  simpa only [internalCount, replayInstance, decide_eq_true_eq] using
    GraphChoices.card_filter_list_indices es
      (fun e => decide (Sum.inl e.left ∈ A ∧ Sum.inr e.right ∈ A))

 theorem replay_opt_mono_sublist (xs ys : List (Arrival L R C)) (h : xs.Sublist ys) :
    opt (replayInstance xs) ≤ opt (replayInstance ys) := by
  apply GraphChoices.opt_le_of_internalCount_le
  intro A
  rw [replay_internalCount, replay_internalCount]
  have hh := (h.filter (fun e => decide (Sum.inl e.left ∈ A ∧ Sum.inr e.right ∈ A))).length_le
  simpa only [List.countP_eq_length_filter] using hh

 theorem residual_sublist (α : C → ℕ) (es : List (Arrival L R C)) :
    (residualArrivals (trace α es)).Sublist es := by
  have hh := List.Sublist.map Event.arrival (List.filter_sublist
    (l := trace α es) (p := fun ev => !ev.threshold))
  simpa only [residualArrivals, trace, traceFrom_arrivals] using hh

 theorem residual_opt_le_full (α : C → ℕ) (es : List (Arrival L R C)) :
    opt (replayInstance (residualArrivals (trace α es))) ≤ opt (replayInstance es) :=
  replay_opt_mono_sublist _ _ (residual_sublist α es)

 theorem residual_left_competitive_full (α : C → ℕ) (es : List (Arrival L R C))
    (u : L) (hres : 0 < (residualArrivals (trace α es)).length) :
    (run α es).greedyLeft u <
      2 * opt (replayInstance es) * (Nat.log 2 (Fintype.card (L ⊕ R)) + 1) := by
  apply (residual_left_competitive α es u hres).trans_le
  exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 (residual_opt_le_full α es))

 theorem residual_right_competitive_full (α : C → ℕ) (es : List (Arrival L R C))
    (v : R) (hres : 0 < (residualArrivals (trace α es)).length) :
    (run α es).greedyRight v <
      2 * opt (replayInstance es) * (Nat.log 2 (Fintype.card (L ⊕ R)) + 1) := by
  apply (residual_right_competitive α es v hres).trans_le
  exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 (residual_opt_le_full α es))

end GraphChoices.ThresholdGreedy
