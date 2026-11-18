import GraphChoices.ResidualComponents
import GraphChoices.ResidualTreeBound

/-! Turn a tail for actual residual component sizes into an expected load
bound. Exceptional samples cost at most T times their probability. This
module does not assume or claim a proved component-shattering estimate. -/
namespace GraphChoices
open Finset

theorem average_add {Ω : Type*} [Fintype Ω] (f g : Ω → ℝ) :
    average (fun ω => f ω + g ω) = average f + average g := by
  simp only [average, sum_add_distrib, add_div]

theorem average_indicator {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (A : Finset Ω) (M : ℝ) :
    average (fun ω => if ω ∈ A then M else 0) = M * eventProbability A := by
  simp [average, eventProbability, mul_div_assoc, mul_comm]

/-- A finite expectation bound with an explicit additive exceptional-sample cost. -/
theorem average_le_good_add_bad {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (X B : Ω → ℝ) (A : Finset Ω) (M : ℝ)
    (hgood : ∀ ω, ω ∉ A → X ω ≤ B ω)
    (hbad : ∀ ω, ω ∈ A → X ω ≤ B ω + M) :
    average X ≤ average B + M * eventProbability A := by
  calc
    _ ≤ average (fun ω => B ω + if ω ∈ A then M else 0) := by
      apply average_mono
      intro ω
      split_ifs with h
      · exact hbad ω h
      · simpa using hgood ω h
    _ = _ := by rw [average_add, average_indicator]

end GraphChoices

namespace GraphChoices.ThresholdGreedy
open Finset
variable {E L R C : Type*} [Fintype E] [DecidableEq E] [Nonempty E]
  [Fintype L] [Fintype R] [Fintype C]
  [DecidableEq L] [DecidableEq R] [DecidableEq C]

/-- The actual large-component event, rather than a canonical pattern event. -/
noncomputable def largeComponentEvent (encode : E → Arrival L R C) (α : C → ℕ)
    (T s : ℕ) : Finset (Fin T → E) := by
  classical
  exact univ.filter fun ω => ∃ v,
    s < (componentVertices (residualInstance α (sampleArrivals encode ω)) v).card

omit [DecidableEq E] [Nonempty E] [Fintype C] in
theorem not_mem_largeComponentEvent (encode : E → Arrival L R C) (α : C → ℕ)
    (T s : ℕ) (ω : Fin T → E) :
    ω ∉ largeComponentEvent encode α T s ↔
      ∀ v, (componentVertices (residualInstance α (sampleArrivals encode ω)) v).card ≤ s := by
  classical
  simp [largeComponentEvent]

/-- Expected offline optimum of the full encoded arrival sequence. -/
noncomputable def expectedReplayOpt (encode : E → Arrival L R C) (T : ℕ) : ℝ :=
  average (fun ω : Fin T → E => (opt (replayInstance (sampleArrivals encode ω)) : ℝ))

noncomputable def expectedTotalMaxLoad (encode : E → Arrival L R C) (α : C → ℕ) (T : ℕ) : ℝ :=
  average (fun ω : Fin T → E => (totalMaxLoad α (sampleArrivals encode ω) : ℝ))

/-- The expectation step of Theorem 4.1. Its error is T times the probability
of an actual large residual component; that probability is not assumed small. -/
theorem expected_load_le_component_tail (encode : E → Arrival L R C) (α : C → ℕ)
    (T s : ℕ) :
    expectedTotalMaxLoad encode α T ≤ (∑ c, (α c : ℝ)) +
      (2 * (Nat.log 2 s + 1) : ℕ) * expectedReplayOpt encode T +
      T * eventProbability (largeComponentEvent encode α T s) := by
  let B : (Fin T → E) → ℝ := fun ω => (∑ c, (α c : ℝ)) +
    (2 * (Nat.log 2 s + 1) : ℕ) * (opt (replayInstance (sampleArrivals encode ω)) : ℝ)
  have hb : ∀ ω : Fin T → E, (∑ c, (α c : ℝ)) ≤ B ω := by
    intro ω
    dsimp [B]
    exact le_add_of_nonneg_right (by positivity)
  have h := average_le_good_add_bad
    (fun ω : Fin T → E => (totalMaxLoad α (sampleArrivals encode ω) : ℝ))
    B (largeComponentEvent encode α T s) (T : ℝ) ?_ ?_
  · change expectedTotalMaxLoad encode α T ≤ _ at h
    have heq : average B = (∑ c, (α c : ℝ)) +
        (2 * (Nat.log 2 s + 1) : ℕ) * expectedReplayOpt encode T := by
      dsimp only [B]
      rw [average_add, average_const, average_mul]
      rfl
    rwa [heq] at h
  · intro ω hω
    have hsmall := (not_mem_largeComponentEvent encode α T s ω).mp hω
    have hh := totalMaxLoad_of_small_components α (sampleArrivals encode ω) s hsmall
    have hh' : (totalMaxLoad α (sampleArrivals encode ω) : ℝ) ≤
        (∑ c, (α c : ℝ)) +
          (2 * opt (replayInstance (sampleArrivals encode ω)) * (Nat.log 2 s + 1) : ℕ) := by
      exact_mod_cast hh
    dsimp [B]
    convert hh' using 1 <;> push_cast <;> ring
  · intro ω _
    have hh := totalMaxLoad_le_budget_add_length α (sampleArrivals encode ω)
    rw [sampleArrivals_length] at hh
    have hh' : (totalMaxLoad α (sampleArrivals encode ω) : ℝ) ≤ (∑ c, (α c : ℝ)) + T := by
      exact_mod_cast hh
    exact hh'.trans (add_le_add_right (hb ω) _)

theorem expected_load_of_component_tail (encode : E → Arrival L R C) (α : C → ℕ)
    (T s : ℕ) (ε : ℝ)
    (htail : eventProbability (largeComponentEvent encode α T s) ≤ ε) :
    expectedTotalMaxLoad encode α T ≤ (∑ c, (α c : ℝ)) +
      (2 * (Nat.log 2 s + 1) : ℕ) * expectedReplayOpt encode T + T * ε := by
  apply (expected_load_le_component_tail encode α T s).trans
  exact add_le_add_left (mul_le_mul_of_nonneg_left htail (Nat.cast_nonneg T)) _

end GraphChoices.ThresholdGreedy
