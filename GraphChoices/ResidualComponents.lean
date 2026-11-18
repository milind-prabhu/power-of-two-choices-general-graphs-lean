import GraphChoices.ComponentGreedy
import GraphChoices.ResidualOptimum

/-! Component-local bounds for the actual Threshold-Greedy state. A bound on
all residual component sizes gives a deterministic bound on the full load,
including thresholds, against the full sample's offline optimum. -/
namespace GraphChoices.ThresholdGreedy
open Finset
variable {L R C : Type*} [Fintype L] [Fintype R]
  [DecidableEq L] [DecidableEq R] [DecidableEq C]

def residualVertexLoad (α : C → ℕ) (es : List (Arrival L R C)) : L ⊕ R → ℕ :=
  Sum.elim (run α es).greedyLeft (run α es).greedyRight

def residualInstance (α : C → ℕ) (es : List (Arrival L R C)) :=
  replayInstance (residualArrivals (trace α es))

theorem residual_vertex_load_eq (α : C → ℕ) (es : List (Arrival L R C)) (v : L ⊕ R) :
    residualVertexLoad α es v =
      load (residualInstance α es) (replayOrientation (residualArrivals (trace α es))) v := by
  have hr := residual_replay α es
  have hh := congrArg (fun s : GreedyLoads L R => greedyVertexLoad s v) hr
  exact hh.trans (replay_final_load _ v)

theorem residual_vertex_load_le_length (α : C → ℕ) (es : List (Arrival L R C)) (v : L ⊕ R) :
    residualVertexLoad α es v ≤ es.length := by
  rw [residual_vertex_load_eq]
  exact (load_le_length _ _ _).trans (residual_sublist α es).length_le

/-- This bound also covers an empty residual sequence, without a positivity premise. -/
theorem residual_vertex_component_bound (α : C → ℕ) (es : List (Arrival L R C)) (v : L ⊕ R) :
    residualVertexLoad α es v ≤ 2 * opt (replayInstance es) *
      (Nat.log 2 (componentVertices (residualInstance α es) v).card + 1) := by
  rw [residual_vertex_load_eq]
  by_cases hres : 0 < (residualArrivals (trace α es)).length
  · apply (greedy_component_competitive _ _ (replay_isGreedy _) hres v).le.trans
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 (residual_opt_le_full α es))
  · have hz : (residualArrivals (trace α es)).length = 0 := by omega
    have hh := load_le_length (residualInstance α es)
      (replayOrientation (residualArrivals (trace α es))) v
    change _ ≤ (residualArrivals (trace α es)).length at hh
    exact (hh.trans hz.le).trans (Nat.zero_le _)

theorem residual_vertex_bound_of_small_components (α : C → ℕ) (es : List (Arrival L R C))
    (s : ℕ) (hsmall : ∀ v, (componentVertices (residualInstance α es) v).card ≤ s)
    (v : L ⊕ R) :
    residualVertexLoad α es v ≤ 2 * opt (replayInstance es) * (Nat.log 2 s + 1) := by
  apply (residual_vertex_component_bound α es v).trans
  exact Nat.mul_le_mul_left _ (Nat.add_le_add_right (Nat.log_mono_right (hsmall v)) 1)

def totalVertexLoad [Fintype C] (α : C → ℕ) (es : List (Arrival L R C)) : L ⊕ R → ℕ :=
  Sum.elim (fun u => (∑ c, (run α es).threshold u c) + (run α es).greedyLeft u)
    (run α es).greedyRight

def totalMaxLoad [Fintype C] (α : C → ℕ) (es : List (Arrival L R C)) : ℕ :=
  univ.sup (totalVertexLoad α es)

omit [Fintype L] [Fintype R] in
theorem total_vertex_le_threshold_add_residual [Fintype C] (α : C → ℕ)
    (es : List (Arrival L R C)) (v : L ⊕ R) :
    totalVertexLoad α es v ≤ (∑ c, α c) + residualVertexLoad α es v := by
  cases v with
  | inl u => exact Nat.add_le_add_right (threshold_budget α es u) _
  | inr v => exact Nat.le_add_left _ _

theorem totalMaxLoad_le_budget_add_length [Fintype C] (α : C → ℕ)
    (es : List (Arrival L R C)) : totalMaxLoad α es ≤ (∑ c, α c) + es.length := by
  apply Finset.sup_le
  intro v _
  exact (total_vertex_le_threshold_add_residual α es v).trans
    (Nat.add_le_add_left (residual_vertex_load_le_length α es v) _)

/-- The deterministic consequence of component shattering needed by Theorem 4.1. -/
theorem totalMaxLoad_of_small_components [Fintype C] (α : C → ℕ)
    (es : List (Arrival L R C)) (s : ℕ)
    (hsmall : ∀ v, (componentVertices (residualInstance α es) v).card ≤ s) :
    totalMaxLoad α es ≤ (∑ c, α c) + 2 * opt (replayInstance es) * (Nat.log 2 s + 1) := by
  apply Finset.sup_le
  intro v _
  exact (total_vertex_le_threshold_add_residual α es v).trans
    (Nat.add_le_add_left (residual_vertex_bound_of_small_components α es s hsmall v) _)

/-- For components of at most ell squared vertices, the Greedy multiplier is
at most 4(log_2 ell + 1), with exact integer constants. -/
theorem totalMaxLoad_of_square_components [Fintype C] (α : C → ℕ)
    (es : List (Arrival L R C)) (ell : ℕ)
    (hsmall : ∀ v, (componentVertices (residualInstance α es) v).card ≤ ell^2) :
    totalMaxLoad α es ≤ (∑ c, α c) + 4 * opt (replayInstance es) * (Nat.log 2 ell + 1) := by
  have hlog : Nat.log 2 (ell^2) + 1 ≤ 2*(Nat.log 2 ell + 1) := by
    by_cases hz : ell = 0
    · simp [hz]
    have hpow := Nat.lt_pow_succ_log_self (by decide : 1 < 2) ell
    have hsquare : ell^2 < 2^(2*(Nat.log 2 ell + 1)) := by
      calc
        ell^2 < (2^(Nat.log 2 ell+1))^2 := Nat.pow_lt_pow_left hpow (by decide)
        _ = _ := by rw [← pow_mul]; congr 1; omega
    have hh := Nat.log_lt_of_lt_pow (pow_ne_zero 2 hz) hsquare
    omega
  apply (totalMaxLoad_of_small_components α es (ell^2) hsmall).trans
  apply Nat.add_le_add_left
  calc
    _ ≤ 2 * opt (replayInstance es) * (2*(Nat.log 2 ell + 1)) := Nat.mul_le_mul_left _ hlog
    _ = _ := by ring

end GraphChoices.ThresholdGreedy
