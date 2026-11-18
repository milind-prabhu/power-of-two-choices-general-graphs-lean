import GraphChoices.ComponentPruning
import GraphChoices.ShapeCoverage
import GraphChoices.LargeShapeTail

/-! Actual large components force either a large left degree or a large
left-heavy subtree. The outstanding canonical-enumeration step is kept as an
explicit containment premise when combining this with canonical-shape tails.
-/
namespace GraphChoices
open Finset

theorem eventProbability_union_le {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (A B : Finset Ω) : eventProbability (A ∪ B) ≤ eventProbability A + eventProbability B := by
  unfold eventProbability
  rw [← add_div]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast card_union_le A B

end GraphChoices

namespace GraphChoices.ThresholdGreedy
open Finset
variable {E L R C : Type*} [Fintype E] [DecidableEq E] [Nonempty E]
  [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R] [DecidableEq C]

/-- A genuine geometric tree in an actual replay component. Its vertices are
a subset of that component, and every edge is an actual replay adjacency. -/
def HasLargeHeavyTree (es : List (Arrival L R C)) (k : ℕ) : Prop :=
  ∃ v : L ⊕ R,
  ∃ s : Set {w : L ⊕ R // w ∈ componentVertices (replayInstance es) v},
  ∃ H : SimpleGraph s,
    H.IsTree ∧
    (∀ x y, H.Adj x y → (arrivalGraph (replayInstance es)).Adj x.val.val y.val.val) ∧
    k+1 < Nat.card s ∧
    Nat.card {x : s // isLeft x.val.val = false} + 1 ≤
      Nat.card {x : s // isLeft x.val.val = true} ∧
    ∃ root : s, isLeft root.val.val = false

noncomputable def largeHeavyTreeEvent (encode : E → Arrival L R C) (α : C → ℕ)
    (T k : ℕ) : Finset (Fin T → E) := by
  classical
  exact univ.filter fun ω => HasLargeHeavyTree (residualArrivals (trace α (sampleArrivals encode ω))) k

noncomputable def largeLeftDegreeEvent (encode : E → Arrival L R C) (α : C → ℕ)
    (T D : ℕ) : Finset (Fin T → E) := by
  classical
  exact univ.filter fun ω => ∃ u,
    D < (listLeftNeighbors (residualArrivals (trace α (sampleArrivals encode ω))) u).card

/-- The deterministic reduction applied to actual random executions. There is
no assumed tree-extraction or side/degree agreement in this containment. -/
theorem largeComponent_subset_degree_or_tree (encode : E → Arrival L R C) (α : C → ℕ)
    (T D k : ℕ) :
    largeComponentEvent encode α T ((D+1)*(k+1)) ⊆
      largeLeftDegreeEvent encode α T D ∪ largeHeavyTreeEvent encode α T k := by
  classical
  intro ω hω
  by_cases hbad : ω ∈ largeLeftDegreeEvent encode α T D
  · exact mem_union_left _ hbad
  apply mem_union_right
  have hD : ∀ u, (listLeftNeighbors (residualArrivals (trace α (sampleArrivals encode ω))) u).card ≤ D := by
    simpa only [largeLeftDegreeEvent, mem_filter, mem_univ, true_and, not_exists, not_lt] using hbad
  obtain ⟨v, hv⟩ := (mem_filter.mp hω).2
  have hlarge : 1 < (componentVertices (residualInstance α (sampleArrivals encode ω)) v).card := by
    have hpos : 1 ≤ (D+1)*(k+1) := Nat.mul_pos (by omega) (by omega)
    omega
  obtain ⟨s, H, ht, hadj, hsize, hheavy, hroot⟩ :=
    replay_component_left_heavy_tree (residualArrivals (trace α (sampleArrivals encode ω))) v D hD hlarge
  have hs : k+1 < Nat.card s := by
    have hmult : (D+1)*(k+1) < (D+1)*Nat.card s := hv.trans_le hsize
    exact (Nat.mul_lt_mul_left (by omega : 0 < D+1)).mp hmult
  exact mem_filter.mpr ⟨mem_univ _, v, s, H, ht, hadj, hs, hheavy, hroot (by omega)⟩

theorem largeLeftDegree_probability_le (encode : E → Arrival L R C) (α : C → ℕ)
    (T D : ℕ) (r : ℝ)
    (hmean : ∀ u, Real.exp 1*T*(((leftSourceBucket encode u).card : ℝ)/Fintype.card E)/(D+1) ≤ r) :
    eventProbability (largeLeftDegreeEvent encode α T D) ≤ Fintype.card L * r^(D+1) := by
  have h := residual_left_degree_tail encode α T (D+1) r
    (by simpa only [Nat.cast_add, Nat.cast_one] using hmean)
  simpa only [largeLeftDegreeEvent, Nat.add_one_le_iff] using h

theorem largeComponent_probability_le_tree_tail (encode : E → Arrival L R C) (α : C → ℕ)
    (T D k : ℕ) (r ε : ℝ)
    (hmean : ∀ u, Real.exp 1*T*(((leftSourceBucket encode u).card : ℝ)/Fintype.card E)/(D+1) ≤ r)
    (htree : eventProbability (largeHeavyTreeEvent encode α T k) ≤ ε) :
    eventProbability (largeComponentEvent encode α T ((D+1)*(k+1))) ≤
      Fintype.card L * r^(D+1) + ε := by
  calc
    _ ≤ eventProbability (largeLeftDegreeEvent encode α T D ∪ largeHeavyTreeEvent encode α T k) :=
      eventProbability_mono (largeComponent_subset_degree_or_tree encode α T D k)
    _ ≤ eventProbability (largeLeftDegreeEvent encode α T D) +
        eventProbability (largeHeavyTreeEvent encode α T k) := eventProbability_union_le _ _
    _ ≤ _ := add_le_add (largeLeftDegree_probability_le encode α T D r hmean) htree

end GraphChoices.ThresholdGreedy

namespace GraphChoices.Patterns
open ThresholdGreedy
variable {E L R C : Type*} [Fintype E] [DecidableEq E] [Nonempty E]
  [Fintype L] [Fintype R] [Fintype C]
  [DecidableEq L] [DecidableEq R] [DecidableEq C]

/-- Conditional shattering assembly. `hcoverage` is the remaining deterministic
canonical-enumeration containment; it is not established by this theorem. -/
theorem largeComponent_tail_of_canonical_coverage (H : C → Peeling.Graph L R)
    (encode : E → Arrival L R C) (α : C → ℕ) (T D k B : ℕ) (r : ℝ)
    (hmean : ∀ u, Real.exp 1*T*(((leftSourceBucket encode u).card : ℝ)/Fintype.card E)/(D+1) ≤ r)
    (hcoverage : largeHeavyTreeEvent encode α T k ⊆ largeShapeEvent H encode α T k B)
    (hshape : ∀ j ≤ B, eventProbability (heavyShapeEvent H encode α T (k+j)) ≤
      (Fintype.card R : ℝ)/2^(k+j)) :
    eventProbability (largeComponentEvent encode α T ((D+1)*(k+1))) ≤
      Fintype.card L * r^(D+1) + 2*(Fintype.card R : ℝ)/2^k := by
  apply largeComponent_probability_le_tree_tail encode α T D k r _ hmean
  exact (eventProbability_mono hcoverage).trans (largeShape_probability_le H encode α T k B hshape)

end GraphChoices.Patterns
