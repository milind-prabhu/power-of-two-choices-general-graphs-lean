import GraphChoices.ComponentExpectation
import GraphChoices.SamplingTail

/-! The degree condition used in the right-leaf pruning reduction: deleting
threshold occurrences cannot increase any sampled left neighborhood. Its
probability tail follows in the same i.i.d. space as the pattern bounds. -/
namespace GraphChoices.ThresholdGreedy
open Finset
variable {E L R C : Type*} [Fintype E] [DecidableEq E] [Nonempty E]
  [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R] [DecidableEq C]

def listLeftNeighbors (es : List (Arrival L R C)) (u : L) : Finset R :=
  ((es.filter fun e => decide (e.left = u)).map Arrival.right).toFinset

omit [Fintype L] [Fintype R] [DecidableEq C] in
theorem listLeftNeighbors_card_le (es : List (Arrival L R C)) (u : L) :
    (listLeftNeighbors es u).card ≤ es.countP (fun e => decide (e.left = u)) := by
  exact (List.toFinset_card_le _).trans_eq (by simp [List.countP_eq_length_filter])

omit [Fintype L] [Fintype R] [DecidableEq C] in
theorem listLeftNeighbors_mono {xs ys : List (Arrival L R C)} (h : xs.Sublist ys) (u : L) :
    listLeftNeighbors xs u ⊆ listLeftNeighbors ys u := by
  intro v hv
  exact List.mem_toFinset.mpr (((h.filter _).map Arrival.right).subset (List.mem_toFinset.mp hv))

theorem residual_left_neighbors_subset (α : C → ℕ) (es : List (Arrival L R C)) (u : L) :
    listLeftNeighbors (residualArrivals (trace α es)) u ⊆ listLeftNeighbors es u :=
  listLeftNeighbors_mono (residual_sublist α es) u

def leftSourceBucket (encode : E → Arrival L R C) (u : L) : Finset E :=
  univ.filter fun e => (encode e).left = u

omit [Nonempty E] [Fintype L] [Fintype R] [DecidableEq R] [DecidableEq C] in
theorem sample_left_count_eq_hits (encode : E → Arrival L R C) {T : ℕ}
    (ω : Fin T → E) (u : L) :
    (sampleArrivals encode ω).countP (fun e => decide (e.left = u)) =
      hitCount (leftSourceBucket encode u) ω := by
  unfold sampleArrivals
  rw [countP_ofFn_eq_sum]
  simp only [hitCount, leftSourceBucket, card_eq_sum_ones, sum_filter,
    mem_filter, mem_univ, true_and, decide_eq_true_eq]

theorem residual_left_degree_le_hits (encode : E → Arrival L R C) (α : C → ℕ) {T : ℕ}
    (ω : Fin T → E) (u : L) :
    (listLeftNeighbors (residualArrivals (trace α (sampleArrivals encode ω))) u).card ≤
      hitCount (leftSourceBucket encode u) ω := by
  calc
    _ ≤ (listLeftNeighbors (sampleArrivals encode ω) u).card :=
      card_le_card (residual_left_neighbors_subset α _ u)
    _ ≤ _ := (listLeftNeighbors_card_le _ u).trans_eq (sample_left_count_eq_hits encode ω u)

/-- Left-degree tail for the actual residual graph, counting distinct neighbors. -/
theorem residual_left_degree_tail (encode : E → Arrival L R C) (α : C → ℕ)
    (T k : ℕ) (r : ℝ)
    (hmean : ∀ u, Real.exp 1*T*(((leftSourceBucket encode u).card : ℝ)/Fintype.card E)/k ≤ r) :
    eventProbability (univ.filter fun ω : Fin T → E => ∃ u,
      k ≤ (listLeftNeighbors (residualArrivals (trace α (sampleArrivals encode ω))) u).card) ≤
      Fintype.card L * r^k := by
  apply (eventProbability_mono (B := univ.filter fun ω : Fin T → E =>
    ∃ u, k ≤ hitCount (leftSourceBucket encode u) ω) ?_).trans
  · exact some_bucket_tail_bound (leftSourceBucket encode) T k r hmean
  · intro ω hω
    obtain ⟨u, hu⟩ := (mem_filter.mp hω).2
    exact mem_filter.mpr ⟨mem_univ _, u, hu.trans (residual_left_degree_le_hits encode α ω u)⟩

end GraphChoices.ThresholdGreedy
