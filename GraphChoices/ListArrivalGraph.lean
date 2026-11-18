import GraphChoices.ResidualDegree
import GraphChoices.TreePruning

/-! Agreement between the graph of a replay, distinct list neighborhoods, and
the bipartite side annotation needed by component pruning. Multiplicities are
forgotten only in graph adjacency; the original list keeps every occurrence. -/
namespace GraphChoices.ThresholdGreedy
open Finset
variable {L R C : Type*} [Fintype L] [Fintype R]
  [DecidableEq L] [DecidableEq R] [DecidableEq C]

def isLeft : L ⊕ R → Bool := Sum.elim (fun _ => true) (fun _ => false)

theorem mem_listLeftNeighbors (es : List (Arrival L R C)) (u : L) (v : R) :
    v ∈ listLeftNeighbors es u ↔ ∃ e ∈ es, e.left = u ∧ e.right = v := by
  simp only [listLeftNeighbors, List.mem_toFinset, List.mem_map, List.mem_filter,
    decide_eq_true_eq]
  constructor
  · rintro ⟨e, ⟨he, hl⟩, hr⟩
    exact ⟨e, he, hl, hr⟩
  · rintro ⟨e, he, hl, hr⟩
    exact ⟨e, ⟨he, hl⟩, hr⟩

theorem replay_adj_iff (es : List (Arrival L R C)) (x y : L ⊕ R) :
    (arrivalGraph (replayInstance es)).Adj x y ↔
      x ≠ y ∧ ∃ e ∈ es,
        (Sum.inl e.left = x ∧ Sum.inr e.right = y) ∨
        (Sum.inl e.left = y ∧ Sum.inr e.right = x) := by
  constructor
  · rintro ⟨hne, t, ht⟩
    exact ⟨hne, es.get t, List.get_mem _ _, ht⟩
  · rintro ⟨hne, e, he, hxy⟩
    obtain ⟨t, ht⟩ := List.mem_iff_get.mp he
    refine ⟨hne, t, ?_⟩
    simpa only [replayInstance, ht] using hxy

theorem replay_adj_sides (es : List (Arrival L R C)) (x y : L ⊕ R)
    (hxy : (arrivalGraph (replayInstance es)).Adj x y) : isLeft x ≠ isLeft y := by
  obtain ⟨_, e, _, h | h⟩ := (replay_adj_iff es x y).mp hxy
  · rcases h with ⟨rfl, rfl⟩
    simp [isLeft]
  · rcases h with ⟨rfl, rfl⟩
    simp [isLeft]

theorem replay_adj_inl_inr (es : List (Arrival L R C)) (u : L) (v : R) :
    (arrivalGraph (replayInstance es)).Adj (Sum.inl u) (Sum.inr v) ↔
      v ∈ listLeftNeighbors es u := by
  rw [replay_adj_iff, mem_listLeftNeighbors]
  simp

theorem replay_left_degree (es : List (Arrival L R C)) (u : L) :
    let G := arrivalGraph (replayInstance es)
    letI : DecidableRel G.Adj := Classical.decRel _
    G.degree (Sum.inl u) = (listLeftNeighbors es u).card := by
  classical
  dsimp only
  have heq : (arrivalGraph (replayInstance es)).neighborFinset (Sum.inl u) =
      (listLeftNeighbors es u).image Sum.inr := by
    ext w
    cases w with
    | inl a =>
      simp only [SimpleGraph.mem_neighborFinset, mem_image, Sum.inr_ne_inl, and_false, exists_false]
      constructor
      · intro h
        exact (replay_adj_sides es _ _ h) rfl
      · exact False.elim
    | inr v => simp [replay_adj_inl_inr]
  rw [← SimpleGraph.card_neighborFinset_eq_degree, heq, card_image_of_injective _ Sum.inr_injective]

end GraphChoices.ThresholdGreedy
