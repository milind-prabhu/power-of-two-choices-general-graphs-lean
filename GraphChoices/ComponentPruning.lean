import GraphChoices.ListArrivalGraph

/-! The pruning theorem applied to an actual replay component. Both graph
degrees and bipartite sides are proved to agree with the implementation's
list neighborhoods; no component-to-tree hypothesis is assumed. -/
namespace GraphChoices
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem connected_both_colors (G : SimpleGraph V) (left : V → Bool)
    (hc : G.Connected) (hcolor : ∀ x y, G.Adj x y → left x ≠ left y)
    (hcard : 1 < Fintype.card V) :
    (∃ v, left v = true) ∧ (∃ v, left v = false) := by
  haveI : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp hcard
  obtain ⟨u, v, hne⟩ := exists_pair_ne V
  obtain ⟨p⟩ := hc u v
  cases p with
  | nil => exact (hne rfl).elim
  | @cons u w v h p =>
    have hdiff := hcolor u w h
    cases hu : left u <;> cases hw : left w
    · exact (hdiff (hu.trans hw.symm)).elim
    · exact ⟨⟨w, hw⟩, ⟨u, hu⟩⟩
    · exact ⟨⟨u, hu⟩, ⟨w, hw⟩⟩
    · exact (hdiff (hu.trans hw.symm)).elim

theorem component_induce_degree {T : ℕ} (I : Instance V T) (v : V)
    (x : {w : V // w ∈ componentVertices I v}) :
    let G := arrivalGraph I
    letI : DecidableRel G.Adj := Classical.decRel _
    (G.induce (componentVertices I v : Set V)).degree x = G.degree x.val := by
  classical
  dsimp only
  simp only [← SimpleGraph.card_neighborSet_eq_degree]
  apply Fintype.card_congr
  refine {
    toFun := fun w => ⟨w.val.val, w.property⟩
    invFun := fun w => ⟨⟨w.val, ?_⟩, w.property⟩
    left_inv := fun w => rfl
    right_inv := fun w => rfl }
  exact (mem_componentVertices I v w.val).mpr
    (((mem_componentVertices I v x.val).mp x.property).trans w.property.reachable)

end GraphChoices

namespace GraphChoices.ThresholdGreedy
open Finset
variable {L R C : Type*} [Fintype L] [Fintype R]
  [DecidableEq L] [DecidableEq R] [DecidableEq C]

/-- Every nontrivial replay component has a large left-heavy tree with a
right root and edges in the actual residual graph. The subtree's vertex type
is a subset of the component, so its ambient vertex map is injective. -/
theorem replay_component_left_heavy_tree (es : List (Arrival L R C)) (v : L ⊕ R)
    (D : ℕ) (hD : ∀ u, (listLeftNeighbors es u).card ≤ D)
    (hlarge : 1 < (componentVertices (replayInstance es) v).card) :
    let U := {w : L ⊕ R // w ∈ componentVertices (replayInstance es) v}
    ∃ s : Set U, ∃ H : SimpleGraph s,
      H.IsTree ∧
      (∀ x y, H.Adj x y → (arrivalGraph (replayInstance es)).Adj x.val.val y.val.val) ∧
      (componentVertices (replayInstance es) v).card ≤ (D+1) * Nat.card s ∧
      Nat.card {x : s // isLeft x.val.val = false} + 1 ≤
        Nat.card {x : s // isLeft x.val.val = true} ∧
      (1 < Nat.card s → ∃ root : s, isLeft root.val.val = false) := by
  classical
  let U := {w : L ⊕ R // w ∈ componentVertices (replayInstance es) v}
  let G : SimpleGraph U := (arrivalGraph (replayInstance es)).induce
    (componentVertices (replayInstance es) v : Set (L ⊕ R))
  have hconn : G.Connected := component_induce_connected _ _
  have hcolor : ∀ x y, G.Adj x y → isLeft x.val ≠ isLeft y.val :=
    fun x y hxy => replay_adj_sides es x.val y.val hxy
  have hcard : 1 < Fintype.card U := by simpa only [U, Fintype.card_coe] using hlarge
  obtain ⟨root, hroot⟩ := (connected_both_colors G (fun x => isLeft x.val) hconn hcolor hcard).1
  have hdeg : ∀ x : U, isLeft x.val = true → G.degree x ≤ D := by
    intro x hx
    rw [component_induce_degree]
    cases heq : x.val with
    | inl u => rw [replay_left_degree]; exact hD u
    | inr w => simp [heq, isLeft] at hx
  obtain ⟨s, H, htree, hsub, _, hsize, hheavy⟩ :=
    exists_large_left_heavy_tree G (fun x => isLeft x.val) hconn hcolor root hroot D hdeg
  refine ⟨s, H, htree, ?_, ?_, hheavy, ?_⟩
  · intro x y hxy
    exact hsub hxy
  · simpa only [U, Fintype.card_coe] using hsize
  · intro hs
    have hcol : ∀ x y, H.Adj x y → isLeft x.val.val ≠ isLeft y.val.val :=
      fun x y hxy => hcolor x.val y.val (hsub hxy)
    have hcard' : 1 < Fintype.card s := by simpa only [Nat.card_eq_fintype_card] using hs
    exact (connected_both_colors H (fun x => isLeft x.val.val) htree.isConnected hcol hcard').2

end GraphChoices.ThresholdGreedy
