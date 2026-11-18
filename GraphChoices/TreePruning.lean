import GraphChoices.ComponentTrees
import Mathlib.Combinatorics.SimpleGraph.Bipartite

/-! The deterministic right-leaf pruning reduction in Claim 4.3. Colors are
Boolean, with true for left vertices. The retained graph contains all left
vertices and all right vertices of degree at least two. -/
namespace GraphChoices
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

theorem path_internal_degree {u v : V} (p : G.Walk u v) (hp : p.IsPath)
    (w : V) (hw : w ∈ p.support) (hwu : w ≠ u) (hwv : w ≠ v) :
    2 ≤ G.degree w := by
  induction p generalizing w with
  | nil => simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hw; exact (hwu hw).elim
  | @cons u x v h p ih =>
    have hps := (SimpleGraph.Walk.cons_isPath_iff h p).mp hp
    simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hw
    rcases hw with hw | hw
    · exact (hwu hw).elim
    by_cases hx : w = x
    · subst w
      cases p with
      | nil => exact (hwv rfl).elim
      | @cons x y v hxy q =>
        have huy : u ≠ y := by
          intro heq
          apply hps.2
          simp [heq]
        have hpair : ({u,y} : Finset V) ⊆ G.neighborFinset x := by
          intro z hz
          rcases mem_insert.mp hz with rfl | hz
          · exact (G.mem_neighborFinset _ _).mpr h.symm
          · have hz' := mem_singleton.mp hz
            subst z
            exact (G.mem_neighborFinset _ _).mpr hxy
        have hc := card_le_card hpair
        simpa only [card_pair huy, SimpleGraph.card_neighborFinset_eq_degree] using hc
    · exact ih hps.1 w hw hx hwv

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem reachable_induce_of_walk {s : Set V} {u v : V} (p : G.Walk u v)
    (hu : u ∈ s) (hv : v ∈ s) (hs : ∀ w ∈ p.support, w ∈ s) :
    (G.induce s).Reachable ⟨u,hu⟩ ⟨v,hv⟩ := by
  induction p with
  | nil => exact SimpleGraph.Reachable.rfl
  | @cons u w v h p ih =>
    have hw : w ∈ s := hs w (by simp)
    have hp : ∀ z ∈ p.support, z ∈ s := fun z hz => hs z (by simp [hz])
    exact (SimpleGraph.Adj.reachable (show (G.induce s).Adj ⟨u,hu⟩ ⟨w,hw⟩ from h)).trans
      (ih hw hv hp)

def prunedVertices (left : V → Bool) : Set V :=
  {v | left v = true ∨ 2 ≤ G.degree v}

instance decidablePrunedVertices (left : V → Bool) :
    DecidablePred (fun v => v ∈ prunedVertices G left) :=
  fun v => inferInstanceAs (Decidable (left v = true ∨ 2 ≤ G.degree v))

theorem pruned_induce_connected (left : V → Bool) (hc : G.Connected)
    (root : V) (hroot : left root = true) :
    (G.induce (prunedVertices G left)).Connected := by
  apply (SimpleGraph.connected_iff_exists_forall_reachable _).mpr
  refine ⟨⟨root, Or.inl hroot⟩, ?_⟩
  intro v
  obtain ⟨p, hp⟩ := (hc root v.val).exists_isPath
  apply reachable_induce_of_walk G p (Or.inl hroot) v.property
  intro w hw
  by_cases hwu : w = root
  · subst w; exact Or.inl hroot
  by_cases hwv : w = v.val
  · subst w; exact v.property
  exact Or.inr (path_internal_degree G p hp w hw hwu hwv)

theorem pruned_induce_isTree (left : V → Bool) (ht : G.IsTree)
    (root : V) (hroot : left root = true) :
    (G.induce (prunedVertices G left)).IsTree :=
  ⟨pruned_induce_connected G left ht.isConnected root hroot,
    ht.IsAcyclic.induce _⟩

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem bool_bipartite (left : V → Bool)
    (hcolor : ∀ x y, G.Adj x y → left x ≠ left y) :
    G.IsBipartiteWith {v | left v = true} {v | left v = false} := by
  constructor
  · simp [Set.disjoint_left]
  · intro x y hxy
    have h := hcolor x y hxy
    cases hx : left x <;> cases hy : left y <;> simp_all

omit [DecidableEq V] in
theorem bool_partition_card (left : V → Bool) :
    (univ.filter fun v => left v = true).card +
      (univ.filter fun v => left v = false).card = Fintype.card V := by
  simpa using filter_card_add_filter_neg_card_eq_card (s := (univ : Finset V)) (fun v => left v = true)

omit [DecidableEq V] in
theorem right_degree_preserved_by_pruning (left : V → Bool)
    (hcolor : ∀ x y, G.Adj x y → left x ≠ left y)
    (v : prunedVertices G left) (hv : left v.val = false) :
    (G.induce (prunedVertices G left)).degree v = G.degree v.val := by
  apply SimpleGraph.degree_induce_of_neighborSet_subset
  intro w hw
  apply Or.inl
  have h := hcolor v.val w hw
  cases hh : left w <;> simp_all

omit [DecidableEq V] in
/-- A tree without right leaves has strictly more left vertices than right
vertices. This is the degree-sum argument with the exact tree edge count. -/
theorem tree_left_heavy_of_right_min_degree (left : V → Bool) (ht : G.IsTree)
    (hcolor : ∀ x y, G.Adj x y → left x ≠ left y)
    (hdeg : ∀ v, left v = false → 2 ≤ G.degree v) :
    (univ.filter fun v => left v = false).card + 1 ≤
      (univ.filter fun v => left v = true).card := by
  classical
  have hbi : G.IsBipartiteWith
      (↑(univ.filter fun v => left v = true)) (↑(univ.filter fun v => left v = false)) := by
    simpa using bool_bipartite G left hcolor
  have hsum := SimpleGraph.isBipartiteWith_sum_degrees_eq_card_edges' hbi
  have hbound : 2 * (univ.filter fun v => left v = false).card ≤ G.edgeFinset.card := by
    calc
      _ = ∑ v ∈ univ.filter (fun v => left v = false), 2 := by simp [mul_comm]
      _ ≤ ∑ v ∈ univ.filter (fun v => left v = false), G.degree v := by
        apply sum_le_sum
        intro v hv
        exact hdeg v (mem_filter.mp hv).2
      _ = _ := hsum
  have hc := ht.card_edgeFinset
  have hp := bool_partition_card left
  omega

theorem pruned_tree_left_heavy (left : V → Bool) (ht : G.IsTree)
    (hcolor : ∀ x y, G.Adj x y → left x ≠ left y)
    (root : V) (hroot : left root = true) :
    let U := prunedVertices G left
    (univ.filter fun v : U => left v.val = false).card + 1 ≤
      (univ.filter fun v : U => left v.val = true).card := by
  apply tree_left_heavy_of_right_min_degree (G.induce (prunedVertices G left))
    (fun v => left v.val) (pruned_induce_isTree G left ht root hroot)
  · intro x y hxy
    exact hcolor x.val y.val hxy
  · intro v hv
    rw [right_degree_preserved_by_pruning G left hcolor v hv]
    rcases v.property with hleft | hdeg
    · simp [hv] at hleft
    · exact hdeg

omit [DecidableEq V] in
theorem left_card_le_pruned_card (left : V → Bool) :
    (univ.filter fun v => left v = true).card ≤ Fintype.card (prunedVertices G left) := by
  rw [Fintype.card_subtype]
  apply card_le_card
  intro v hv
  exact mem_filter.mpr ⟨mem_univ _, Or.inl (mem_filter.mp hv).2⟩

/-- Deleting right leaves loses at most a factor D+1 in tree size, when all
left degrees are at most D. This also covers a singleton left tree. -/
theorem pruning_size_bound (left : V → Bool) (hc : G.Connected)
    (hcolor : ∀ x y, G.Adj x y → left x ≠ left y)
    (root : V) (hroot : left root = true) (D : ℕ)
    (hD : ∀ v, left v = true → G.degree v ≤ D) :
    Fintype.card V ≤ (D+1) * Fintype.card (prunedVertices G left) := by
  classical
  have hbi : G.IsBipartiteWith
      (↑(univ.filter fun v => left v = true)) (↑(univ.filter fun v => left v = false)) := by
    simpa using bool_bipartite G left hcolor
  have hright : (univ.filter fun v => left v = false).card ≤ G.edgeFinset.card := by
    calc
      _ = ∑ v ∈ univ.filter (fun v => left v = false), 1 := by simp
      _ ≤ ∑ v ∈ univ.filter (fun v => left v = false), G.degree v := by
        apply sum_le_sum
        intro v hv
        have hvfalse := (mem_filter.mp hv).2
        have hne : v ≠ root := by intro heq; subst v; simp [hroot] at hvfalse
        letI : Nontrivial V := ⟨⟨v, root, hne⟩⟩
        exact hc.preconnected.degree_pos_of_nontrivial v
      _ = _ := SimpleGraph.isBipartiteWith_sum_degrees_eq_card_edges' hbi
  have hleft : G.edgeFinset.card ≤ D * (univ.filter fun v => left v = true).card := by
    calc
      _ = ∑ v ∈ univ.filter (fun v => left v = true), G.degree v :=
        (SimpleGraph.isBipartiteWith_sum_degrees_eq_card_edges hbi).symm
      _ ≤ ∑ v ∈ univ.filter (fun v => left v = true), D := by
        apply sum_le_sum
        intro v hv
        exact hD v (mem_filter.mp hv).2
      _ = _ := by simp [mul_comm]
  have hpart := bool_partition_card left
  calc
    Fintype.card V ≤ (D+1)*(univ.filter fun v => left v = true).card := by nlinarith
    _ ≤ _ := Nat.mul_le_mul_left _ (left_card_le_pruned_card G left)

/-- Deterministic large-component reduction: any connected bipartite graph
with left degrees at most D contains a left-heavy tree with at least a
1/(D+1) fraction of its vertices. All original left vertices are retained. -/
theorem exists_large_left_heavy_tree (left : V → Bool) (hc : G.Connected)
    (hcolor : ∀ x y, G.Adj x y → left x ≠ left y)
    (root : V) (hroot : left root = true) (D : ℕ)
    (hD : ∀ v, left v = true → G.degree v ≤ D) :
    ∃ s : Set V, ∃ H : SimpleGraph s,
      H.IsTree ∧ H ≤ G.induce s ∧
      (∀ v, left v = true → v ∈ s) ∧
      Fintype.card V ≤ (D+1) * Nat.card s ∧
      Nat.card {v : s // left v.val = false} + 1 ≤ Nat.card {v : s // left v.val = true} := by
  classical
  obtain ⟨F, hFG, htree⟩ := hc.exists_isTree_le
  let s := prunedVertices F left
  refine ⟨s, F.induce s, pruned_induce_isTree F left htree root hroot, ?_, ?_, ?_, ?_⟩
  · intro x y hxy
    exact hFG hxy
  · intro v hv
    exact Or.inl hv
  · have hFD : ∀ v, left v = true → F.degree v ≤ D := by
      intro v hv
      exact (F.degree_le_of_le hFG).trans (hD v hv)
    simpa only [Nat.card_eq_fintype_card] using
      pruning_size_bound F left htree.isConnected (fun x y h => hcolor x y (hFG h)) root hroot D hFD
  · simpa only [Nat.card_eq_fintype_card, Fintype.card_subtype] using
      pruned_tree_left_heavy F left htree (fun x y h => hcolor x y (hFG h)) root hroot

end GraphChoices
