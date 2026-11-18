import GraphChoices.ForestIndices

/-! A canonical geometric shape encoding for every finite connected graph,
with a prescribed right root and an exact bijection of vertex sets. -/
namespace GraphChoices.Patterns
open Finset
variable {V : Type*} [Fintype V]

theorem exists_canonical_embedding (G : SimpleGraph V) (hc : G.Connected)
    (color : V → Bool) (hcolor : ∀ u v, G.Adj u v → color u ≠ color v)
    (root : V) (hroot : color root = false) :
    ∃ m : ℕ, ∃ s : UnlabelledShape m, ∃ e : Fin (m+1) ≃ V,
      m+1 = Fintype.card V ∧ e ⟨0, by omega⟩ = root ∧
      ∀ i : Fin m, G.Adj (e (childIndex i)) (e (parentIndex (skeletonPattern s) i)) ∧
        color (e (childIndex i)) = (skeletonPattern s).childLeft i := by
  classical
  obtain ⟨t, ht, hn, hcover, hsize⟩ := exists_spanning_labelled_forest G hc root
  let xs := root :: forestLabels t
  have hlen : xs.length = t.numNodes+1 := by simp [xs, forestLabels_length]
  let F : ℕ → V := fun i => if hi : i < xs.length then xs[i] else root
  have hF (i : ℕ) (hi : i < xs.length) : F i = xs[i] := dif_pos hi
  have hF0 : F 0 = root := by simp [F, xs]
  have hbij : Function.Bijective (fun i : Fin (t.numNodes+1) => F i.val) := by
    constructor
    · intro i j hij
      change F i.val = F j.val at hij
      have hi : i.val < xs.length := by rw [hlen]; exact i.isLt
      have hj : j.val < xs.length := by rw [hlen]; exact j.isLt
      rw [hF i.val hi, hF j.val hj] at hij
      exact Fin.ext ((hn.getElem_inj_iff).mp hij)
    · intro v
      obtain ⟨i, hi⟩ := List.mem_iff_get.mp (hcover v)
      let j : Fin (t.numNodes+1) := ⟨i.val, by simpa only [List.length_cons, forestLabels_length] using i.isLt⟩
      refine ⟨j, ?_⟩
      change F j.val = v
      rw [hF j.val (by exact i.isLt)]
      exact hi
  let e : Fin (t.numNodes+1) ≃ V := Equiv.ofBijective _ hbij
  let s : UnlabelledShape t.numNodes :=
    ⟨eraseForest t, Tree.mem_treesOfNumNodesEq.mpr (eraseForest_numNodes t)⟩
  have hvalid : ForestValid G (F 0) t := by simpa only [hF0] using ht
  have hparent : color (F 0) = !true := by simpa only [hF0] using hroot
  have hvalues : ∀ i < t.numNodes, F (0+i+1) = forestValue t root i := by
    intro i hi
    rw [hF (0+i+1) (by rw [hlen]; omega)]
    simpa only [xs, Nat.zero_add, List.getElem_cons_succ] using (forestValue_eq_get t root i hi).symm
  have hspec := forest_index_spec G color hcolor t F root 0 0 true hvalid hparent hvalues
  refine ⟨t.numNodes, s, e, hsize, hF0, ?_⟩
  intro i
  have h := hspec i.val i.isLt
  have hpar : (parentIndex (skeletonPattern s) i).val = parentPos t 0 0 i.val := by
    change (forestParent (eraseForest t) 0 0 le_rfl _).val = _
    exact forestParent_eq_parentPos t 0 0 le_rfl _
  have hside : (skeletonPattern s).childLeft i = sidePos t true i.val := by
    change forestSide (eraseForest t) true _ = _
    exact forestSide_eq_sidePos t true _
  constructor
  · change G.Adj (F (i.val+1)) (F (parentIndex (skeletonPattern s) i).val)
    rw [hpar]
    simpa only [Nat.zero_add] using h.1
  · change color (F (i.val+1)) = _
    rw [hside]
    simpa only [Nat.zero_add] using h.2

/-- The right root contributes no left vertex, so the non-root left-index
count equals the number of left vertices of the encoded graph exactly. -/
theorem left_index_card (m : ℕ) (e : Fin (m+1) ≃ V) (color : V → Bool)
    (hroot : color (e ⟨0, by omega⟩) = false) :
    (univ.filter fun i : Fin m => color (e (childIndex i)) = true).card =
      Nat.card {v : V // color v = true} := by
  classical
  let A := {i : Fin m // i ∈ univ.filter (fun i => color (e (childIndex i)) = true)}
  let f : A → {v : V // color v = true} := fun i =>
    ⟨e (childIndex i.val), (mem_filter.mp i.property).2⟩
  have hf : Function.Bijective f := by
    constructor
    · intro i j hij
      have hidx := e.injective (congrArg Subtype.val hij)
      apply Subtype.ext
      apply Fin.ext
      have hval := congrArg Fin.val hidx
      simp only [childIndex] at hval
      omega
    · intro v
      let j := e.symm v.val
      have hj0 : j.val ≠ 0 := by
        intro hj
        have hj' : j = ⟨0, by omega⟩ := Fin.ext hj
        have he : e ⟨0, by omega⟩ = v.val := by rw [← hj']; exact e.apply_symm_apply _
        rw [he, v.property] at hroot
        contradiction
      let i : Fin m := ⟨j.val-1, by have := j.isLt; omega⟩
      have hij : childIndex i = j := by apply Fin.ext; dsimp [childIndex, i]; omega
      have hcol : color (e (childIndex i)) = true := by
        rw [hij]
        simpa only [j, e.apply_symm_apply] using v.property
      refine ⟨⟨i, mem_filter.mpr ⟨mem_univ _, hcol⟩⟩, ?_⟩
      apply Subtype.ext
      change e (childIndex i) = v.val
      rw [hij]
      exact e.apply_symm_apply _
  have hcard := Fintype.card_congr (Equiv.ofBijective f hf)
  simpa only [A, Fintype.card_coe, Nat.card_eq_fintype_card] using hcard

end GraphChoices.Patterns
