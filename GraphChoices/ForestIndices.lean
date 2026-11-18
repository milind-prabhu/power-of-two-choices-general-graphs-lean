import GraphChoices.LabelledForest

/-! Preorder indices of a labelled forest and their agreement with the
previously counted unlabelled shape representation. -/
namespace GraphChoices.Patterns
variable {V : Type*}

theorem map_numNodes {W : Type*} (t : Tree V) (f : V → W) : (t.map f).numNodes = t.numNodes := by
  induction t with
  | nil => rfl
  | node v l r hl hr => simp [Tree.map, Tree.numNodes, hl, hr]

def eraseForest (t : Tree V) : Tree Unit := t.map (fun _ => ())

theorem eraseForest_numNodes (t : Tree V) : (eraseForest t).numNodes = t.numNodes := by
  induction t with
  | nil => rfl
  | node v l r hl hr => simp [eraseForest, Tree.map, Tree.numNodes] at *; omega

def forestValue : Tree V → V → ℕ → V
  | .nil, fallback, _ => fallback
  | .node v l r, fallback, i =>
    if i = 0 then v else if i ≤ l.numNodes then forestValue l fallback (i-1)
    else forestValue r fallback (i-1-l.numNodes)

def parentPos : Tree V → ℕ → ℕ → ℕ → ℕ
  | .nil, p, _, _ => p
  | .node _ l r, p, start, i =>
    if i = 0 then p else if i ≤ l.numNodes then parentPos l (start+1) (start+1) (i-1)
    else parentPos r p (start+1+l.numNodes) (i-1-l.numNodes)

def sidePos : Tree V → Bool → ℕ → Bool
  | .nil, side, _ => side
  | .node _ l r, side, i =>
    if i = 0 then side else if i ≤ l.numNodes then sidePos l (!side) (i-1)
    else sidePos r side (i-1-l.numNodes)

theorem forestValue_eq_get (t : Tree V) (fallback : V) (i : ℕ) (hi : i < t.numNodes) :
    forestValue t fallback i = (forestLabels t)[i]'(by rw [forestLabels_length]; exact hi) := by
  induction t generalizing i with
  | nil => simp at hi
  | node v l r hl hr =>
    cases i with
    | zero => simp [forestValue, forestLabels]
    | succ i =>
      simp only [forestLabels, List.getElem_cons_succ]
      by_cases hil : i+1 ≤ l.numNodes
      · rw [List.getElem_append_left (by rw [forestLabels_length]; omega)]
        simpa [forestValue, hil] using hl i (by omega)
      · rw [List.getElem_append_right (by rw [forestLabels_length]; omega)]
        have hir : i-l.numNodes < r.numNodes := by simp only [Tree.numNodes] at hi; omega
        simpa [forestValue, hil, forestLabels_length] using hr (i-l.numNodes) hir

theorem forestParent_eq_parentPos (t : Tree V) (p start : ℕ) (hp : p ≤ start)
    (i : Fin (eraseForest t).numNodes) :
    (forestParent (eraseForest t) p start hp i).val = parentPos t p start i.val := by
  induction t generalizing p start with
  | nil => exact Fin.elim0 i
  | node v l r hl hr =>
    by_cases hz : i.val = 0
    · simp [eraseForest, Tree.map, forestParent, parentPos, hz]
    by_cases hil : i.val ≤ l.numNodes
    · simp only [eraseForest, Tree.map, forestParent, parentPos, hz, if_false,
        map_numNodes, hil, dite_true, dite_false, if_true]
      exact hl (start+1) (start+1) le_rfl _
    · simp only [eraseForest, Tree.map, forestParent, parentPos, hz, if_false,
        map_numNodes, hil, dite_true, dite_false]
      have hir : i.val-1-(eraseForest l).numNodes < (eraseForest r).numNodes := by
        have hbound := i.isLt
        simp only [eraseForest_numNodes, Tree.numNodes] at hbound ⊢
        omega
      have h := hr p (start+1+(eraseForest l).numNodes) (by omega)
        ⟨i.val-1-(eraseForest l).numNodes, hir⟩
      convert h using 1 <;> simp only [eraseForest_numNodes]

theorem forestSide_eq_sidePos (t : Tree V) (side : Bool) (i : Fin (eraseForest t).numNodes) :
    forestSide (eraseForest t) side i = sidePos t side i.val := by
  induction t generalizing side with
  | nil => exact Fin.elim0 i
  | node v l r hl hr =>
    by_cases hz : i.val = 0
    · simp [eraseForest, Tree.map, forestSide, sidePos, hz]
    by_cases hil : i.val ≤ l.numNodes
    · simp only [eraseForest, Tree.map, forestSide, sidePos, hz, if_false,
        map_numNodes, hil, dite_true, dite_false, if_true]
      exact hl (!side) _
    · simp only [eraseForest, Tree.map, forestSide, sidePos, hz, if_false,
        map_numNodes, hil, dite_true, dite_false]
      exact hr side _

/-- Indexed edges and side labels are inherited from the labelled forest's
recursive graph edges. The lookup may be embedded in any larger preorder. -/
theorem forest_index_spec (G : SimpleGraph V) (color : V → Bool)
    (hcolor : ∀ u v, G.Adj u v → color u ≠ color v)
    (t : Tree V) (F : ℕ → V) (fallback : V) (p start : ℕ) (side : Bool)
    (ht : ForestValid G (F p) t) (hparent : color (F p) = !side)
    (hvalues : ∀ i < t.numNodes, F (start+i+1) = forestValue t fallback i) :
    ∀ i < t.numNodes,
      G.Adj (F (start+i+1)) (F (parentPos t p start i)) ∧
      color (F (start+i+1)) = sidePos t side i := by
  induction t generalizing p start side with
  | nil => intro i hi; simp at hi
  | node v l r hl hr =>
    obtain ⟨hpv, hvl, hpr⟩ := ht
    have hv : F (start+1) = v := by simpa [forestValue] using hvalues 0 (by simp)
    have hcv : color v = side := by
      have hne := hcolor (F p) v hpv
      cases side <;> cases hc : color v <;> simp_all
    intro i hi
    by_cases hz : i = 0
    · subst i
      simpa [parentPos, sidePos, hv] using And.intro hpv.symm hcv
    by_cases hil : i ≤ l.numNodes
    · have hvals : ∀ j < l.numNodes, F ((start+1)+j+1) = forestValue l fallback j := by
        intro j hj
        have h := hvalues (j+1) (by simp only [Tree.numNodes]; omega)
        have hsplit : forestValue (.node v l r) fallback (j+1) = forestValue l fallback j := by
          simp [forestValue, show j+1 ≤ l.numNodes by omega]
        rw [hsplit] at h
        convert h using 1 <;> congr 1 <;> omega
      have hvalid : ForestValid G (F (start+1)) l := by simpa only [hv] using hvl
      have hcparent : color (F (start+1)) = !(!side) := by simpa [hv] using hcv
      have h := hl (start+1) (start+1) (!side) hvalid hcparent hvals (i-1) (by omega)
      have heq : start+1+(i-1)+1 = start+i+1 := by omega
      simpa only [parentPos, sidePos, hz, if_false, hil, if_true, heq] using h
    · have hvals : ∀ j < r.numNodes, F ((start+1+l.numNodes)+j+1) = forestValue r fallback j := by
        intro j hj
        have h := hvalues (j+1+l.numNodes) (by simp only [Tree.numNodes]; omega)
        have hnot : ¬j+1+l.numNodes ≤ l.numNodes := by omega
        have hsplit : forestValue (.node v l r) fallback (j+1+l.numNodes) = forestValue r fallback j := by
          rw [forestValue, if_neg (by omega), if_neg hnot]
          congr 1
          omega
        rw [hsplit] at h
        convert h using 1 <;> congr 1 <;> omega
      have h := hr p (start+1+l.numNodes) side hpr hparent hvals (i-1-l.numNodes)
        (by simp only [Tree.numNodes] at hi; omega)
      have heq : start+1+l.numNodes+(i-1-l.numNodes)+1 = start+i+1 := by omega
      simpa only [parentPos, sidePos, hz, if_false, hil, heq] using h

end GraphChoices.Patterns
