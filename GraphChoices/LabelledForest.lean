import GraphChoices.ShapeCoverage
import Mathlib.Data.Nat.Find

/-! A spanning first-child/next-sibling forest in every finite connected
graph. Maximality is over the bounded node count, not an assumed enumeration.
The distinguished root is external to the binary forest. -/
namespace GraphChoices.Patterns
open Finset
variable {V : Type*}

def forestLabels : Tree V → List V
  | .nil => []
  | .node v l r => v :: (forestLabels l ++ forestLabels r)

def ForestValid (G : SimpleGraph V) : V → Tree V → Prop
  | _, .nil => True
  | p, .node v l r => G.Adj p v ∧ ForestValid G v l ∧ ForestValid G p r

theorem forestLabels_length (t : Tree V) : (forestLabels t).length = t.numNodes := by
  induction t with
  | nil => rfl
  | node v l r hl hr => simp [forestLabels, Tree.numNodes, hl, hr]

/-- Insert a new child at any named vertex in the forest, without imposing
an ordering on the old vertices. The labels change by exactly one insertion. -/
theorem forest_grow {G : SimpleGraph V} (t : Tree V) (p u x : V)
    (ht : ForestValid G p t) (hu : u = p ∨ u ∈ forestLabels t) (hux : G.Adj u x) :
    ∃ t' : Tree V, ForestValid G p t' ∧ (forestLabels t').Perm (x :: forestLabels t) := by
  induction t generalizing p with
  | nil =>
    have hup : u = p := by simpa [forestLabels] using hu
    subst u
    exact ⟨.node x .nil .nil, ⟨hux, trivial, trivial⟩, by simp [forestLabels]⟩
  | node v l r hl hr =>
    by_cases hup : u = p
    · subst u
      exact ⟨.node x .nil (.node v l r), ⟨hux, trivial, ht⟩, by simp [forestLabels]⟩
    have hu' : u ∈ forestLabels (.node v l r) := hu.resolve_left hup
    obtain ⟨hpv, hvl, hpr⟩ := ht
    simp only [forestLabels, List.mem_cons, List.mem_append] at hu'
    rcases hu' with rfl | hu | hu
    · refine ⟨.node u (.node x .nil l) r, ⟨hpv, ⟨hux, trivial, hvl⟩, hpr⟩, ?_⟩
      simp only [forestLabels, List.nil_append, List.cons_append]
      exact List.Perm.swap _ _ _
    · obtain ⟨l', hl', hperm⟩ := hl v hvl (Or.inr hu)
      refine ⟨.node v l' r, ⟨hpv, hl', hpr⟩, ?_⟩
      have h := (hperm.append_right (forestLabels r)).cons v
      exact h.trans (List.Perm.swap _ _ _)
    · obtain ⟨r', hr', hperm⟩ := hr p hpr (Or.inr hu)
      refine ⟨.node v l r', ⟨hpv, hvl, hr'⟩, ?_⟩
      have h := (hperm.append_left (forestLabels l)).cons v
      apply h.trans
      simpa only [forestLabels, List.cons_append] using
        (List.perm_middle (a := x) (l₁ := v :: forestLabels l) (l₂ := forestLabels r))

theorem walk_mem_of_closed {G : SimpleGraph V} {u v : V} (p : G.Walk u v)
    (S : Set V) (hu : u ∈ S) (hclosed : ∀ a ∈ S, ∀ b, G.Adj a b → b ∈ S) : v ∈ S := by
  induction p with
  | nil => exact hu
  | @cons a b c hab p ih => exact ih (hclosed a hu b hab)

/-- Every finite connected graph has a nonrepeating spanning labelled binary
forest with the designated root external to that forest. -/
theorem exists_spanning_labelled_forest [Fintype V] (G : SimpleGraph V)
    (hc : G.Connected) (root : V) :
    ∃ t : Tree V, ForestValid G root t ∧ (root :: forestLabels t).Nodup ∧
      (∀ v, v ∈ root :: forestLabels t) ∧ t.numNodes+1 = Fintype.card V := by
  classical
  let P (n : ℕ) : Prop := ∃ t : Tree V,
    t.numNodes = n ∧ ForestValid G root t ∧ (root :: forestLabels t).Nodup
  have hzero : P 0 := ⟨.nil, rfl, trivial, by simp [forestLabels]⟩
  let n := Nat.findGreatest P (Fintype.card V)
  obtain ⟨t, hcount, ht, hn⟩ := Nat.findGreatest_spec (Nat.zero_le (Fintype.card V)) hzero
  have hclosed : ∀ u ∈ root :: forestLabels t, ∀ x, G.Adj u x → x ∈ root :: forestLabels t := by
    intro u hu x hux
    by_contra hx
    have hu' : u = root ∨ u ∈ forestLabels t := by simpa using hu
    obtain ⟨t', ht', hperm⟩ := forest_grow t root u x ht hu' hux
    have hn0 : (x :: root :: forestLabels t).Nodup := List.nodup_cons.mpr ⟨hx, hn⟩
    have hn1 : (root :: x :: forestLabels t).Nodup := (List.Perm.swap _ _ _).nodup_iff.mpr hn0
    have hn' : (root :: forestLabels t').Nodup := (hperm.cons root).nodup_iff.mpr hn1
    have hlen := hperm.length_eq
    simp only [forestLabels_length, List.length_cons] at hlen
    have hsize : t'.numNodes = n+1 := by omega
    have hbound := hn'.length_le_card
    simp only [List.length_cons, forestLabels_length] at hbound
    have hnew : P (n+1) := ⟨t', hsize, ht', hn'⟩
    exact Nat.findGreatest_is_greatest (show n < n+1 by omega) (by omega) hnew
  have hcover : ∀ v, v ∈ root :: forestLabels t := by
    intro v
    obtain ⟨p⟩ := hc root v
    exact walk_mem_of_closed p {w | w ∈ root :: forestLabels t} (by simp) hclosed
  refine ⟨t, ht, hn, hcover, ?_⟩
  have hfin : (root :: forestLabels t).toFinset = univ := by
    apply Finset.eq_univ_of_forall
    intro v
    exact List.mem_toFinset.mpr (hcover v)
  have hcard := congrArg Finset.card hfin
  simpa only [List.toFinset_card_of_nodup hn, card_univ, List.length_cons, forestLabels_length] using hcard

end GraphChoices.Patterns
