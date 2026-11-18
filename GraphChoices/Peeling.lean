import GraphChoices.CapacityMatching
import Aesop

/-! The finite graph-theoretic peeling step behind Lemma 3.7. This module
proves extraction and termination from a hereditary neighborhood-expansion
condition. The analytic-to-graph certificate is kept as an explicit premise. -/
namespace GraphChoices.Peeling
open Finset
variable {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]

abbrev Graph (L R : Type*) := Finset (L × R)

def leftNeighbors (H : Graph L R) (u : L) : Finset R :=
  univ.filter fun v => (u,v) ∈ H

def rightNeighbors (H : Graph L R) (v : R) : Finset L :=
  univ.filter fun u => (u,v) ∈ H

def leftDegree (H : Graph L R) (u : L) : ℕ := (leftNeighbors H u).card

def rightDegree (H : Graph L R) (v : R) : ℕ := (rightNeighbors H v).card

 theorem leftNeighbors_mono {F H : Graph L R} (h : F ⊆ H) (u : L) :
    leftNeighbors F u ⊆ leftNeighbors H u := by
  intro v hv
  simp only [leftNeighbors, mem_filter, mem_univ, true_and] at hv ⊢
  exact h hv

 theorem leftDegree_mono {F H : Graph L R} (h : F ⊆ H) (u : L) :
    leftDegree F u ≤ leftDegree H u := card_le_card (leftNeighbors_mono h u)

 theorem leftDegree_sdiff {F H : Graph L R} (h : F ⊆ H) (u : L) :
    leftDegree (H \ F) u = leftDegree H u - leftDegree F u := by
  have heq : leftNeighbors (H \ F) u = leftNeighbors H u \ leftNeighbors F u := by
    ext v; simp [leftNeighbors]
  rw [leftDegree, heq, card_sdiff_of_subset (leftNeighbors_mono h u)]
  rfl

 theorem rightDegree_union_le (F H : Graph L R) (v : R) :
    rightDegree (F ∪ H) v ≤ rightDegree F v + rightDegree H v := by
  have heq : rightNeighbors (F ∪ H) v = rightNeighbors F v ∪ rightNeighbors H v := by
    ext u; simp [rightNeighbors]
  exact (congrArg card heq).le.trans (card_union_le _ _)

/-- Every sufficiently high-degree left set expands, in every residual graph. -/
def PeelingExpansion (H : Graph L R) (k b : ℕ) : Prop :=
  ∀ F : Graph L R, F ⊆ H → ∀ A : Finset L,
    (∀ u ∈ A, k < leftDegree F u) →
      A.card ≤ b * (GraphChoices.neighbors (fun u v => (u,v) ∈ F) A).card

 theorem PeelingExpansion.mono {F H : Graph L R} {k b : ℕ}
    (h : PeelingExpansion H k b) (hF : F ⊆ H) : PeelingExpansion F k b := by
  intro J hJ A hA
  exact h J (hJ.trans hF) A hA

/-- A matching covers exactly a specified active set, with right capacity b. -/
 theorem exists_active_matching (H : Graph L R) (A : Finset L) (b : ℕ)
    (hexpand : ∀ B : Finset L, B ⊆ A →
      B.card ≤ b * (GraphChoices.neighbors (fun u v => (u,v) ∈ H) B).card) :
    ∃ M : Graph L R, M ⊆ H ∧
      (∀ u, leftDegree M u = if u ∈ A then 1 else 0) ∧
      (∀ v, rightDegree M v ≤ b) := by
  classical
  let U := {u : L // u ∈ A}
  let r (u : U) (v : R) := (u.val,v) ∈ H
  have hcap (B : Finset U) : B.card ≤ b * (GraphChoices.neighbors r B).card := by
    have hb := hexpand (B.image Subtype.val) (by
      intro u hu
      obtain ⟨w, hw, rfl⟩ := mem_image.mp hu
      exact w.property)
    have hi : (B.image Subtype.val).card = B.card := card_image_of_injective _ Subtype.val_injective
    have heq : GraphChoices.neighbors (fun u v => (u,v) ∈ H) (B.image Subtype.val) =
        GraphChoices.neighbors r B := by
      ext v
      simp only [GraphChoices.neighbors, mem_filter, mem_univ, true_and, mem_image]
      constructor
      · rintro ⟨u, ⟨w, hw, rfl⟩, h⟩; exact ⟨w, hw, h⟩
      · rintro ⟨w, hw, h⟩; exact ⟨w.val, ⟨w, hw, rfl⟩, h⟩
    simpa [hi, heq] using hb
  obtain ⟨f, hf, hfb⟩ := GraphChoices.exists_capacity_matching r b hcap
  let M : Graph L R := univ.image fun u : U => (u.val, f u)
  refine ⟨M, ?_, ?_, ?_⟩
  · intro p hp
    obtain ⟨u, hu, rfl⟩ := mem_image.mp hp
    exact hf u
  · intro u
    by_cases hu : u ∈ A
    · have heq : leftNeighbors M u = {f ⟨u,hu⟩} := by
        ext v
        simp only [leftNeighbors, mem_filter, mem_univ, true_and, M, mem_image, mem_singleton]
        constructor
        · rintro ⟨w, hw⟩
          have hwval : w.val = u := congrArg Prod.fst hw
          have hwsub : w = ⟨u,hu⟩ := Subtype.ext hwval
          have := congrArg Prod.snd hw
          simpa [hwsub] using this.symm
        · intro hv
          exact ⟨⟨u,hu⟩, by simp [hv]⟩
      simp [leftDegree, heq, hu]
    · have heq : leftNeighbors M u = ∅ := by
        ext v
        simp only [leftNeighbors, mem_filter, mem_univ, true_and, M, mem_image, notMem_empty, iff_false]
        rintro ⟨w, hw⟩
        have hwval : w.val = u := congrArg Prod.fst hw
        exact hu (hwval ▸ w.property)
      simp [leftDegree, heq, hu]
  · intro v
    have heq : rightNeighbors M v = (univ.filter fun u : U => f u = v).image Subtype.val := by
      ext u
      simp only [rightNeighbors, mem_filter, mem_univ, true_and, M, mem_image]
      constructor
      · rintro ⟨w, hw⟩
        exact ⟨w, congrArg Prod.snd hw, congrArg Prod.fst hw⟩
      · rintro ⟨w, hw, rfl⟩
        exact ⟨w, by simp [hw]⟩
    calc
      rightDegree M v = ((univ.filter fun u : U => f u = v).image Subtype.val).card := congrArg card heq
      _ ≤ (univ.filter fun u : U => f u = v).card := card_image_le
      _ ≤ b := hfb v

/-- Extraction terminates after at most D matching rounds. The removed piece
has right degree at most D b, and the residual has left degree at most k. -/
 theorem exists_peeling_piece (H : Graph L R) (k b D : ℕ)
    (hD : ∀ u, leftDegree H u ≤ D) (hexpand : PeelingExpansion H k b) :
    ∃ P : Graph L R, P ⊆ H ∧
      (∀ u, leftDegree (H \ P) u ≤ k) ∧
      (∀ v, rightDegree P v ≤ D*b) := by
  induction D generalizing H with
  | zero =>
    refine ⟨∅, empty_subset _, ?_, ?_⟩
    · intro u; simpa using (hD u).trans (Nat.zero_le k)
    · intro v; simp [rightDegree, rightNeighbors]
  | succ D ih =>
    by_cases hk : D+1 ≤ k
    · refine ⟨∅, empty_subset _, ?_, ?_⟩
      · intro u; simpa using (hD u).trans hk
      · intro v; simp [rightDegree, rightNeighbors]
    · let A : Finset L := univ.filter fun u => k < leftDegree H u
      obtain ⟨M, hMH, hML, hMR⟩ := exists_active_matching H A b (by
        intro B hBA
        apply hexpand H (subset_refl _) B
        intro u hu
        exact (mem_filter.mp (hBA hu)).2)
      have hnext (u : L) : leftDegree (H \ M) u ≤ D := by
        rw [leftDegree_sdiff hMH, hML]
        by_cases hu : u ∈ A
        · rw [if_pos hu]
          have := hD u
          omega
        · rw [if_neg hu]
          have hlow : leftDegree H u ≤ k := by
            simpa only [A, mem_filter, mem_univ, true_and, not_lt] using hu
          omega
      obtain ⟨Q, hQ, hQleft, hQright⟩ := ih (H \ M) hnext
        (hexpand.mono sdiff_subset)
      have hQH : Q ⊆ H := hQ.trans sdiff_subset
      refine ⟨M ∪ Q, union_subset hMH hQH, ?_, ?_⟩
      · intro u
        have heq : H \ (M ∪ Q) = (H \ M) \ Q := by ext p; simp; tauto
        rw [heq]
        exact hQleft u
      · intro v
        have hdeg := rightDegree_union_le M Q v
        have hm := hMR v
        have hq := hQright v
        nlinarith

end GraphChoices.Peeling
