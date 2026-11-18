import GraphChoices.Peeling

/-! Iteration of the proved peeling round: every finite valid schedule yields
edge-disjoint pieces with their per-round degree bounds. A final cutoff of zero
gives an exact edge partition, not just a collection of partial subgraphs. -/
namespace GraphChoices.Peeling
open Finset
variable {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]

def unionPieces : List (Graph L R) → Graph L R
  | [] => ∅
  | P::Ps => P ∪ unionPieces Ps

def finalBudget : ℕ → List (ℕ × ℕ) → ℕ
  | D, [] => D
  | _, (k,_)::ss => finalBudget k ss

/-- The left cap and right cap promised for each successive piece. -/
def pieceBudgets : ℕ → List (ℕ × ℕ) → List (ℕ × ℕ)
  | _, [] => []
  | D, (k,b)::ss => (D,D*b) :: pieceBudgets k ss

inductive PeelingRun : Graph L R → ℕ → List (ℕ × ℕ) → List (Graph L R) → Graph L R → Prop
  | nil (H : Graph L R) (D : ℕ) (hD : ∀ u, leftDegree H u ≤ D) : PeelingRun H D [] [] H
  | cons {H P : Graph L R} {D k b : ℕ} {ss : List (ℕ × ℕ)} {Ps : List (Graph L R)} {F : Graph L R}
      (hP : P ⊆ H) (hPL : ∀ u, leftDegree P u ≤ D)
      (hPR : ∀ v, rightDegree P v ≤ D*b)
      (tail : PeelingRun (H \ P) k ss Ps F) :
      PeelingRun H D ((k,b)::ss) (P::Ps) F

 theorem mem_subset_unionPieces {P : Graph L R} {Ps : List (Graph L R)} (hP : P ∈ Ps) :
    P ⊆ unionPieces Ps := by
  induction Ps with
  | nil => simp at hP
  | cons Q Qs ih =>
    rcases List.mem_cons.mp hP with rfl | hp
    · exact subset_union_left
    · exact (ih hp).trans subset_union_right

/-- Finite construction of a complete peeling execution. -/
 theorem exists_peeling_run (G H : Graph L R) (hHG : H ⊆ G) (D : ℕ)
    (hD : ∀ u, leftDegree H u ≤ D) (ss : List (ℕ × ℕ))
    (hexpand : ∀ kb ∈ ss, PeelingExpansion G kb.1 kb.2) :
    ∃ Ps F, PeelingRun H D ss Ps F := by
  induction ss generalizing H D with
  | nil => exact ⟨[],H,PeelingRun.nil H D hD⟩
  | cons kb ss ih =>
    obtain ⟨k,b⟩ := kb
    obtain ⟨P,hPH,hnext,hPR⟩ := exists_peeling_piece H k b D hD
      ((hexpand (k,b) (by simp)).mono hHG)
    obtain ⟨Ps,F,htail⟩ := ih (H \ P) (sdiff_subset.trans hHG) k hnext
      (fun kb hkb => hexpand kb (by simp [hkb]))
    refine ⟨P::Ps,F,PeelingRun.cons hPH ?_ hPR htail⟩
    intro u
    exact (leftDegree_mono hPH u).trans (hD u)

 theorem PeelingRun.length_eq {H F : Graph L R} {D : ℕ}
    {ss : List (ℕ × ℕ)} {Ps : List (Graph L R)} (h : PeelingRun H D ss Ps F) :
    Ps.length = ss.length := by
  induction h with
  | nil => rfl
  | cons _ _ _ _ ih => simpa using ih

 theorem PeelingRun.degree_bounds {H F : Graph L R} {D : ℕ}
    {ss : List (ℕ × ℕ)} {Ps : List (Graph L R)} (h : PeelingRun H D ss Ps F) :
    List.Forall₂ (fun P kb => (∀ u, leftDegree P u ≤ kb.1) ∧
      (∀ v, rightDegree P v ≤ kb.2)) Ps (pieceBudgets D ss) := by
  induction h with
  | nil => exact List.Forall₂.nil
  | cons _ hPL hPR _ ih => exact List.Forall₂.cons ⟨hPL,hPR⟩ ih

 theorem PeelingRun.final_degree_bound {H F : Graph L R} {D : ℕ}
    {ss : List (ℕ × ℕ)} {Ps : List (Graph L R)} (h : PeelingRun H D ss Ps F) :
    ∀ u, leftDegree F u ≤ finalBudget D ss := by
  induction h with
  | nil _ _ hD => exact hD
  | cons _ _ _ _ ih => exact ih

/-- Every recorded execution really is an edge-disjoint extraction; the final
residual is precisely the complement of all pieces in the original graph. -/
 theorem PeelingRun.partition_properties {H F : Graph L R} {D : ℕ}
    {ss : List (ℕ × ℕ)} {Ps : List (Graph L R)} (h : PeelingRun H D ss Ps F) :
    unionPieces Ps ⊆ H ∧ F = H \ unionPieces Ps ∧ Ps.Pairwise Disjoint := by
  induction h with
  | nil => simp [unionPieces]
  | @cons H P D k b ss Ps F hPH hPL hPR htail ih =>
    obtain ⟨hPs,hF,hdisj⟩ := ih
    refine ⟨union_subset hPH (hPs.trans sdiff_subset), ?_, ?_⟩
    · rw [hF]
      ext p
      simp [unionPieces]
      tauto
    · apply List.pairwise_cons.mpr
      refine ⟨?_,hdisj⟩
      intro Q hQ
      apply Finset.disjoint_left.mpr
      intro e heP heQ
      have he : e ∈ H \ P := hPs (mem_subset_unionPieces hQ heQ)
      exact (mem_sdiff.mp he).2 heP

 theorem graph_empty_of_left_degrees_zero (H : Graph L R)
    (h : ∀ u, leftDegree H u ≤ 0) : H = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro p hp
  have hn : p.2 ∈ leftNeighbors H p.1 := by simpa [leftNeighbors] using hp
  have hc : 0 < leftDegree H p.1 := card_pos.mpr ⟨p.2,hn⟩
  have := h p.1
  omega

/-- An exact edge partition with one piece per scheduled round and all degree
bounds, provided the schedule ends at zero. -/
 theorem exists_edge_partition (G : Graph L R) (D : ℕ)
    (hD : ∀ u, leftDegree G u ≤ D) (ss : List (ℕ × ℕ))
    (hexpand : ∀ kb ∈ ss, PeelingExpansion G kb.1 kb.2)
    (hfinal : finalBudget D ss = 0) :
    ∃ Ps : List (Graph L R), Ps.length = ss.length ∧ Ps.Pairwise Disjoint ∧
      unionPieces Ps = G ∧
      List.Forall₂ (fun P kb => (∀ u, leftDegree P u ≤ kb.1) ∧
        (∀ v, rightDegree P v ≤ kb.2)) Ps (pieceBudgets D ss) := by
  obtain ⟨Ps,F,h⟩ := exists_peeling_run G G (subset_refl _) D hD ss hexpand
  obtain ⟨hsub,hF,hpair⟩ := h.partition_properties
  have hz : F = ∅ := graph_empty_of_left_degrees_zero F (by simpa [hfinal] using h.final_degree_bound)
  have hcover : unionPieces Ps = G := by
    apply subset_antisymm hsub
    intro e he
    by_contra hn
    have : e ∈ F := by rw [hF]; exact mem_sdiff.mpr ⟨he,hn⟩
    simpa [hz] using this
  exact ⟨Ps,h.length_eq,hpair,hcover,h.degree_bounds⟩

end GraphChoices.Peeling
