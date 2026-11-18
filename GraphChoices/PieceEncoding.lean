import GraphChoices.SkewDecomposition
import GraphChoices.PreprocessedShattering

/-! Actual edge classes and degree certificates from an exact finite graph
partition. Edge labels are the base graph's concrete endpoint pairs, so
simplicity and all bucket bounds are proved rather than assumed. -/
namespace GraphChoices.Peeling
open Finset
open ThresholdGreedy
variable {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]

theorem mem_unionPieces_iff (Ps : List (Graph L R)) (e : L × R) :
    e ∈ unionPieces Ps ↔ ∃ P ∈ Ps, e ∈ P := by
  induction Ps with
  | nil => simp [unionPieces]
  | cons P Ps ih => simp [unionPieces, ih, or_and_right, exists_or]

theorem exists_piece_index (G : Graph L R) (Ps : List (Graph L R))
    (hcover : unionPieces Ps = G) (e : G) : ∃ i : Fin Ps.length, e.val ∈ Ps.get i := by
  have he : e.val ∈ unionPieces Ps := by rw [hcover]; exact e.property
  obtain ⟨P, hP, heP⟩ := (mem_unionPieces_iff Ps e.val).mp he
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hP
  exact ⟨i, by rw [hi]; exact heP⟩

noncomputable def pieceClass (G : Graph L R) (Ps : List (Graph L R))
    (hcover : unionPieces Ps = G) (e : G) : Fin Ps.length :=
  Classical.choose (exists_piece_index G Ps hcover e)

theorem pieceClass_mem (G : Graph L R) (Ps : List (Graph L R))
    (hcover : unionPieces Ps = G) (e : G) : e.val ∈ Ps.get (pieceClass G Ps hcover e) :=
  Classical.choose_spec (exists_piece_index G Ps hcover e)

noncomputable def pieceEncode (G : Graph L R) (Ps : List (Graph L R))
    (hcover : unionPieces Ps = G) (e : G) : Arrival L R (Fin Ps.length) :=
  ⟨e.val.1, e.val.2, pieceClass G Ps hcover e⟩

theorem pieceEncode_simple (G : Graph L R) (Ps : List (Graph L R)) (hcover : unionPieces Ps = G) :
    Function.Injective fun e => ((pieceEncode G Ps hcover e).left, (pieceEncode G Ps hcover e).right) := by
  intro e f h
  exact Subtype.ext h

theorem pieceEncode_source (G : Graph L R) (Ps : List (Graph L R)) (hcover : unionPieces Ps = G) :
    ∀ e, ((pieceEncode G Ps hcover e).left, (pieceEncode G Ps hcover e).right) ∈
      Ps.get (pieceEncode G Ps hcover e).cls := pieceClass_mem G Ps hcover

theorem piece_sourceBucket_card_le (G : Graph L R) (Ps : List (Graph L R))
    (hcover : unionPieces Ps = G) (u : L) (i : Fin Ps.length) :
    (sourceBucket (pieceEncode G Ps hcover) u i).card ≤ leftDegree (Ps.get i) u := by
  classical
  apply card_le_card_of_injOn (fun e : G => e.val.2)
  · intro e he
    obtain ⟨hu, hc⟩ := (mem_filter.mp he).2
    have hsrc := pieceEncode_source G Ps hcover e
    rw [hc] at hsrc
    change e.val.1 = u at hu
    change (e.val.1, e.val.2) ∈ Ps.get i at hsrc
    change e.val.2 ∈ leftNeighbors (Ps.get i) u
    simp only [leftNeighbors, mem_filter, mem_univ, true_and]
    rw [← hu]
    exact hsrc
  · intro e he f hf hright
    have heleft := (mem_filter.mp he).2.1
    have hfleft := (mem_filter.mp hf).2.1
    apply Subtype.ext
    exact Prod.ext (heleft.trans hfleft.symm) hright

theorem piece_leftSourceBucket_card_le (G : Graph L R) (Ps : List (Graph L R))
    (hcover : unionPieces Ps = G) (u : L) :
    (leftSourceBucket (pieceEncode G Ps hcover) u).card ≤ leftDegree G u := by
  classical
  apply card_le_card_of_injOn (fun e : G => e.val.2)
  · intro e he
    have hu := (mem_filter.mp he).2
    change e.val.1 = u at hu
    change e.val.2 ∈ leftNeighbors G u
    simp only [leftNeighbors, mem_filter, mem_univ, true_and]
    rw [← hu]
    exact e.property
  · intro e he f hf hright
    apply Subtype.ext
    exact Prod.ext ((mem_filter.mp he).2.trans (mem_filter.mp hf).2.symm) hright

def maxLeftDegree (G : Graph L R) : ℕ := univ.sup (leftDegree G)

def maxRightDegree (G : Graph L R) : ℕ := univ.sup (rightDegree G)

theorem leftDegree_le_max (G : Graph L R) (u : L) : leftDegree G u ≤ maxLeftDegree G :=
  Finset.le_sup (mem_univ u)

theorem rightDegree_le_max (G : Graph L R) (v : R) : rightDegree G v ≤ maxRightDegree G :=
  Finset.le_sup (mem_univ v)

theorem maxLeftDegree_le (G : Graph L R) (D : ℕ) (h : ∀ u, leftDegree G u ≤ D) :
    maxLeftDegree G ≤ D := Finset.sup_le (fun u _ => h u)

theorem nat_sup_cast_le {U : Type*} (s : Finset U) (f : U → ℕ) (K : ℝ)
    (hK : 0 ≤ K) (h : ∀ u ∈ s, (f u : ℝ) ≤ K) : ((s.sup f : ℕ) : ℝ) ≤ K := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hK
  | @insert u s hu ih =>
    rw [Finset.sup_insert]
    change ((max (f u) (s.sup f) : ℕ) : ℝ) ≤ K
    rw [Nat.cast_max]
    exact max_le (h u (mem_insert_self _ _)) (ih (fun v hv => h v (mem_insert_of_mem hv)))

theorem maxLeftDegree_real_le (G : Graph L R) (K : ℝ)
    (hK : 0 ≤ K) (h : ∀ u, (leftDegree G u : ℝ) ≤ K) : (maxLeftDegree G : ℝ) ≤ K :=
  nat_sup_cast_le _ _ _ hK (fun u _ => h u)

theorem maxRightDegree_real_le (G : Graph L R) (K : ℝ)
    (hK : 0 ≤ K) (h : ∀ v, (rightDegree G v : ℝ) ≤ K) : (maxRightDegree G : ℝ) ≤ K :=
  nat_sup_cast_le _ _ _ hK (fun v _ => h v)

theorem piece_maxLeftDegree_le (G : Graph L R) (Ps : List (Graph L R))
    (hcover : unionPieces Ps = G) (i : Fin Ps.length) :
    maxLeftDegree (Ps.get i) ≤ maxLeftDegree G := by
  apply maxLeftDegree_le
  intro u
  have hsub : Ps.get i ⊆ G := by
    rw [← hcover]
    exact mem_subset_unionPieces (List.get_mem _ _)
  exact (leftDegree_mono hsub u).trans (leftDegree_le_max G u)

end GraphChoices.Peeling
