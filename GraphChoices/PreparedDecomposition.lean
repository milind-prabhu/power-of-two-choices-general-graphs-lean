import GraphChoices.PieceEncoding
import GraphChoices.AutomaticBudget
import GraphChoices.ThresholdPolicy

/-! The structural partition as an operational input to Threshold-Greedy.
The stored bounds are derived from the proved decomposition, and the source
edge labels, classes and degree certificates all use that exact partition. -/
namespace GraphChoices.Peeling
open Finset
open ThresholdGreedy
open Patterns
variable {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]

structure PreparedDecomposition (G : Graph L R) (B N : ℕ) (d : ℝ) where
  pieces : List (Graph L R)
  count : pieces.length = numberRounds B
  disjoint : pieces.Pairwise Disjoint
  cover : unionPieces pieces = G
  positive_average : 0 < d
  large_log : 1 < Real.log (N:ℝ)
  average_cap : d ≤ 16*B
  global_cap : ∀ u, leftDegree G u ≤ 4*B
  preprocessing : ∀ u, (leftDegree G u : ℝ) ≤ d*Real.log (N:ℝ)
  left_bound : ∀ i : Fin pieces.length,
    (maxLeftDegree (pieces.get i) : ℝ) ≤ 16*B/(scaleNat i.val : ℝ)
  right_bound : ∀ i : Fin pieces.length,
    (maxRightDegree (pieces.get i) : ℝ) ≤
      16*B*((scaleNat i.val : ℝ)*Real.log (N:ℝ))^(2*graphLogSkewness G d (N:ℝ))

theorem exists_preparedDecomposition (G : Graph L R) (B N : ℕ) (d : ℝ)
    (hd : 0 < d) (hN : 1 < Real.log (N:ℝ))
    (hleft : ∀ u, (leftDegree G u : ℝ) ≤ d*Real.log (N:ℝ))
    (hB : d ≤ 16*B) (hD : ∀ u, leftDegree G u ≤ 4*B) :
    Nonempty (PreparedDecomposition G B N d) := by
  obtain ⟨Ps, hlen, hdisj, hcover, hbounds⟩ := exists_skew_biregular_partition G B d (N:ℝ) hd hN hleft hB hD
  refine ⟨⟨Ps, hlen, hdisj, hcover, hd, hN, hB, hD, hleft, ?_, ?_⟩⟩
  · intro i
    exact maxLeftDegree_real_le _ _ (by positivity) (hbounds i).1
  · intro i
    exact maxRightDegree_real_le _ _ (by positivity) (hbounds i).2

variable {G : Graph L R} {B N : ℕ} {d : ℝ}

noncomputable def PreparedDecomposition.encode (P : PreparedDecomposition G B N d) :
    G → Arrival L R (Fin P.pieces.length) := pieceEncode G P.pieces P.cover

def PreparedDecomposition.DL (P : PreparedDecomposition G B N d) (i : Fin P.pieces.length) : ℕ :=
  maxLeftDegree (P.pieces.get i)

def PreparedDecomposition.DR (P : PreparedDecomposition G B N d) (i : Fin P.pieces.length) : ℕ :=
  maxRightDegree (P.pieces.get i)

noncomputable def PreparedDecomposition.thresholds (P : PreparedDecomposition G B N d) (T : ℕ) :
    Fin P.pieces.length → ℕ :=
  automaticThresholds (E := G) P.DL P.DR (4*B) T (fun i => scaleNat i.val)

def graphBase (G : Graph L R) : BaseGraph (L ⊕ R) G where
  left e := Sum.inl e.val.1
  right e := Sum.inr e.val.2

noncomputable def PreparedDecomposition.policy (P : PreparedDecomposition G B N d) (T : ℕ) : OnlinePolicy G :=
  thresholdPolicy P.encode (P.thresholds T)

noncomputable def PreparedDecomposition.budget (P : PreparedDecomposition G B N d) (T : ℕ) : ℝ :=
  P.pieces.length*(16*Real.exp 1*B*((T:ℝ)/Fintype.card G)+2*graphLogSkewness G d (N:ℝ)+2) +
    (Real.log (16*B*((T:ℝ)/Fintype.card G)/branchTarget (4*B) P.pieces.length ((T:ℝ)/Fintype.card G)) +
      2*graphLogSkewness G d (N:ℝ)*Real.log (Real.log (N:ℝ)))/Real.log 2

theorem PreparedDecomposition.source (P : PreparedDecomposition G B N d) :
    ∀ e, ((P.encode e).left, (P.encode e).right) ∈ P.pieces.get (P.encode e).cls :=
  pieceEncode_source G P.pieces P.cover

theorem PreparedDecomposition.simple (P : PreparedDecomposition G B N d) :
    Function.Injective fun e => ((P.encode e).left, (P.encode e).right) :=
  pieceEncode_simple G P.pieces P.cover

theorem PreparedDecomposition.bucket_bound (P : PreparedDecomposition G B N d) (u : L) (i : Fin P.pieces.length) :
    (sourceBucket P.encode u i).card ≤ P.DL i :=
  (piece_sourceBucket_card_le G P.pieces P.cover u i).trans (leftDegree_le_max _ _)

theorem PreparedDecomposition.global_bucket_bound (P : PreparedDecomposition G B N d) (u : L) :
    (leftSourceBucket P.encode u).card ≤ maxLeftDegree G :=
  (piece_leftSourceBucket_card_le G P.pieces P.cover u).trans (leftDegree_le_max _ _)

theorem PreparedDecomposition.piece_left_cap (P : PreparedDecomposition G B N d) (i : Fin P.pieces.length) (u : L) :
    leftDegree (P.pieces.get i) u ≤ 4*B :=
  (leftDegree_le_max _ _).trans ((piece_maxLeftDegree_le G P.pieces P.cover i).trans (maxLeftDegree_le G _ P.global_cap))

theorem PreparedDecomposition.piece_right_cap (P : PreparedDecomposition G B N d) (i : Fin P.pieces.length) (v : R) :
    rightDegree (P.pieces.get i) v ≤ P.DR i := rightDegree_le_max _ _

theorem PreparedDecomposition.max_degree_preprocessing (P : PreparedDecomposition G B N d) :
    (maxLeftDegree G : ℝ) ≤ d*Real.log (N:ℝ) :=
  maxLeftDegree_real_le G _ (mul_nonneg P.positive_average.le (by linarith [P.large_log])) P.preprocessing

theorem PreparedDecomposition.vertex_count_pos (P : PreparedDecomposition G B N d) : 0 < N := by
  have h := P.large_log
  by_contra hn
  have hz : N = 0 := by omega
  norm_num [hz] at h

theorem PreparedDecomposition.scale_gt_one (P : PreparedDecomposition G B N d) (i : Fin P.pieces.length) :
    (1:ℝ) < scaleNat i.val := by
  have hh := scaleNat_ge_two i.val
  exact_mod_cast (by omega : 1 < scaleNat i.val)

variable [Nonempty G]

theorem PreparedDecomposition.class_count_pos (P : PreparedDecomposition G B N d) : 0 < P.pieces.length := by
  simpa only [Fintype.card_fin] using class_card_pos P.encode

theorem PreparedDecomposition.reference_cap_pos (P : PreparedDecomposition G B N d) : 0 < B := by
  classical
  let e : G := Classical.choice (inferInstance : Nonempty G)
  have hmem : e.val.2 ∈ leftNeighbors G e.val.1 := by simpa [leftNeighbors] using e.property
  have hp : 0 < leftDegree G e.val.1 := card_pos.mpr ⟨e.val.2, hmem⟩
  have hc := P.global_cap e.val.1
  omega

theorem PreparedDecomposition.threshold_budget (P : PreparedDecomposition G B N d) (T : ℕ)
    (hmass : 1 ≤ 16*(B:ℝ)*((T:ℝ)/Fintype.card G)) :
    (∑ i, (P.thresholds T i : ℝ)) ≤ P.budget T := by
  exact automaticThresholds_budget P.pieces.length (4*B) T P.DL P.DR (B:ℝ)
    (Real.log (N:ℝ)) (graphLogSkewness G d (N:ℝ)) P.class_count_pos
    (by exact_mod_cast P.reference_cap_pos) P.large_log.le (graphLogSkewness_nonneg G d (N:ℝ))
    hmass P.left_bound P.right_bound

theorem PreparedDecomposition.mass_at_vertex_horizon (P : PreparedDecomposition G B N d)
    (haverage : 2*(G.card : ℝ) = (N:ℝ)*d) :
    1 ≤ 16*(B:ℝ)*((N:ℝ)/Fintype.card G) := by
  have hE : (0:ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  rw [← mul_div_assoc]
  apply (le_div_iff₀ hE).mpr
  have hp := mul_le_mul_of_nonneg_left P.average_cap (Nat.cast_nonneg N : (0:ℝ) ≤ N)
  have heq : (Fintype.card G : ℝ) = G.card := by rw [Fintype.card_coe]
  rw [heq]
  nlinarith

end GraphChoices.Peeling
