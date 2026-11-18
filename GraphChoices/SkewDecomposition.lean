import GraphChoices.GraphSkew
import GraphChoices.Decomposition
import Mathlib.Data.List.OfFn
import Mathlib.Data.Nat.Log
import Mathlib.Data.List.Forall2

/-! The graph decomposition at the paper's doubly exponential scales, with
integer capacities and an explicit termination condition. Complexity estimates
and the asymptotic simplification of the degree bounds are separate from this
finite existence theorem. -/
namespace GraphChoices.Peeling
open Finset
variable {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]

def scaleNat (i : ℕ) : ℕ := 2^(2^(i+1))

def roundBudget (B i : ℕ) : ℕ := 16*B / scaleNat i

 theorem scaleNat_pos (i : ℕ) : 0 < scaleNat i := by unfold scaleNat; positivity

 theorem scaleNat_succ (i : ℕ) : scaleNat (i+1) = (scaleNat i)^2 := by
  unfold scaleNat
  rw [← pow_mul, pow_succ]

 theorem roundBudget_zero (B : ℕ) : roundBudget B 0 = 4*B := by
  simp only [roundBudget, scaleNat]
  norm_num
  omega

/-- Floor rounding leaves enough slack for the minimum active integer degree. -/
 theorem active_cutoff_at_scale (B i : ℕ) (d : ℝ) (hd : d ≤ 16*B) :
    d / (scaleNat i : ℝ)^2 ≤ (roundBudget B (i+1) + 1 : ℕ) := by
  have hpos := scaleNat_pos (i+1)
  have hdiv : 16*B < (16*B / scaleNat (i+1) + 1) * scaleNat (i+1) := by
    have hm := Nat.mod_lt (16*B) hpos
    have he := Nat.mod_add_div (16*B) (scaleNat (i+1))
    nlinarith
  have hcast : (16*B : ℝ) ≤ ((roundBudget B (i+1) + 1 : ℕ) : ℝ) * (scaleNat i : ℝ)^2 := by
    have he : scaleNat (i+1) = scaleNat i ^ 2 := scaleNat_succ i
    have hr : ((16*B : ℕ) : ℝ) < ((16*B / scaleNat (i+1) + 1 : ℕ) : ℝ) * (scaleNat (i+1) : ℝ) := by
      exact_mod_cast hdiv
    simpa [roundBudget, he] using hr.le
  have hscale : (0:ℝ) < (scaleNat i : ℝ) := by exact_mod_cast scaleNat_pos i
  apply (div_le_iff₀ (sq_pos_of_pos hscale)).mpr
  exact hd.trans hcast

noncomputable def skewSchedule (G : Graph L R) (B h : ℕ) (d n : ℝ) : List (ℕ × ℕ) :=
  List.ofFn fun i : Fin h =>
    (roundBudget B (i.val+1), scaleCapacity G d n (scaleNat i.val))

 theorem skewSchedule_length (G : Graph L R) (B h : ℕ) (d n : ℝ) :
    (skewSchedule G B h d n).length = h := by simp [skewSchedule]

 theorem skewSchedule_expands (G : Graph L R) (B h : ℕ) (d n : ℝ)
    (hd : 0 < d) (hn : 1 < Real.log n)
    (hleft : ∀ u, (leftDegree G u : ℝ) ≤ d * Real.log n) (hB : d ≤ 16*B) :
    ∀ kb ∈ skewSchedule G B h d n, PeelingExpansion G kb.1 kb.2 := by
  intro kb hkb
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hkb
  apply peelingExpansion_of_graphLogSkewness G _ d n (scaleNat i.val) hd _ hn hleft
    (active_cutoff_at_scale B i.val d hB)
  exact_mod_cast (scaleNat_pos i.val)

/-- A zero cutoff in the last round makes the schedule end at zero. -/
 theorem finalBudget_append (D : ℕ) (ss : List (ℕ × ℕ)) (kb : ℕ × ℕ) :
    finalBudget D (ss ++ [kb]) = kb.1 := by
  induction ss generalizing D with
  | nil => rfl
  | cons a ss ih => exact ih a.1

 theorem skewSchedule_finalBudget (G : Graph L R) (B h : ℕ) (d n : ℝ) :
    finalBudget (roundBudget B 0) (skewSchedule G B h d n) = roundBudget B h := by
  induction h with
  | zero => simp [skewSchedule, finalBudget]
  | succ h ih =>
    unfold skewSchedule
    rw [List.ofFn_succ']
    simp only [List.concat_eq_append]
    rw [finalBudget_append]
    rfl

/-- Concrete doubly exponential decomposition. There is one piece for each
scale 2^(2^(i+1)); their exact integer degree caps are recorded by pieceBudgets.
The condition 16 B < scaleNat h certifies that all edges have been extracted. -/
 theorem exists_doubly_exponential_decomposition (G : Graph L R) (B h : ℕ) (d n : ℝ)
    (hd : 0 < d) (hn : 1 < Real.log n)
    (hleft : ∀ u, (leftDegree G u : ℝ) ≤ d * Real.log n)
    (hB : d ≤ 16*B) (hD : ∀ u, leftDegree G u ≤ 4*B)
    (hstop : 16*B < scaleNat h) :
    ∃ Ps : List (Graph L R), Ps.length = h ∧ Ps.Pairwise Disjoint ∧
      unionPieces Ps = G ∧
      List.Forall₂ (fun P kb => (∀ u, leftDegree P u ≤ kb.1) ∧
        (∀ v, rightDegree P v ≤ kb.2)) Ps
        (pieceBudgets (4*B) (skewSchedule G B h d n)) := by
  have hfinal : finalBudget (4*B) (skewSchedule G B h d n) = 0 := by
    rw [← roundBudget_zero B, skewSchedule_finalBudget]
    exact Nat.div_eq_of_lt hstop
  obtain ⟨Ps,hlen,hdisj,hcover,hbounds⟩ := exists_edge_partition G (4*B) hD
    (skewSchedule G B h d n) (skewSchedule_expands G B h d n hd hn hleft hB) hfinal
  exact ⟨Ps,hlen.trans (skewSchedule_length G B h d n),hdisj,hcover,hbounds⟩

theorem pieceBudgets_append (D : ℕ) (ss : List (ℕ × ℕ)) (kb : ℕ × ℕ) :
    pieceBudgets D (ss ++ [kb]) = pieceBudgets D ss ++
      [(finalBudget D ss, finalBudget D ss * kb.2)] := by
  induction ss generalizing D with
  | nil => rfl
  | cons a ss ih => simpa [pieceBudgets, finalBudget] using congrArg (List.cons (D,D*a.2)) (ih a.1)

/-- The generic iteration certificate has exactly the intended scale-by-scale
integer degree caps. -/
theorem pieceBudgets_skewSchedule (G : Graph L R) (B h : ℕ) (d n : ℝ) :
    pieceBudgets (4*B) (skewSchedule G B h d n) =
      List.ofFn (fun i : Fin h => (roundBudget B i.val,
        roundBudget B i.val * scaleCapacity G d n (scaleNat i.val))) := by
  induction h with
  | zero => simp [skewSchedule, pieceBudgets]
  | succ h ih =>
    have heq : skewSchedule G B (h+1) d n = skewSchedule G B h d n ++
        [(roundBudget B (h+1), scaleCapacity G d n (scaleNat h))] := by
      unfold skewSchedule
      rw [List.ofFn_succ']
      simp only [List.concat_eq_append]
      rfl
    rw [heq, pieceBudgets_append, ih]
    have hfinal : finalBudget (4*B) (skewSchedule G B h d n) = roundBudget B h := by
      rw [← roundBudget_zero B, skewSchedule_finalBudget]
    rw [hfinal, List.ofFn_succ']
    simp only [List.concat_eq_append]
    rfl

theorem scaleNat_ge_two (i : ℕ) : 2 ≤ scaleNat i := by
  have hp : 1 ≤ 2^(i+1) := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by decide))
  simpa [scaleNat] using Nat.pow_le_pow_right (by decide : 0 < 2) hp

theorem roundBudget_mul_scale (B i : ℕ) : roundBudget B i * scaleNat i ≤ 16*B :=
  Nat.div_mul_le_self _ _

theorem roundBudget_real_le (B i : ℕ) :
    (roundBudget B i : ℝ) ≤ (16*B : ℝ) / scaleNat i := by
  have hp : (0:ℝ) < scaleNat i := by exact_mod_cast scaleNat_pos i
  apply (le_div_iff₀ hp).mpr
  exact_mod_cast roundBudget_mul_scale B i

/-- Integer rounding of the right capacity costs no extra constant, since each
scale is at least two and the unrounded right-capacity factor is at least one. -/
theorem rounded_capacity_product (B i : ℕ) (Q : ℝ) (hQ : 1 ≤ Q) :
    ((roundBudget B i * ⌈Q⌉₊ : ℕ) : ℝ) ≤ 16*B*Q := by
  have hscale : (2:ℝ) ≤ scaleNat i := by exact_mod_cast scaleNat_ge_two i
  have hmul : (roundBudget B i : ℝ) * scaleNat i ≤ 16*B := by
    exact_mod_cast roundBudget_mul_scale B i
  have hnonneg : (0:ℝ) ≤ roundBudget B i := Nat.cast_nonneg _
  have hsmall : (roundBudget B i : ℝ)*2 ≤ 16*B := by nlinarith
  have hceil : (⌈Q⌉₊ : ℝ) ≤ 2*Q := by
    have hh := Nat.ceil_lt_add_one (by linarith : 0 ≤ Q)
    linarith
  calc
    _ = (roundBudget B i : ℝ) * (⌈Q⌉₊ : ℝ) := by norm_cast
    _ ≤ (roundBudget B i : ℝ) * (2*Q) := mul_le_mul_of_nonneg_left hceil hnonneg
    _ = ((roundBudget B i : ℝ)*2)*Q := by ring
    _ ≤ 16*B*Q := mul_le_mul_of_nonneg_right hsmall (by linarith)

/-- An explicit log-log number of matching-extraction rounds. -/
def numberRounds (B : ℕ) : ℕ := Nat.log 2 (Nat.log 2 (16*B) + 1)

 theorem numberRounds_suffices (B : ℕ) : 16*B < scaleNat (numberRounds B) := by
  have houter := Nat.lt_pow_succ_log_self (by decide : 1 < 2) (16*B)
  have hinner := Nat.lt_pow_succ_log_self (by decide : 1 < 2) (Nat.log 2 (16*B) + 1)
  exact houter.trans_le (Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.le_of_lt hinner))

/-- A bounded-left-degree graph admits an exact partition with the explicit
log-log piece count; no termination or expansion conclusion is assumed. -/
theorem exists_loglog_skew_decomposition (G : Graph L R) (B : ℕ) (d n : ℝ)
    (hd : 0 < d) (hn : 1 < Real.log n)
    (hleft : ∀ u, (leftDegree G u : ℝ) ≤ d * Real.log n)
    (hB : d ≤ 16*B) (hD : ∀ u, leftDegree G u ≤ 4*B) :
    ∃ Ps : List (Graph L R), Ps.length = numberRounds B ∧ Ps.Pairwise Disjoint ∧
      unionPieces Ps = G ∧
      List.Forall₂ (fun P kb => (∀ u, leftDegree P u ≤ kb.1) ∧
        (∀ v, rightDegree P v ≤ kb.2)) Ps
        (pieceBudgets (4*B) (skewSchedule G B (numberRounds B) d n)) :=
  exists_doubly_exponential_decomposition G B _ d n hd hn hleft hB hD (numberRounds_suffices B)

/-- Structural existence part of the skew-biregular decomposition, stated with
explicit real degree bounds and an exact log-log piece count. -/
theorem exists_skew_biregular_partition (G : Graph L R) (B : ℕ) (d n : ℝ)
    (hd : 0 < d) (hn : 1 < Real.log n)
    (hleft : ∀ u, (leftDegree G u : ℝ) ≤ d * Real.log n)
    (hB : d ≤ 16*B) (hD : ∀ u, leftDegree G u ≤ 4*B) :
    ∃ Ps : List (Graph L R), Ps.length = numberRounds B ∧ Ps.Pairwise Disjoint ∧
      unionPieces Ps = G ∧ ∀ i : Fin Ps.length,
        (∀ u, (leftDegree (Ps.get i) u : ℝ) ≤ 16*B/(scaleNat i.val)) ∧
        (∀ v, (rightDegree (Ps.get i) v : ℝ) ≤
          16*B*((scaleNat i.val : ℝ)*Real.log n)^(2*graphLogSkewness G d n)) := by
  obtain ⟨Ps,hlen,hdisj,hcover,hbounds⟩ := exists_loglog_skew_decomposition G B d n hd hn hleft hB hD
  rw [pieceBudgets_skewSchedule] at hbounds
  refine ⟨Ps,hlen,hdisj,hcover,?_⟩
  intro i
  have hi : i.val < numberRounds B := by rw [← hlen]; exact i.isLt
  have hh := hbounds.get i.isLt (by simp [hi])
  simp only [List.get_eq_getElem, List.getElem_ofFn] at hh
  constructor
  · intro u
    exact (by exact_mod_cast hh.1 u : (leftDegree (Ps.get i) u : ℝ) ≤ roundBudget B i.val).trans
      (roundBudget_real_le B i.val)
  · intro v
    have hQ : (1:ℝ) ≤ ((scaleNat i.val : ℝ)*Real.log n)^(2*graphLogSkewness G d n) := by
      have hs : (2:ℝ) ≤ scaleNat i.val := by exact_mod_cast scaleNat_ge_two i.val
      apply Real.one_le_rpow
      · nlinarith
      · exact mul_nonneg (by norm_num) (graphLogSkewness_nonneg G d n)
    have hright : (rightDegree (Ps.get i) v : ℝ) ≤
        ((roundBudget B i.val * scaleCapacity G d n (scaleNat i.val) : ℕ) : ℝ) := by
      exact_mod_cast hh.2 v
    exact hright.trans (rounded_capacity_product B i.val _ hQ)

end GraphChoices.Peeling
