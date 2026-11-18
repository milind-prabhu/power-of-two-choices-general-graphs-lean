import GraphChoices.BudgetSimplification

/-! Explicit integer log-log bounds for the number of decomposition classes
and the Greedy multiplier after component shattering. -/
namespace GraphChoices

def iteratedLog (N : ℕ) : ℕ := Nat.log 2 (Nat.log 2 N+1)+1

theorem iteratedLog_pos (N : ℕ) : 0 < iteratedLog N := by unfold iteratedLog; omega

theorem nat_log_mul_two_pow (a k : ℕ) (ha : 0 < a) : Nat.log 2 (a*2^k) = Nat.log 2 a+k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ← mul_assoc, Nat.log_mul_base (by decide) (by positivity), ih]
    omega

theorem nat_log_square_bound (a : ℕ) : Nat.log 2 (a^2)+1 ≤ 2*(Nat.log 2 a+1) := by
  by_cases ha : a = 0
  · simp [ha]
  have hp := Nat.lt_pow_succ_log_self (by decide : 1 < 2) a
  have hs : a^2 < 2^(2*(Nat.log 2 a+1)) := by
    calc
      _ < (2^(Nat.log 2 a+1))^2 := Nat.pow_lt_pow_left hp (by decide)
      _ = _ := by rw [← pow_mul]; congr 1; omega
  have hh := Nat.log_lt_of_lt_pow (pow_ne_zero 2 ha) hs
  omega

theorem numberRounds_le_iteratedLog (B N : ℕ) (hN : 0 < N) (hB : B ≤ N^2) :
    Peeling.numberRounds B ≤ iteratedLog N+2 := by
  by_cases hB0 : B = 0
  · simp [hB0, Peeling.numberRounds]
  let l := Nat.log 2 N+1
  have hl : 1 ≤ l := by dsimp [l]; omega
  have hpow := Nat.lt_pow_succ_log_self (by decide : 1 < 2) N
  have hbound : 16*B < 2^(2*l+4) := by
    calc
      _ ≤ 16*N^2 := Nat.mul_le_mul_left _ hB
      _ < 16*(2^l)^2 := Nat.mul_lt_mul_of_pos_left (Nat.pow_lt_pow_left hpow (by decide)) (by decide)
      _ = _ := by
        have he : 2^(2*l+4) = (2^l)^2*16 := by
          rw [pow_add, show 2*l = l*2 by omega, pow_mul]
          norm_num
        rw [he]
        ring
  have hin := Nat.log_lt_of_lt_pow (by positivity : 16*B ≠ 0) hbound
  have hinner : Nat.log 2 (16*B)+1 ≤ 8*l := by omega
  have hmono := Nat.log_mono_right hinner (b := 2)
  have heq : Nat.log 2 (8*l) = Nat.log 2 l+3 := by
    simpa only [show 2^3 = 8 by norm_num, mul_comm] using nat_log_mul_two_pow l 3 (by omega)
  unfold Peeling.numberRounds
  rw [heq] at hmono
  change Nat.log 2 (Nat.log 2 (16*B)+1) ≤ Nat.log 2 l+1+2
  omega

theorem real_loglog_le_iteratedLog (N : ℕ) (hlog : 1 < Real.log (N:ℝ)) :
    Real.log (Real.log (N:ℝ)) ≤ (iteratedLog N : ℝ) := by
  have hN : 0 < N := by
    by_contra hn
    have hz : N = 0 := by omega
    norm_num [hz] at hlog
  have hl := Patterns.real_log_le_nat_log_shift N hN
  have hpos : 0 < Real.log (N:ℝ) := by linarith
  have hh := Real.log_le_log hpos hl
  exact hh.trans (Patterns.real_log_le_nat_log_shift (Nat.log 2 N+1) (by omega))

theorem greedy_multiplier_le_iteratedLog (N : ℕ) :
    2*(Nat.log 2 (3*(polynomialCutoff N 5+1)^2)+1) ≤ 20*iteratedLog N := by
  let l := Nat.log 2 N+1
  have hl : 1 ≤ l := by dsimp [l]; omega
  have hl2 : l ≤ l*l := Nat.le_mul_self l
  have hsize : 3*(6*l+1)^2 ≤ (16*l)^2 := by nlinarith
  have hmono := Nat.log_mono_right hsize (b := 2)
  have hsquare := nat_log_square_bound (16*l)
  have hlog : Nat.log 2 (16*l) = Nat.log 2 l+4 := by
    simpa only [show 2^4 = 16 by norm_num, mul_comm] using nat_log_mul_two_pow l 4 (by omega)
  rw [hlog] at hsquare
  change 2*(Nat.log 2 (3*(6*l+1)^2)+1) ≤ 20*(Nat.log 2 l+1)
  omega

theorem exceptional_error_le_three (N : ℕ) (hN : 0 < N) : 3*(N:ℝ)/(N:ℝ)^5 ≤ 3 := by
  have hNr : (0:ℝ) < N := by exact_mod_cast hN
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hp : (1:ℝ) ≤ (N:ℝ)^4 := one_le_pow₀ hN1
  calc
    _ = 3/(N:ℝ)^4 := by rw [pow_succ]; field_simp
    _ ≤ 3 := (div_le_iff₀ (by positivity)).mpr (by linarith)

end GraphChoices

namespace GraphChoices.Peeling
open Patterns
variable {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
  {G : Graph L R} {B N : ℕ} {d : ℝ} [Nonempty G]

theorem PreparedDecomposition.budget_loglog (P : PreparedDecomposition G B N d)
    (hB : B ≤ N^2) (haverage : 2*(G.card : ℝ) = (N:ℝ)*d) :
    P.budget N ≤ 320*((B:ℝ)*((N:ℝ)/Fintype.card G)+graphLogSkewness G d (N:ℝ)+1)*(iteratedLog N : ℝ) := by
  have hn : P.pieces.length ≤ iteratedLog N+2 := by
    rw [P.count]
    exact numberRounds_le_iteratedLog B N P.vertex_count_pos hB
  have hnr : (P.pieces.length : ℝ) ≤ (iteratedLog N : ℝ)+2 := by exact_mod_cast hn
  have hQ : (1:ℝ) ≤ iteratedLog N := by exact_mod_cast iteratedLog_pos N
  have hl := real_loglog_le_iteratedLog N P.large_log
  have hs := graphLogSkewness_nonneg G d (N:ℝ)
  have hfactor : (P.pieces.length : ℝ)+Real.log (Real.log (N:ℝ))+1 ≤ 5*(iteratedLog N : ℝ) := by linarith
  calc
    _ ≤ _ := P.budget_simplified haverage
    _ ≤ 64*((B:ℝ)*((N:ℝ)/Fintype.card G)+graphLogSkewness G d (N:ℝ)+1)*(5*(iteratedLog N : ℝ)) :=
      mul_le_mul_of_nonneg_left hfactor (by positivity)
    _ = _ := by ring

end GraphChoices.Peeling
