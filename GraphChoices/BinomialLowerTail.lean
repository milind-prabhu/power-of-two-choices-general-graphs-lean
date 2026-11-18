import GraphChoices.RandomGreedy

namespace GraphChoices
open Finset
variable {E : Type*} [Fintype E] [DecidableEq E] [Nonempty E]

theorem average_pow_hits (A : Finset E) (T : ℕ) (r : ℝ) :
    average (fun ω : Fin T → E => r^(hitCount A ω)) =
      (1+((A.card:ℝ)/Fintype.card E)*(r-1))^T := by
  have hp (ω : Fin T → E) : r^(hitCount A ω) = ∏ t, if ω t ∈ A then r else 1 := by
    simp only [prod_ite, prod_const_one, mul_one, prod_const, hitCount]
  have hfilter : (univ.filter fun e : E => e ∈ A) = A := by ext e; simp
  have hs : (∑ e : E, if e ∈ A then r else 1) = Fintype.card E+(r-1)*A.card := by
    have hh (e : E) : (if e ∈ A then r else 1) = 1+(r-1)*(if e ∈ A then (1:ℝ) else 0) := by
      split <;> ring
    calc
      _ = ∑ e : E, (1+(r-1)*(if e ∈ A then (1:ℝ) else 0)) := sum_congr rfl (fun e _ => hh e)
      _ = _ := by simp only [sum_add_distrib, sum_const, card_univ, nsmul_eq_mul, mul_one, ← mul_sum, sum_boole, hfilter]
  simp only [average, hp]
  rw [← Fintype.prod_sum (fun (_ : Fin T) (e : E) => if e ∈ A then r else 1)]
  simp only [hs, prod_const, card_univ, Fintype.card_fin, Fintype.card_fun, Nat.cast_pow, ← div_pow]
  have hm : (Fintype.card E:ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  congr 1
  field_simp

theorem hitLowerTail_probability (A : Finset E) (T k : ℕ) :
    eventProbability (univ.filter fun ω : Fin T → E => hitCount A ω < k) ≤
      Real.exp ((k:ℝ)*Real.log 2-(T:ℝ)*((A.card:ℝ)/Fintype.card E)/2) := by
  let bad := univ.filter fun ω : Fin T → E => hitCount A ω < k
  have hm : average (fun ω : Fin T → E => (if ω ∈ bad then (1:ℝ) else 0)*(1/2)^k) ≤
      average (fun ω : Fin T → E => (1/2:ℝ)^(hitCount A ω)) := by
    apply average_mono
    intro ω
    split_ifs with hω
    · simp only [one_mul]
      exact pow_le_pow_of_le_one (by norm_num) (by norm_num) ((mem_filter.mp hω).2.le)
    · simp only [zero_mul]
      positivity
  have heq : average (fun ω : Fin T → E => (if ω ∈ bad then (1:ℝ) else 0)*(1/2)^k) =
      (1/2:ℝ)^k*eventProbability bad := by
    conv_lhs => arg 1; ext ω; rw [mul_comm]
    rw [average_mul, average_unit_indicator]
  rw [heq, average_pow_hits] at hm
  have hexp : (1+((A.card:ℝ)/Fintype.card E)*((1/2:ℝ)-1))^T ≤
      Real.exp (-(T:ℝ)*((A.card:ℝ)/Fintype.card E)/2) := by
    have hp : 0 ≤ 1+((A.card:ℝ)/Fintype.card E)*((1/2:ℝ)-1) := by
      have hh : (A.card:ℝ)/Fintype.card E ≤ 1 := eventProbability_le_one A
      linarith
    calc
      _ ≤ (Real.exp (-((A.card:ℝ)/Fintype.card E)/2))^T := by
        apply pow_le_pow_left₀ hp
        have hh := Real.add_one_le_exp (-((A.card:ℝ)/Fintype.card E)/2)
        linarith
      _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring
  have htwo : (1/2:ℝ)^k*Real.exp ((k:ℝ)*Real.log 2) = 1 := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num), ← mul_pow]
    norm_num
  have hh := mul_le_mul_of_nonneg_left (hm.trans hexp) (le_of_lt (Real.exp_pos ((k:ℝ)*Real.log 2)))
  have hright : Real.exp ((k:ℝ)*Real.log 2)*Real.exp (-(T:ℝ)*((A.card:ℝ)/Fintype.card E)/2) =
      Real.exp ((k:ℝ)*Real.log 2-(T:ℝ)*((A.card:ℝ)/Fintype.card E)/2) := by rw [← Real.exp_add]; congr 1; ring
  rw [← mul_assoc, mul_comm (Real.exp _), htwo, one_mul, hright] at hh
  exact hh

theorem coordinate_event_probability {Ω : Type*} [Fintype Ω] [DecidableEq Ω] [Nonempty Ω]
    (B : Finset Ω) {k : ℕ} (i : Fin k) :
    eventProbability (univ.filter fun ω : Fin k → Ω => ω i ∈ B) = eventProbability B := by
  rw [← average_unit_indicator, ← average_unit_indicator B]
  have hh := average_coordinate i (fun x : Ω => if x ∈ B then (1:ℝ) else 0)
  simpa only [mem_filter, mem_univ, true_and] using hh

end GraphChoices
