import GraphChoices.BlockSampling
import GraphChoices.ComponentExpectation

/-! Pairwise occupancy bounds suffice for expected density. The quadratic
minorant below replaces a high-probability negative-association argument. -/
namespace GraphChoices
open Finset

theorem average_sub {Ω : Type*} [Fintype Ω] (f g : Ω → ℝ) :
    average (fun ω => f ω - g ω) = average f - average g := by
  simp [average, sum_sub_distrib, sub_div]

theorem average_div {Ω : Type*} [Fintype Ω] (f : Ω → ℝ) (a : ℝ) :
    average (fun ω => f ω / a) = average f / a := by
  simp only [average, div_eq_mul_inv, ← sum_mul]
  ring

noncomputable def successNumber {I Ω : Type*} [Fintype I] [DecidableEq Ω]
    (events : I → Finset Ω) (ω : Ω) : ℝ := ∑ i, if ω ∈ events i then 1 else 0

theorem successNumber_nonneg {I Ω : Type*} [Fintype I] [DecidableEq Ω]
    (events : I → Finset Ω) (ω : Ω) : 0 ≤ successNumber events ω := by
  exact sum_nonneg fun _ _ => by split <;> norm_num

theorem average_successNumber {I Ω : Type*} [Fintype I] [Fintype Ω] [DecidableEq Ω]
    (events : I → Finset Ω) :
    average (successNumber events) = ∑ i, eventProbability (events i) := by
  unfold successNumber
  rw [average_sum]
  simp_rw [average_unit_indicator]

theorem average_indicator_product {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (A B : Finset Ω) :
    average (fun ω => (if ω ∈ A then (1 : ℝ) else 0) *
      (if ω ∈ B then (1 : ℝ) else 0)) = eventProbability (A ∩ B) := by
  rw [← average_unit_indicator]
  congr 1
  funext ω
  by_cases hA : ω ∈ A <;> by_cases hB : ω ∈ B <;> simp [hA, hB]

theorem successNumber_second_moment {I Ω : Type*} [Fintype I] [Fintype Ω]
    [DecidableEq Ω] (events : I → Finset Ω)
    (hcov : ∀ i j, i ≠ j → eventProbability (events i ∩ events j) ≤
      eventProbability (events i) * eventProbability (events j)) :
    average (fun ω => (successNumber events ω)^2) ≤
      (∑ i, eventProbability (events i))^2 + ∑ i, eventProbability (events i) := by
  classical
  have heq (ω : Ω) : (successNumber events ω)^2 =
      ∑ i, ∑ j, (if ω ∈ events i then (1 : ℝ) else 0) *
        (if ω ∈ events j then (1 : ℝ) else 0) := by
    simp only [successNumber, pow_two, sum_mul, mul_sum]
    rw [sum_comm]
  simp_rw [heq, average_sum, average_indicator_product]
  calc
    _ ≤ ∑ i, ∑ j, (eventProbability (events i) * eventProbability (events j) +
        if i = j then eventProbability (events i) else 0) := by
      apply sum_le_sum
      intro i _
      apply sum_le_sum
      intro j _
      by_cases hij : i = j
      · subst j
        simp only [inter_self, if_true]
        nlinarith [sq_nonneg (eventProbability (events i))]
      · simpa only [if_neg hij, add_zero] using hcov i j hij
    _ = _ := by simp [sum_add_distrib, ← mul_sum, ← sum_mul, pow_two]

theorem density_quadratic_lower {z r f k a : ℝ}
    (hz : 0 ≤ z) (hr : 0 < r) (hk : 0 ≤ k) (ha : 0 < a)
    (hdensity : k*z ≤ (z+r)*f) :
    k*(2*z/a - (z^2+r*z)/a^2) ≤ f := by
  have hzr : 0 < z+r := by linarith
  have hf : k*z/(z+r) ≤ f := (div_le_iff₀ hzr).mpr (by simpa only [mul_comm f] using hdensity)
  apply le_trans _ hf
  apply (le_div_iff₀ hzr).mpr
  have ha2 : 0 < a^2 := sq_pos_of_pos ha
  apply (le_of_mul_le_mul_right (a := a^2) ?_ ha2)
  have heq : (k*(2*z/a - (z^2+r*z)/a^2)*(z+r)) * a^2 =
      k*(2*z*a - (z^2+r*z))*(z+r) := by field_simp <;> ring
  rw [heq]
  nlinarith [mul_nonneg (mul_nonneg hk hz) (sq_nonneg (a-(z+r)))]

/-- If E[Z²] ≤ E[Z]²+E[Z] and E[Z] ≥ r ≥ 1, any sampled
graph with density at least k Z/(Z+r) has expected optimum at least k/3. -/
theorem expected_density_of_second_moment {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (Z f : Ω → ℝ) (k r : ℝ) (hz : ∀ ω, 0 ≤ Z ω) (hk : 0 ≤ k)
    (hr : 1 ≤ r) (hmean : r ≤ average Z)
    (hsecond : average (fun ω => (Z ω)^2) ≤ (average Z)^2 + average Z)
    (hdensity : ∀ ω, k*Z ω ≤ (Z ω+r)*f ω) :
    k/3 ≤ average f := by
  let m := average Z
  let a := m+r+1
  have hm : 1 ≤ m := hr.trans hmean
  have ha : 0 < a := by dsimp [a]; linarith
  have hminor := average_mono fun ω => density_quadratic_lower (hz ω)
    (by linarith : 0 < r) hk ha (hdensity ω)
  rw [average_mul, average_sub, average_div, average_mul, average_div,
    average_add, average_mul] at hminor
  change k*(2*m/a - (average (fun ω => (Z ω)^2)+r*m)/a^2) ≤ average f at hminor
  have hbound : k*m/a ≤ average f := by
    apply le_trans _ hminor
    have ha2 : 0 < a^2 := sq_pos_of_pos ha
    apply (le_of_mul_le_mul_right (a := a^2) ?_ ha2)
    have heq : k*m/a*a^2 = k*m*a := by field_simp <;> ring
    have heq2 : (k*(2*m/a - (average (fun ω => (Z ω)^2)+r*m)/a^2))*a^2 =
        k*(2*m*a - (average (fun ω => (Z ω)^2)+r*m)) := by field_simp <;> ring
    rw [heq, heq2]
    have hh : average (fun ω => (Z ω)^2) ≤ m^2+m := hsecond
    dsimp [a]
    nlinarith [mul_nonneg hk (sub_nonneg.mpr hh)]
  apply le_trans _ hbound
  apply (le_div_iff₀ ha).mpr
  have hma : a ≤ 3*m := by dsimp [a]; linarith
  nlinarith [mul_nonneg hk (sub_nonneg.mpr hma)]

end GraphChoices
