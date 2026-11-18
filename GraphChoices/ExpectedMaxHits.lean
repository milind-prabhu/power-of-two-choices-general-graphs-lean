import GraphChoices.PreprocessedCompetitive
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.Jensen

/-! An expectation version of the maximum-binomial bound. Jensen and the
exact finite exponential moment avoid any horizon-dependent failure term. -/
namespace GraphChoices
open Finset

theorem exp_average_le {Ω : Type*} [Fintype Ω] [Nonempty Ω] (f : Ω → ℝ) :
    Real.exp (average f) ≤ average (fun ω => Real.exp (f ω)) := by
  have hm : (Fintype.card Ω : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have h := convexOn_exp.map_sum_le (t := (univ : Finset Ω))
    (w := fun _ => (Fintype.card Ω : ℝ)⁻¹) (p := f)
    (fun _ _ => by positivity) (by simp [hm]) (fun _ _ => Set.mem_univ _)
  have havg (g : Ω → ℝ) : (∑ ω, (Fintype.card Ω:ℝ)⁻¹*g ω) = average g := by
    simp only [average, ← mul_sum, div_eq_mul_inv]
    ring
  simp only [smul_eq_mul] at h
  rwa [havg, havg] at h

variable {E : Type*} [Fintype E] [DecidableEq E] [Nonempty E]

theorem average_two_pow_hits (A : Finset E) (T : ℕ) :
    average (fun ω : Fin T → E => (2:ℝ)^(hitCount A ω)) =
      (1+(A.card:ℝ)/Fintype.card E)^T := by
  have hp (ω : Fin T → E) : (2:ℝ)^(hitCount A ω) =
      ∏ t, if ω t ∈ A then (2:ℝ) else 1 := by
    simp only [prod_ite, prod_const_one, mul_one, prod_const, hitCount]
  have hs : (∑ e : E, if e ∈ A then (2:ℝ) else 1) = Fintype.card E+A.card := by
    have hh (e : E) : (if e ∈ A then (2:ℝ) else 1) = 1+(if e ∈ A then 1 else 0) := by
      split <;> norm_num
    calc
      _ = ∑ e : E, (1+(if e ∈ A then (1:ℝ) else 0)) := sum_congr rfl (fun e _ => hh e)
      _ = _ := by
        simp only [sum_add_distrib, sum_const, card_univ, nsmul_eq_mul, mul_one, sum_boole]
        congr 3
        ext e
        simp
  simp only [average, hp]
  rw [← Fintype.prod_sum (fun (_ : Fin T) (e : E) => if e ∈ A then (2:ℝ) else 1)]
  simp only [hs, prod_const, card_univ,
    Fintype.card_fin, Fintype.card_fun, Nat.cast_pow, ← div_pow]
  have hm : (Fintype.card E:ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  congr 1
  field_simp

theorem average_two_pow_hits_le (A : Finset E) (T : ℕ) (μ : ℝ)
    (hmean : (T:ℝ)*((A.card:ℝ)/Fintype.card E) ≤ μ) :
    average (fun ω : Fin T → E => (2:ℝ)^(hitCount A ω)) ≤ Real.exp μ := by
  rw [average_two_pow_hits]
  calc
    _ ≤ (Real.exp ((A.card:ℝ)/Fintype.card E))^T :=
      pow_le_pow_left₀ (by positivity) (by simpa only [add_comm] using Real.add_one_le_exp ((A.card:ℝ)/Fintype.card E)) T
    _ = Real.exp ((T:ℝ)*((A.card:ℝ)/Fintype.card E)) := (Real.exp_nat_mul _ T).symm
    _ ≤ _ := Real.exp_le_exp.mpr hmean

/-- Every bucket may overlap other buckets; only its marginal mean matters. -/
theorem expected_max_hits {I : Type*} [Fintype I] [Nonempty I]
    (bucket : I → Finset E) (T : ℕ) (μ : ℝ)
    (hmean : ∀ i, (T:ℝ)*(((bucket i).card:ℝ)/Fintype.card E) ≤ μ) :
    average (fun ω : Fin T → E => ((univ.sup fun i => hitCount (bucket i) ω : ℕ):ℝ)) ≤
      2*(Real.log (Fintype.card I:ℝ)+μ) := by
  classical
  let X := fun ω : Fin T → E => ((univ.sup fun i => hitCount (bucket i) ω : ℕ):ℝ)
  have hpoint (ω : Fin T → E) : Real.exp (Real.log 2*X ω) ≤
      ∑ i, (2:ℝ)^(hitCount (bucket i) ω) := by
    obtain ⟨i,_,hi⟩ := exists_mem_eq_sup (s := (univ : Finset I)) (by simp) (fun i => hitCount (bucket i) ω)
    have he : Real.exp (Real.log 2*X ω) = (2:ℝ)^(hitCount (bucket i) ω) := by
      dsimp only [X]
      rw [hi, mul_comm, Real.exp_nat_mul, Real.exp_log (by norm_num)]
    rw [he]
    exact single_le_sum (f := fun i => (2:ℝ)^(hitCount (bucket i) ω)) (fun _ _ => by positivity) (mem_univ i)
  have hupper : average (fun ω => Real.exp (Real.log 2*X ω)) ≤
      (Fintype.card I:ℝ)*Real.exp μ := by
    apply (average_mono hpoint).trans
    rw [average_sum]
    simpa using sum_le_sum (fun i (_ : i ∈ (univ : Finset I)) => average_two_pow_hits_le (bucket i) T μ (hmean i))
  have hj := exp_average_le (fun ω => Real.log 2*X ω)
  rw [average_mul] at hj
  have hexp := hj.trans hupper
  have hcard : (0:ℝ) < Fintype.card I := by exact_mod_cast Fintype.card_pos
  rw [← Real.exp_log hcard, ← Real.exp_add, Real.exp_le_exp] at hexp
  have hX' : 0 ≤ average X := by unfold average X; positivity
  have hl2 : (1:ℝ)/2 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  change average X ≤ _
  nlinarith [mul_le_mul_of_nonneg_right hl2 hX']

end GraphChoices
