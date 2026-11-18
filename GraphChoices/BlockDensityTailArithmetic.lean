import GraphChoices.CompleteBlockDensity

namespace GraphChoices.LowerBound

/-- The count of vertex subsets cancels against the binomial density tail.
The remaining small-side factor makes the bound polynomially small in m. -/
theorem block_size_pair_bound (m t a b k : ℕ) (hm : 0 < m) (ht : 1 ≤ t)
    (ha : 0 < a) (hb : 0 < b) (ham : a ≤ m) (hbtm : b ≤ t*m) (hk : 16 ≤ k)
    (hscale : Real.exp 1*(t:ℝ)*(2*Real.exp 1/(k:ℝ))^k ≤ 1/256) :
    (m.choose a:ℝ)*((t*m).choose b:ℝ)*
      (2*Real.exp 1*(a:ℝ)*b/((m:ℝ)*k*(a+b)))^(k*(a+b)) ≤ 1/(m:ℝ)^8 := by
  let z := min a b
  let n := a+b
  have hz : 0 < z := lt_min ha hb
  have hzm : z ≤ m := (min_le_left _ _).trans ham
  have hzn : z ≤ n := (min_le_left a b).trans (by dsimp [n]; omega)
  have hmr : (0:ℝ) < m := by exact_mod_cast hm
  have hzr : (0:ℝ) < z := by exact_mod_cast hz
  have hkr : (0:ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have har : (0:ℝ) < a := by exact_mod_cast ha
  have hbr : (0:ℝ) < b := by exact_mod_cast hb
  have htr : (1:ℝ) ≤ t := by exact_mod_cast ht
  have hnr : (0:ℝ) < n := by dsimp [n]; positivity
  let C := Real.exp 1*t*m/z
  let D := 2*Real.exp 1*z/((m:ℝ)*k)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hca : (m.choose a:ℝ) ≤ C^a := by
    apply (choose_le_exp_div_pow m a).trans
    apply pow_le_pow_left₀ (by positivity)
    dsimp [C]
    have hza : (z:ℝ) ≤ a := by dsimp only [z]; exact_mod_cast min_le_left a b
    calc
      _ ≤ Real.exp 1*m/z := div_le_div_of_nonneg_left (by positivity) hzr hza
      _ ≤ _ := by
        have hh := mul_le_mul_of_nonneg_right htr (show 0 ≤ Real.exp 1*m/z by positivity)
        convert hh using 1 <;> ring
  have hcb : ((t*m).choose b:ℝ) ≤ C^b := by
    apply (choose_le_exp_div_pow (t*m) b).trans
    apply pow_le_pow_left₀ (by positivity)
    dsimp [C]
    push_cast
    have hzb : (z:ℝ) ≤ b := by dsimp only [z]; exact_mod_cast min_le_right a b
    convert div_le_div_of_nonneg_left (show 0 ≤ Real.exp 1*(t:ℝ)*m by positivity) hzr hzb using 1 <;> ring
  have htail : 2*Real.exp 1*(a:ℝ)*b/((m:ℝ)*k*(a+b)) ≤ D := by
    dsimp [D]
    apply (div_le_div_iff₀ (by positivity : (0:ℝ)<(m:ℝ)*k*(a+b)) (by positivity : (0:ℝ)<(m:ℝ)*k)).mpr
    have hab : (a:ℝ)*b ≤ (z:ℝ)*(a+b) := by
      by_cases hh : a ≤ b
      · have he : z = a := min_eq_left hh
        rw [he]
        nlinarith
      · have he : z = b := min_eq_right (le_of_not_ge hh)
        rw [he]
        nlinarith
    nlinarith [mul_nonneg (by positivity : 0 ≤ 2*Real.exp 1*m*k) (sub_nonneg.mpr hab)]
  have hfactor : C*D^k = (Real.exp 1*(t:ℝ)*(2*Real.exp 1/(k:ℝ))^k)*((z:ℝ)/m)^(k-1) := by
    have hk' : k = (k-1)+1 := by omega
    have heq : D = (2*Real.exp 1/(k:ℝ))*((z:ℝ)/m) := by dsimp [D]; ring
    have hzpow : ((z:ℝ)/m)^k = ((z:ℝ)/m)^(k-1)*((z:ℝ)/m) := by
      conv_lhs => rw [hk']
      rw [pow_succ]
    rw [heq, mul_pow, hzpow]
    dsimp [C]
    field_simp <;> ring
  have hpow : ((z:ℝ)/m)^((k-1)*n) ≤ ((z:ℝ)/m)^8 := by
    apply pow_le_pow_of_le_one (by positivity) ((div_le_one hmr).mpr (by exact_mod_cast hzm))
    have hn : 2 ≤ n := by dsimp [n]; omega
    have hkm : 15 ≤ k-1 := by omega
    nlinarith
  have hz8 : (z:ℝ)^8 ≤ (256:ℝ)^n := by
    have hz2 : z ≤ 2^z := (Nat.lt_two_pow_self : z < 2^z).le
    have hh : z^8 ≤ 256^n := by
      calc
        _ ≤ (2^z)^8 := Nat.pow_le_pow_left hz2 _
        _ = 256^z := by rw [← pow_mul, Nat.mul_comm z 8, pow_mul]; norm_num
        _ ≤ _ := Nat.pow_le_pow_right (by norm_num) hzn
    exact_mod_cast hh
  calc
    _ ≤ C^a*C^b*D^(k*n) := by
      apply mul_le_mul (mul_le_mul hca hcb (by positivity) (pow_nonneg hC _)) _ (by positivity) (by positivity)
      apply pow_le_pow_left₀ (by positivity) htail
    _ = (C*D^k)^n := by rw [mul_pow, ← pow_mul, ← pow_add]
    _ ≤ ((1/256:ℝ)*((z:ℝ)/m)^(k-1))^n := by
      apply pow_le_pow_left₀ (by positivity)
      rw [hfactor]
      exact mul_le_mul_of_nonneg_right hscale (by positivity)
    _ = (1/256:ℝ)^n*((z:ℝ)/m)^((k-1)*n) := by rw [mul_pow, ← pow_mul]
    _ ≤ (1/256:ℝ)^n*((z:ℝ)/m)^8 := mul_le_mul_of_nonneg_left hpow (by positivity)
    _ ≤ 1/(m:ℝ)^8 := by
      rw [div_pow, div_pow, one_pow]
      have hh : (z:ℝ)^8/(256:ℝ)^n ≤ 1 := (div_le_one (by positivity)).mpr hz8
      calc
        _ = ((z:ℝ)^8/(256:ℝ)^n)/(m:ℝ)^8 := by ring
        _ ≤ _ := div_le_div_of_nonneg_right hh (by positivity)

end GraphChoices.LowerBound
