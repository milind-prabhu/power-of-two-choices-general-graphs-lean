import GraphChoices.CanonicalCoverage

/-! Completely instantiated finite component tails. The sampled-degree cutoff
is chosen from an actual source-bucket bound and the logarithmic polynomial
cutoff, so neither a mean inequality nor a canonical-coverage premise is left.
-/
namespace GraphChoices.Patterns
open Finset
open ThresholdGreedy
variable {E L R C : Type*} [Fintype E] [DecidableEq E] [Nonempty E]
  [Fintype L] [Fintype R] [Fintype C]
  [DecidableEq L] [DecidableEq R] [DecidableEq C]

noncomputable def sampledDegreeCutoff (M T N c : ℕ) : ℕ :=
  ⌈2*Real.exp 1*T*(M:ℝ)/Fintype.card E⌉₊ + polynomialCutoff N c

theorem sampledDegreeCutoff_ge (M T N c : ℕ) :
    polynomialCutoff N c ≤ sampledDegreeCutoff (E := E) M T N c + 1 := by
  unfold sampledDegreeCutoff
  omega

theorem sampledDegreeCutoff_mean (encode : E → Arrival L R C) (M T N c : ℕ)
    (hM : ∀ u, (leftSourceBucket encode u).card ≤ M) :
    ∀ u, Real.exp 1*T*(((leftSourceBucket encode u).card : ℝ)/Fintype.card E)/
      ((sampledDegreeCutoff (E := E) M T N c : ℕ)+1 : ℝ) ≤ 1/2 := by
  intro u
  have hbucket : ((leftSourceBucket encode u).card : ℝ) ≤ M := by exact_mod_cast hM u
  have hmean := mul_le_mul_of_nonneg_left
    (div_le_div_of_nonneg_right hbucket (Nat.cast_nonneg (Fintype.card E)))
    (show 0 ≤ Real.exp 1*(T:ℝ) by positivity)
  have hc := Nat.le_ceil (2*Real.exp 1*T*(M:ℝ)/Fintype.card E)
  have hcut : ⌈2*Real.exp 1*T*(M:ℝ)/Fintype.card E⌉₊ ≤ sampledDegreeCutoff (E := E) M T N c := by
    unfold sampledDegreeCutoff
    omega
  have hcut' : (⌈2*Real.exp 1*T*(M:ℝ)/Fintype.card E⌉₊ : ℝ) ≤ sampledDegreeCutoff (E := E) M T N c := by
    exact_mod_cast hcut
  apply (div_le_iff₀ (by positivity : (0:ℝ) < (sampledDegreeCutoff (E := E) M T N c : ℝ)+1)).mpr
  have heq : Real.exp 1*T*((M:ℝ)/Fintype.card E) = Real.exp 1*T*(M:ℝ)/Fintype.card E := by ring
  rw [heq] at hmean
  have htwo : 2*(Real.exp 1*T*(M:ℝ)/Fintype.card E) ≤
      (⌈2*Real.exp 1*T*(M:ℝ)/Fintype.card E⌉₊ : ℝ) := by
    convert hc using 1 <;> ring
  linarith

/-- Actual component failure at most 3/N^c with a concrete cutoff. The graph
and sampling degree bounds are explicit input data, not probability premises. -/
theorem concrete_component_tail (H : C → Peeling.Graph L R)
    (encode : E → Arrival L R C) (DL DR : C → ℕ) (D M T N c : ℕ) (f : C → ℝ)
    (hsimple : Function.Injective fun e => ((encode e).left,(encode e).right))
    (hsource : ∀ e, ((encode e).left, (encode e).right) ∈ H (encode e).cls)
    (hDL : ∀ u a, (sourceBucket encode u a).card ≤ DL a)
    (hL : ∀ a u, Peeling.leftDegree (H a) u ≤ D)
    (hR : ∀ a v, Peeling.rightDegree (H a) v ≤ DR a)
    (hM : ∀ u, (leftSourceBucket encode u).card ≤ M)
    (hT : 0 < T) (hf : ∀ a, 1 < f a)
    (hN : 0 < N) (hLN : Fintype.card L ≤ N) (hRN : Fintype.card R ≤ N) :
    eventProbability (largeComponentEvent encode (automaticThresholds (E := E) DL DR D T f)
      T ((sampledDegreeCutoff (E := E) M T N c+1)*(polynomialCutoff N c+1))) ≤ 3/(N:ℝ)^c :=
  largeComponent_polynomial_automatic H encode DL DR D T _ _ N c f hsimple hsource hDL hL hR hT hf
    hN hLN hRN (sampledDegreeCutoff_ge M T N c) le_rfl (sampledDegreeCutoff_mean encode M T N c hM)

theorem concrete_expected_load (H : C → Peeling.Graph L R)
    (encode : E → Arrival L R C) (DL DR : C → ℕ) (D M T N c : ℕ) (f : C → ℝ)
    (hsimple : Function.Injective fun e => ((encode e).left,(encode e).right))
    (hsource : ∀ e, ((encode e).left, (encode e).right) ∈ H (encode e).cls)
    (hDL : ∀ u a, (sourceBucket encode u a).card ≤ DL a)
    (hL : ∀ a u, Peeling.leftDegree (H a) u ≤ D)
    (hR : ∀ a v, Peeling.rightDegree (H a) v ≤ DR a)
    (hM : ∀ u, (leftSourceBucket encode u).card ≤ M)
    (hT : 0 < T) (hf : ∀ a, 1 < f a)
    (hN : 0 < N) (hLN : Fintype.card L ≤ N) (hRN : Fintype.card R ≤ N) :
    expectedTotalMaxLoad encode (automaticThresholds (E := E) DL DR D T f) T ≤
      (∑ a, (automaticThresholds (E := E) DL DR D T f a : ℝ)) +
      (2*(Nat.log 2 ((sampledDegreeCutoff (E := E) M T N c+1)*(polynomialCutoff N c+1))+1) : ℕ)*
        expectedReplayOpt encode T + 3*T/(N:ℝ)^c :=
  expected_load_polynomial_automatic H encode DL DR D T _ _ N c f hsimple hsource hDL hL hR hT hf
    hN hLN hRN (sampledDegreeCutoff_ge M T N c) le_rfl (sampledDegreeCutoff_mean encode M T N c hM)

theorem sampledDegreeCutoff_le_three_cutoffs (M T N c : ℕ)
    (hmean : Real.exp 1*T*(M:ℝ)/Fintype.card E ≤ (polynomialCutoff N c : ℝ)) :
    sampledDegreeCutoff (E := E) M T N c ≤ 3*polynomialCutoff N c := by
  have hceil : ⌈2*Real.exp 1*T*(M:ℝ)/Fintype.card E⌉₊ ≤ 2*polynomialCutoff N c := by
    apply Nat.ceil_le.mpr
    push_cast
    calc
      _ = 2*(Real.exp 1*T*(M:ℝ)/Fintype.card E) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hmean (by norm_num)
  unfold sampledDegreeCutoff
  omega

theorem largeComponentEvent_antitone (encode : E → Arrival L R C) (α : C → ℕ)
    (T a b : ℕ) (hab : a ≤ b) :
    largeComponentEvent encode α T b ⊆ largeComponentEvent encode α T a := by
  classical
  intro ω hω
  obtain ⟨v, hv⟩ := (mem_filter.mp hω).2
  exact mem_filter.mpr ⟨mem_univ _, v, hab.trans_lt hv⟩

/-- The log-squared component bound, with all tree-coverage and numerical
tail conditions discharged. The sole additional mean condition is an explicit
upper bound on the expected sampled left degree (including its factor e). -/
theorem log_squared_component_tail (H : C → Peeling.Graph L R)
    (encode : E → Arrival L R C) (DL DR : C → ℕ) (D M T N c : ℕ) (f : C → ℝ)
    (hsimple : Function.Injective fun e => ((encode e).left,(encode e).right))
    (hsource : ∀ e, ((encode e).left, (encode e).right) ∈ H (encode e).cls)
    (hDL : ∀ u a, (sourceBucket encode u a).card ≤ DL a)
    (hL : ∀ a u, Peeling.leftDegree (H a) u ≤ D)
    (hR : ∀ a v, Peeling.rightDegree (H a) v ≤ DR a)
    (hM : ∀ u, (leftSourceBucket encode u).card ≤ M)
    (hT : 0 < T) (hf : ∀ a, 1 < f a)
    (hN : 0 < N) (hLN : Fintype.card L ≤ N) (hRN : Fintype.card R ≤ N)
    (hmean : Real.exp 1*T*(M:ℝ)/Fintype.card E ≤ (polynomialCutoff N c : ℝ)) :
    eventProbability (largeComponentEvent encode (automaticThresholds (E := E) DL DR D T f)
      T (3*(polynomialCutoff N c+1)^2)) ≤ 3/(N:ℝ)^c := by
  have hd := sampledDegreeCutoff_le_three_cutoffs M T N c hmean
  have hsize : (sampledDegreeCutoff (E := E) M T N c+1)*(polynomialCutoff N c+1) ≤
      3*(polynomialCutoff N c+1)^2 := by
    have hm := Nat.mul_le_mul_right (polynomialCutoff N c+1) (Nat.add_le_add_right hd 1)
    nlinarith
  apply (eventProbability_mono (largeComponentEvent_antitone encode _ T _ _ hsize)).trans
  exact concrete_component_tail H encode DL DR D M T N c f hsimple hsource hDL hL hR hM hT hf hN hLN hRN

theorem log_squared_expected_load (H : C → Peeling.Graph L R)
    (encode : E → Arrival L R C) (DL DR : C → ℕ) (D M T N c : ℕ) (f : C → ℝ)
    (hsimple : Function.Injective fun e => ((encode e).left,(encode e).right))
    (hsource : ∀ e, ((encode e).left, (encode e).right) ∈ H (encode e).cls)
    (hDL : ∀ u a, (sourceBucket encode u a).card ≤ DL a)
    (hL : ∀ a u, Peeling.leftDegree (H a) u ≤ D)
    (hR : ∀ a v, Peeling.rightDegree (H a) v ≤ DR a)
    (hM : ∀ u, (leftSourceBucket encode u).card ≤ M)
    (hT : 0 < T) (hf : ∀ a, 1 < f a)
    (hN : 0 < N) (hLN : Fintype.card L ≤ N) (hRN : Fintype.card R ≤ N)
    (hmean : Real.exp 1*T*(M:ℝ)/Fintype.card E ≤ (polynomialCutoff N c : ℝ)) :
    expectedTotalMaxLoad encode (automaticThresholds (E := E) DL DR D T f) T ≤
      (∑ a, (automaticThresholds (E := E) DL DR D T f a : ℝ)) +
      (2*(Nat.log 2 (3*(polynomialCutoff N c+1)^2)+1) : ℕ)*expectedReplayOpt encode T + 3*T/(N:ℝ)^c := by
  have ht := log_squared_component_tail H encode DL DR D M T N c f hsimple hsource hDL hL hR hM hT hf
    hN hLN hRN hmean
  have h := expected_load_of_component_tail encode _ T _ _ ht
  convert h using 1 <;> ring

end GraphChoices.Patterns
