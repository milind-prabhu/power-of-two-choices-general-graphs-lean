import GraphChoices.ExplicitThresholds
import GraphChoices.LargeShapeTail
import GraphChoices.PolynomialShattering

/-! Concrete rate and branching parameters remove the remaining numerical
decay premises from the canonical-shape tail. These are finite explicit
thresholds; end-to-end component coverage and asymptotic analysis are separate.
-/
namespace GraphChoices.Patterns
open ThresholdGreedy

noncomputable def shapeRate (h : ℕ) : ℝ := 1/(8*h)

noncomputable def branchTarget (D h : ℕ) (z : ℝ) : ℝ := (shapeRate h)^2/((D:ℝ)*z+1)

theorem shapeRate_pos (h : ℕ) (hh : 0 < h) : 0 < shapeRate h := by
  unfold shapeRate
  positivity

theorem shapeRate_le_one (h : ℕ) (hh : 0 < h) : shapeRate h ≤ 1 := by
  have hhr : (1:ℝ) ≤ h := by exact_mod_cast hh
  unfold shapeRate
  apply (div_le_iff₀ (by positivity : (0:ℝ) < 8*h)).mpr
  linarith

theorem shapeRate_class_factor (h : ℕ) (hh : 0 < h) :
    4*(h:ℝ)*shapeRate h = 1/2 := by
  have hne : (h:ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hh
  unfold shapeRate
  field_simp
  ring

theorem branchTarget_pos (D h : ℕ) (z : ℝ) (hh : 0 < h) (hz : 0 ≤ z) :
    0 < branchTarget D h z := by
  unfold branchTarget
  exact div_pos (sq_pos_of_pos (shapeRate_pos h hh)) (by positivity)

theorem branchTarget_le_rate (D h : ℕ) (z : ℝ) (hh : 0 < h) (hz : 0 ≤ z) :
    branchTarget D h z ≤ shapeRate h := by
  have hr := shapeRate_pos h hh
  have hr1 := shapeRate_le_one h hh
  unfold branchTarget
  apply (div_le_iff₀ (by positivity : (0:ℝ) < (D:ℝ)*z+1)).mpr
  have hDz : 0 ≤ (D:ℝ)*z := mul_nonneg (Nat.cast_nonneg _) hz
  have hmul := mul_nonneg hr.le hDz
  nlinarith

theorem branchTarget_pair (D h : ℕ) (z : ℝ) (hh : 0 < h) (hz : 0 ≤ z) :
    (D:ℝ)*z*branchTarget D h z ≤ (shapeRate h)^2 := by
  have hb := (branchTarget_pos D h z hh hz).le
  have heq : branchTarget D h z * ((D:ℝ)*z+1) = (shapeRate h)^2 := by
    unfold branchTarget
    exact div_mul_cancel₀ _ (ne_of_gt (by positivity : (0:ℝ) < (D:ℝ)*z+1))
  nlinarith

variable {E L R C : Type*} [Fintype E] [DecidableEq E] [Nonempty E]
  [Fintype L] [Fintype R] [Fintype C]
  [DecidableEq L] [DecidableEq R] [DecidableEq C]

theorem class_card_pos (encode : E → Arrival L R C) : 0 < Fintype.card C := by
  classical
  exact Fintype.card_pos_iff.mpr ⟨(encode (Classical.choice (inferInstance : Nonempty E))).cls⟩

noncomputable def automaticThresholds (DL DR : C → ℕ) (D T : ℕ) (f : C → ℝ) : C → ℕ :=
  explicitThresholds (E := E) DL DR T f
    (branchTarget D (Fintype.card C) ((T:ℝ)/Fintype.card E))

/-- Canonical-shape geometric decay for an explicit integer threshold vector.
Every local numerical inequality is proved from the parameter definitions. -/
theorem heavyShape_geometric_automatic (H : C → Peeling.Graph L R)
    (encode : E → Arrival L R C) (DL DR : C → ℕ) (D T m : ℕ) (f : C → ℝ)
    (hsimple : Function.Injective fun e => ((encode e).left,(encode e).right))
    (hDL : ∀ u c, (sourceBucket encode u c).card ≤ DL c)
    (hL : ∀ c u, Peeling.leftDegree (H c) u ≤ D)
    (hR : ∀ c v, Peeling.rightDegree (H c) v ≤ DR c)
    (hT : 0 < T) (hf : ∀ c, 1 < f c) :
    eventProbability (heavyShapeEvent H encode (automaticThresholds (E := E) DL DR D T f) T m) ≤
      (Fintype.card R : ℝ)/2^m := by
  have hh := class_card_pos encode
  have hz : 0 ≤ (T:ℝ)/Fintype.card E := by positivity
  have hdec := heavyShape_decay_explicit H encode DL DR D T m f hsimple hDL hL hR
    (branchTarget D (Fintype.card C) ((T:ℝ)/Fintype.card E)) (shapeRate (Fintype.card C)) hT
    (branchTarget_pos _ _ _ hh hz) (shapeRate_pos _ hh).le
    (branchTarget_le_rate _ _ _ hh hz) (branchTarget_pair _ _ _ hh hz) hf
  exact heavyShape_geometric_tail H encode _ T m _ (shapeRate_pos _ hh).le hdec
    (shapeRate_class_factor _ hh).le

theorem largeShape_geometric_automatic (H : C → Peeling.Graph L R)
    (encode : E → Arrival L R C) (DL DR : C → ℕ) (D T k B : ℕ) (f : C → ℝ)
    (hsimple : Function.Injective fun e => ((encode e).left,(encode e).right))
    (hDL : ∀ u c, (sourceBucket encode u c).card ≤ DL c)
    (hL : ∀ c u, Peeling.leftDegree (H c) u ≤ D)
    (hR : ∀ c v, Peeling.rightDegree (H c) v ≤ DR c)
    (hT : 0 < T) (hf : ∀ c, 1 < f c) :
    eventProbability (largeShapeEvent H encode (automaticThresholds (E := E) DL DR D T f) T k B) ≤
      2*(Fintype.card R : ℝ)/2^k := by
  apply largeShape_probability_le
  intro j _
  exact heavyShape_geometric_automatic H encode DL DR D T (k+j) f hsimple hDL hL hR hT hf

/-- Component tail for the concrete threshold vector. The only combinatorial
coverage premise is explicitly visible; no canonical probability bound or
local decay inequality is assumed. D bounds base-piece left degrees, while
d bounds sampled residual left degrees outside the degree exception. -/
theorem largeComponent_polynomial_automatic_of_coverage (H : C → Peeling.Graph L R)
    (encode : E → Arrival L R C) (DL DR : C → ℕ) (D T d k B N c : ℕ) (f : C → ℝ)
    (hsimple : Function.Injective fun e => ((encode e).left,(encode e).right))
    (hDL : ∀ u c, (sourceBucket encode u c).card ≤ DL c)
    (hL : ∀ c u, Peeling.leftDegree (H c) u ≤ D)
    (hR : ∀ c v, Peeling.rightDegree (H c) v ≤ DR c)
    (hT : 0 < T) (hf : ∀ c, 1 < f c)
    (hN : 0 < N) (hLN : Fintype.card L ≤ N) (hRN : Fintype.card R ≤ N)
    (hd : polynomialCutoff N c ≤ d+1) (hk : polynomialCutoff N c ≤ k)
    (hmean : ∀ u, Real.exp 1*T*(((leftSourceBucket encode u).card : ℝ)/Fintype.card E)/(d+1) ≤ 1/2)
    (hcoverage : largeHeavyTreeEvent encode (automaticThresholds (E := E) DL DR D T f) T k ⊆
      largeShapeEvent H encode (automaticThresholds (E := E) DL DR D T f) T k B) :
    eventProbability (largeComponentEvent encode (automaticThresholds (E := E) DL DR D T f)
      T ((d+1)*(k+1))) ≤ 3/(N:ℝ)^c := by
  apply largeComponent_polynomial_tail_of_coverage H encode _ T d k B N c hN hLN hRN hd hk hmean hcoverage
  intro j _
  exact heavyShape_geometric_automatic H encode DL DR D T (k+j) f hsimple hDL hL hR hT hf

theorem expected_load_polynomial_automatic_of_coverage (H : C → Peeling.Graph L R)
    (encode : E → Arrival L R C) (DL DR : C → ℕ) (D T d k B N c : ℕ) (f : C → ℝ)
    (hsimple : Function.Injective fun e => ((encode e).left,(encode e).right))
    (hDL : ∀ u c, (sourceBucket encode u c).card ≤ DL c)
    (hL : ∀ c u, Peeling.leftDegree (H c) u ≤ D)
    (hR : ∀ c v, Peeling.rightDegree (H c) v ≤ DR c)
    (hT : 0 < T) (hf : ∀ c, 1 < f c)
    (hN : 0 < N) (hLN : Fintype.card L ≤ N) (hRN : Fintype.card R ≤ N)
    (hd : polynomialCutoff N c ≤ d+1) (hk : polynomialCutoff N c ≤ k)
    (hmean : ∀ u, Real.exp 1*T*(((leftSourceBucket encode u).card : ℝ)/Fintype.card E)/(d+1) ≤ 1/2)
    (hcoverage : largeHeavyTreeEvent encode (automaticThresholds (E := E) DL DR D T f) T k ⊆
      largeShapeEvent H encode (automaticThresholds (E := E) DL DR D T f) T k B) :
    expectedTotalMaxLoad encode (automaticThresholds (E := E) DL DR D T f) T ≤
      (∑ c, (automaticThresholds (E := E) DL DR D T f c : ℝ)) +
      (2*(Nat.log 2 ((d+1)*(k+1))+1) : ℕ)*expectedReplayOpt encode T + 3*T/(N:ℝ)^c := by
  apply expected_load_polynomial_of_coverage H encode _ T d k B N c hN hLN hRN hd hk hmean hcoverage
  intro j _
  exact heavyShape_geometric_automatic H encode DL DR D T (k+j) f hsimple hDL hL hR hT hf

end GraphChoices.Patterns
