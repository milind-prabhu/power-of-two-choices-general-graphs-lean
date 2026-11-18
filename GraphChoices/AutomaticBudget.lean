import GraphChoices.ExplicitThresholdBudget
import GraphChoices.AutomaticThresholds

/-! The finite-index budget for the exact automatic threshold vector used by
the execution and shattering theorems. All rate and branching parameters are
the same definitions, rather than independently chosen numerical certificates.
-/
namespace GraphChoices.Patterns
open Finset

noncomputable def extendFinZero {h : ℕ} (f : Fin h → ℝ) (i : ℕ) : ℝ :=
  if hi : i < h then f ⟨i,hi⟩ else 0

theorem sufficientThreshold_fin_scale_budget (h : ℕ) (mean x : Fin h → ℝ) (A L σ K : ℝ)
    (hmean : ∀ i, 0 ≤ mean i) (hx : ∀ i, 0 ≤ x i)
    (hA : 0 ≤ A) (hL : 1 ≤ L) (hσ : 0 ≤ σ) (hK : 1 ≤ K)
    (hbase : ∀ i, (Peeling.scaleNat i.val : ℝ)*mean i ≤ A)
    (hbranch : ∀ i, x i ≤ K*((Peeling.scaleNat i.val : ℝ)*L)^(2*σ)) :
    (∑ i : Fin h, (sufficientThreshold (mean i) (Peeling.scaleNat i.val)
      (Real.log (x i)/Real.log (Peeling.scaleNat i.val)) : ℝ)) ≤
      h*(A+2*σ+2)+(Real.log K+2*σ*Real.log L)/Real.log 2 := by
  have ht := sufficientThreshold_scale_budget h (extendFinZero mean) (extendFinZero x) A L σ K
    (fun i hi => by simpa [extendFinZero, hi] using hmean ⟨i,hi⟩)
    (fun i hi => by simpa [extendFinZero, hi] using hx ⟨i,hi⟩) hA hL hσ hK
    (fun i hi => by simpa [extendFinZero, hi] using hbase ⟨i,hi⟩)
    (fun i hi => by simpa [extendFinZero, hi] using hbranch ⟨i,hi⟩)
  rw [← Fin.sum_univ_eq_sum_range] at ht
  simpa only [extendFinZero, Fin.isLt, dite_true] using ht

variable {E : Type*} [Fintype E] [Nonempty E]

/-- Budget for exactly the automatic thresholds. h is the actual finite
class count, D is the actual common left cap, and z=T/|E|. -/
theorem automaticThresholds_budget (h D T : ℕ) (DL DR : Fin h → ℕ) (B L σ : ℝ)
    (hh : 0 < h) (hB : 0 < B) (hL : 1 ≤ L) (hσ : 0 ≤ σ)
    (hmass : 1 ≤ 16*B*((T:ℝ)/Fintype.card E))
    (hDL : ∀ i, (DL i : ℝ) ≤ 16*B/(Peeling.scaleNat i.val : ℝ))
    (hDR : ∀ i, (DR i : ℝ) ≤ 16*B*((Peeling.scaleNat i.val : ℝ)*L)^(2*σ)) :
    (∑ i : Fin h, (automaticThresholds (E := E) DL DR D T (fun i => Peeling.scaleNat i.val) i : ℝ)) ≤
      h*(16*Real.exp 1*B*((T:ℝ)/Fintype.card E)+2*σ+2) +
      (Real.log (16*B*((T:ℝ)/Fintype.card E)/
        branchTarget D h ((T:ℝ)/Fintype.card E)) + 2*σ*Real.log L)/Real.log 2 := by
  have hz : 0 ≤ (T:ℝ)/Fintype.card E := by positivity
  have hb := branchTarget_pos D h _ hh hz
  have hb1 := (branchTarget_le_rate D h _ hh hz).trans (shapeRate_le_one h hh)
  have hK : 1 ≤ 16*B*((T:ℝ)/Fintype.card E)/branchTarget D h ((T:ℝ)/Fintype.card E) := by
    apply (le_div_iff₀ hb).mpr
    simpa only [one_mul] using hb1.trans hmass
  have ht := sufficientThreshold_fin_scale_budget h
    (fun i => Real.exp 1*T*(DL i : ℝ)/Fintype.card E)
    (fun i => (DR i : ℝ)*((T:ℝ)/Fintype.card E)/branchTarget D h ((T:ℝ)/Fintype.card E))
    (16*Real.exp 1*B*((T:ℝ)/Fintype.card E)) L σ _
    (fun _ => by positivity) (fun _ => by positivity) (by positivity) hL hσ hK ?_ ?_
  · simpa only [automaticThresholds, explicitThresholds, Fintype.card_fin] using ht
  · intro i
    have hpos : (0:ℝ) < Peeling.scaleNat i.val := by exact_mod_cast Peeling.scaleNat_pos i.val
    have hd := (le_div_iff₀ hpos).mp (hDL i)
    calc
      _ = (Real.exp 1*((T:ℝ)/Fintype.card E))*((DL i : ℝ)*(Peeling.scaleNat i.val : ℝ)) := by ring
      _ ≤ (Real.exp 1*((T:ℝ)/Fintype.card E))*(16*B) := mul_le_mul_of_nonneg_left hd (by positivity)
      _ = _ := by ring
  · intro i
    calc
      _ = (DR i : ℝ)*(((T:ℝ)/Fintype.card E)/branchTarget D h ((T:ℝ)/Fintype.card E)) := by ring
      _ ≤ (16*B*((Peeling.scaleNat i.val : ℝ)*L)^(2*σ))*
          (((T:ℝ)/Fintype.card E)/branchTarget D h ((T:ℝ)/Fintype.card E)) :=
        mul_le_mul_of_nonneg_right (hDR i) (by positivity)
      _ = _ := by ring

end GraphChoices.Patterns
