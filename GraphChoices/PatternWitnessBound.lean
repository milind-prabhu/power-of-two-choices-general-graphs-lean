import GraphChoices.InjectedWitnesses
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Sigma

/-! Joint witness bound of the form used in Equations (10)--(12). Tree slots
require fixed base edges. Each threshold bucket chooses an unordered set of
alpha_j time steps. Only globally injective assignments are retained, so all
required occurrences are distinct and the product probability is justified.
The graph-to-witness encoding and pattern-embedding count are separate results.
-/
namespace GraphChoices
open Finset
variable {E J : Type*} [Fintype E] [DecidableEq E] [Nonempty E]
  [Fintype J] [DecidableEq J]

abbrev TimeChoice (T k : ℕ) :=
  {K : Finset (Fin T) // K ∈ (univ : Finset (Fin T)).powersetCard k}

abbrev TimeWitness (J : Type*) (T m : ℕ) (α : J → ℕ) :=
  (Fin m → Fin T) × ((j : J) → TimeChoice T (α j))

abbrev WitnessSlot (J : Type*) (m : ℕ) (α : J → ℕ) :=
  Fin m ⊕ ((j : J) × Fin (α j))

noncomputable def witnessTime {T m : ℕ} {α : J → ℕ} (w : TimeWitness J T m α) :
    WitnessSlot J m α → Fin T
  | Sum.inl i => w.1 i
  | Sum.inr ⟨j,i⟩ => (w.2 j).val.orderEmbOfFin ((mem_powersetCard.mp (w.2 j).property).2) i

def slotAllowed {m : ℕ} {α : J → ℕ} (tree : Fin m → E) (bucket : J → Finset E) :
    WitnessSlot J m α → Finset E
  | Sum.inl i => {tree i}
  | Sum.inr ⟨j,_⟩ => bucket j

 theorem timeChoice_card (T k : ℕ) : Fintype.card (TimeChoice T k) = T.choose k := by
  simp [TimeChoice, Fintype.card_coe, card_powersetCard]

 theorem timeWitness_card (T m : ℕ) (α : J → ℕ) :
    Fintype.card (TimeWitness J T m α) = T^m * ∏ j, T.choose (α j) := by
  simp [TimeWitness, Fintype.card_prod, Fintype.card_fun, Fintype.card_pi, timeChoice_card]

 theorem slot_probability_product {m : ℕ} (α : J → ℕ) (tree : Fin m → E) (bucket : J → Finset E) :
    (∏ s : WitnessSlot J m α, ((slotAllowed tree bucket s).card : ℝ) / Fintype.card E) =
      ((1:ℝ) / Fintype.card E)^m * ∏ j, (((bucket j).card : ℝ) / Fintype.card E)^(α j) := by
  rw [Fintype.prod_sum_type, Fintype.prod_sigma]
  simp [slotAllowed, div_pow, prod_div_distrib]

noncomputable def patternWitnessEvent (T m : ℕ) (α : J → ℕ)
    (tree : Fin m → E) (bucket : J → Finset E) : Finset (Fin T → E) := by
  classical
  exact univ.biUnion fun w : TimeWitness J T m α =>
    if Function.Injective (witnessTime w) then requirementsEvent (witnessTime w) (slotAllowed tree bucket) else ∅

/-- Joint counting and probability bound with exact binomial coefficients. -/
 theorem patternWitness_probability_le (T m : ℕ) (α : J → ℕ)
    (tree : Fin m → E) (bucket : J → Finset E) :
    eventProbability (patternWitnessEvent T m α tree bucket) ≤
      ((T:ℝ) / Fintype.card E)^m *
        ∏ j, (T.choose (α j) : ℝ) * (((bucket j).card : ℝ) / Fintype.card E)^(α j) := by
  classical
  have hh := injected_witness_union_bound
    (W := TimeWitness J T m α) (J := WitnessSlot J m α) witnessTime (slotAllowed tree bucket)
  change eventProbability (patternWitnessEvent T m α tree bucket) ≤ _ at hh
  calc
    _ ≤ (Fintype.card (TimeWitness J T m α) : ℝ) *
        (∏ s : WitnessSlot J m α, ((slotAllowed tree bucket s).card : ℝ) / Fintype.card E) := hh
    _ = _ := by
      rw [timeWitness_card, slot_probability_product]
      simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_prod, prod_mul_distrib, div_pow]
      ring

/-- The exponential version corresponding to the raw pattern bound in (12).
All time-step collisions have been discarded before applying independence. -/
 theorem patternWitness_probability_le_exp (T m : ℕ) (α : J → ℕ)
    (tree : Fin m → E) (bucket : J → Finset E) :
    eventProbability (patternWitnessEvent T m α tree bucket) ≤
      ((T:ℝ) / Fintype.card E)^m *
        ∏ j, (Real.exp 1 * T * (((bucket j).card : ℝ) / Fintype.card E) / α j)^(α j) := by
  apply (patternWitness_probability_le T m α tree bucket).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply prod_le_prod
  · intro j _; positivity
  · intro j _
    calc
      (T.choose (α j) : ℝ) * (((bucket j).card : ℝ) / Fintype.card E)^(α j) ≤
          (Real.exp 1 * T / α j)^(α j) * (((bucket j).card : ℝ) / Fintype.card E)^(α j) :=
        mul_le_mul_of_nonneg_right (choose_le_exp_div_pow T (α j)) (by positivity)
      _ = _ := by rw [← mul_pow]; congr 1; ring

end GraphChoices
