import GraphChoices.RandomGreedy

namespace GraphChoices.RandomGreedy
open Finset
variable {V E : Type*} [Fintype V] [DecidableEq V]

theorem choice_at_tie (G : BaseGraph V E) (s : V → ℕ) (e : E) (c : Bool)
    (h : s (G.left e) = s (G.right e)) : choice G s (e,c) = c := by
  simp [choice,h]

theorem fair_tie_probability (G : BaseGraph V E) (s : V → ℕ) (e : E)
    (h : s (G.left e) = s (G.right e)) :
    eventProbability (univ.filter fun c : Bool => choice G s (e,c) = true) = 1/2 := by
  have heq : (univ.filter fun c : Bool => choice G s (e,c) = true) = {true} := by
    ext c
    simp [choice_at_tie G s e c h]
  rw [heq]
  norm_num [eventProbability]

variable [Fintype E] [DecidableEq E] [Nonempty E]

theorem coin_expectedOpt (G : BaseGraph V E) (T : ℕ) :
    expectedOpt (coinGraph G) T = expectedOpt G T := by
  unfold expectedOpt
  let e := (Equiv.arrowProdEquivProdArrow (Fin T) (fun _ => E) (fun _ => Bool)).symm
  rw [← average_equiv e]
  change average (fun p : (Fin T → E) × (Fin T → Bool) => (opt (G.sample p.1):ℝ)) =
    average (fun ω : Fin T → E => (opt (G.sample ω):ℝ))
  exact average_product_fst (Ω' := Fin T → Bool) (fun ω : Fin T → E => (opt (G.sample ω):ℝ))

end GraphChoices.RandomGreedy
