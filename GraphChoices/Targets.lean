import GraphChoices.Preprocessing
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# End-to-end specification

This module defines the main theorem as a proposition, without assuming it.
GraphChoices.MainProof proves this exact proposition as mainTheorem.
The online policy receives only the preceding edge labels and current edge.
-/
namespace GraphChoices

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E] [Nonempty E] {T : ℕ}

/-- No loops and no repeated unordered base edges. -/
def BaseGraph.IsSimple (G : BaseGraph V E) : Prop :=
  (∀ e, G.left e ≠ G.right e) ∧
    ∀ e f, ((G.left e = G.left f ∧ G.right e = G.right f) ∨
      (G.left e = G.right f ∧ G.right e = G.left f)) → e = f

abbrev OnlinePolicy (E : Type*) := List E → E → Bool

def onlineOrientation (p : OnlinePolicy E) (ω : Fin T → E) : Orientation T :=
  fun t => p ((List.ofFn ω).take t.val) (ω t)

def collapsePolicy (b : E → Bool) (p : OnlinePolicy E) : OnlinePolicy E :=
  fun history e => if b e then p history e else !(p history e)

omit [Fintype E] [DecidableEq E] [Nonempty E] in
 theorem collapsePolicy_orientation (b : E → Bool) (p : OnlinePolicy E) (ω : Fin T → E) :
    onlineOrientation (collapsePolicy b p) ω =
      transport (fun t => b (ω t)) (onlineOrientation p ω) := rfl

/-- The expected transfer also preserves the explicit online-policy type. -/
 theorem online_expected_transfer (G : BaseGraph V E) (b : E → Bool)
    (p : OnlinePolicy E) (c : ℝ) (hc : 0 ≤ c)
    (hcost : expectedCost (T := T) (G.split b) (onlineOrientation p) ≤
      c * expectedOpt (G.split b) T) :
    expectedCost (T := T) G (onlineOrientation (collapsePolicy b p)) ≤
      (2*c) * expectedOpt G T := by
  exact expected_competitive_transfer G b (onlineOrientation p) c hc hcost

/-- Positive for small n and asymptotically Theta(log log n). -/
noncomputable def loglogFactor (n : ℕ) : ℝ :=
  1 + Real.log (1 + Real.log (max 2 (n : ℝ)))

/-- Theorem 1.1 specification, proved by GraphChoices.mainTheorem, with a
horizon-aware deterministic online policy and
an explicit bounded-at-small-n interpretation of O(log log n).
Edge labels use Fin(m+1) to ensure that the sampling space is nonempty. -/
def MainTheorem : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (n m : ℕ) (G : BaseGraph (Fin n) (Fin (m+1))), G.IsSimple →
      ∀ T : ℕ, ∃ p : OnlinePolicy (Fin (m+1)),
        expectedCost G (onlineOrientation (T := T) p) ≤
          C * loglogFactor n * expectedOpt G T

end GraphChoices
