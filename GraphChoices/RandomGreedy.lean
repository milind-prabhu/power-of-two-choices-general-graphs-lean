import GraphChoices.MainProof

/-! Ordinary Greedy with a fresh independent fair coin for ties. The source
alphabet E × Bool records both the edge and the otherwise unused coin. -/
namespace GraphChoices.RandomGreedy
open Finset
variable {V E : Type*} [Fintype V] [DecidableEq V]

def choice (G : BaseGraph V E) (s : V → ℕ) (x : E × Bool) : Bool :=
  if s (G.left x.1) < s (G.right x.1) then true
  else if s (G.right x.1) < s (G.left x.1) then false else x.2

def target (G : BaseGraph V E) (s : V → ℕ) (x : E × Bool) : V :=
  if choice G s x then G.left x.1 else G.right x.1

def step (G : BaseGraph V E) (s : V → ℕ) (x : E × Bool) : V → ℕ :=
  fun v => s v + if target G s x = v then 1 else 0

def run (G : BaseGraph V E) (xs : List (E × Bool)) : V → ℕ :=
  xs.foldl (step G) (fun _ => 0)

def policy (G : BaseGraph V E) : OnlinePolicy (E × Bool) := fun history x => choice G (run G history) x

def coinGraph (G : BaseGraph V E) : BaseGraph V (E × Bool) where
  left x := G.left x.1
  right x := G.right x.1

def state (G : BaseGraph V E) {T : ℕ} (ω : Fin T → E × Bool) (k : ℕ) : V → ℕ :=
  run G ((List.ofFn ω).take k)

theorem run_append (G : BaseGraph V E) (xs : List (E × Bool)) (x : E × Bool) :
    run G (xs ++ [x]) = step G (run G xs) x := by simp only [run, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem state_zero (G : BaseGraph V E) {T : ℕ} (ω : Fin T → E × Bool) (v : V) : state G ω 0 v = 0 := by
  simp only [state, List.take_zero, run, List.foldl_nil]

theorem state_step (G : BaseGraph V E) {T : ℕ} (ω : Fin T → E × Bool) (t : Fin T) (v : V) :
    state G ω (t.val+1) v = state G ω t.val v +
      if destination ((coinGraph G).sample ω) (onlineOrientation (policy G) ω) t = v then 1 else 0 := by
  have ht : t.val < (List.ofFn ω).length := by simpa using t.isLt
  simp only [state, List.take_succ_eq_append_getElem ht, run_append, step,
    List.getElem_ofFn, destination, BaseGraph.sample, coinGraph, onlineOrientation, policy, target]

theorem state_eq_prefixLoad (G : BaseGraph V E) {T : ℕ} (ω : Fin T → E × Bool)
    (k : ℕ) (hk : k ≤ T) (v : V) :
    state G ω k v = prefixLoad ((coinGraph G).sample ω) (onlineOrientation (policy G) ω) k v :=
  execution_counts_prefix _ _ _ (state_zero G ω) (state_step G ω) k hk v

theorem state_mono (G : BaseGraph V E) {T : ℕ} (ω : Fin T → E × Bool)
    {a b : ℕ} (hab : a ≤ b) (hb : b ≤ T) (v : V) : state G ω a v ≤ state G ω b v := by
  rw [state_eq_prefixLoad G ω a (hab.trans hb), state_eq_prefixLoad G ω b hb]
  apply card_le_card
  intro t ht
  simp only [mem_filter, mem_univ, true_and] at ht ⊢
  exact ⟨by omega,ht.2⟩

theorem choice_favours_left (G : BaseGraph V E) (s : V → ℕ) (x : E × Bool)
    (hcoin : x.2 = true) (hload : s (G.left x.1) ≤ s (G.right x.1)) : choice G s x = true := by
  unfold choice
  split_ifs with h1 h2
  · rfl
  · omega
  · exact hcoin

theorem policy_isGreedy (G : BaseGraph V E) {T : ℕ} (ω : Fin T → E × Bool) :
    IsGreedy ((coinGraph G).sample ω) (onlineOrientation (policy G) ω) := by
  apply isGreedy_of_execution _ _ _ (state_zero G ω) (state_step G ω)
  intro t v hv
  change v = G.left (ω t).1 ∨ v = G.right (ω t).1 at hv
  change state G ω t.val (target G (state G ω t.val) (ω t)) ≤ state G ω t.val v
  by_cases h1 : state G ω t.val (G.left (ω t).1) < state G ω t.val (G.right (ω t).1)
  · simp only [target, choice, if_pos h1, ↓reduceIte]
    rcases hv with rfl | rfl <;> omega
  · by_cases h2 : state G ω t.val (G.right (ω t).1) < state G ω t.val (G.left (ω t).1)
    · simp only [target, choice, if_neg h1, if_pos h2, Bool.false_eq_true, ↓reduceIte]
      rcases hv with rfl | rfl <;> omega
    · simp only [target, choice, if_neg h1, if_neg h2]
      split <;> rcases hv with rfl | rfl <;> omega

variable [Fintype E] [DecidableEq E] [Nonempty E]
noncomputable def expectedLoad (G : BaseGraph V E) (T : ℕ) : ℝ :=
  expectedCost (coinGraph G) (onlineOrientation (T := T) (policy G))

end GraphChoices.RandomGreedy
