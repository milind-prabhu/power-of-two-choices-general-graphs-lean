import GraphChoices.Model
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-! An exact finite probability space: every function Fin T → E is equally
likely. Thus edge samples are independent and uniform, with replacement.
Expectations are finite averages, so no measure-theoretic assumptions are hidden. -/
namespace GraphChoices
open Finset

noncomputable def average {Ω : Type*} [Fintype Ω] (f : Ω → ℝ) : ℝ :=
  (∑ ω, f ω) / Fintype.card Ω

 theorem average_mono {Ω : Type*} [Fintype Ω] {f g : Ω → ℝ} (h : ∀ ω, f ω ≤ g ω) :
    average f ≤ average g := by
  unfold average
  exact div_le_div_of_nonneg_right (sum_le_sum fun ω _ => h ω) (Nat.cast_nonneg _)

 theorem average_sum {Ω K : Type*} [Fintype Ω] [Fintype K] (f : K → Ω → ℝ) :
    average (fun ω => ∑ k, f k ω) = ∑ k, average (f k) := by
  unfold average
  simp only [div_eq_mul_inv, sum_mul]
  rw [sum_comm]

 theorem average_mul {Ω : Type*} [Fintype Ω] (c : ℝ) (f : Ω → ℝ) :
    average (fun ω => c * f ω) = c * average f := by
  simp only [average, ← mul_sum]
  ring

 theorem average_const {Ω : Type*} [Fintype Ω] [Nonempty Ω] (c : ℝ) :
    average (fun _ : Ω => c) = c := by
  simp [average, Fintype.card_ne_zero]

variable {E : Type*} [Fintype E] [DecidableEq E] [Nonempty E] {T : ℕ}

omit [Nonempty E] in
 theorem sample_fiber_card (t : Fin T) (e : E) :
    (univ.filter fun ω : Fin T → E => ω t = e).card = Fintype.card E ^ (T-1) := by
  simpa using Fintype.card_filter_piFinset_const_eq_of_mem
    (ι := Fin T) (univ : Finset E) t (mem_univ e)

omit [Nonempty E] in
 theorem sum_coordinate (t : Fin T) (f : E → ℝ) :
    (∑ ω : Fin T → E, f (ω t)) =
      (Fintype.card E : ℝ)^(T-1) * ∑ e, f e := by
  calc
    _ = ∑ e : E, ∑ ω ∈ (univ.filter fun ω : Fin T → E => ω t = e), f (ω t) :=
      (sum_fiberwise univ (fun ω : Fin T → E => ω t) (fun ω => f (ω t))).symm
    _ = ∑ e : E, (Fintype.card E : ℝ)^(T-1) * f e := by
      apply sum_congr rfl
      intro e _
      calc
        _ = ∑ _ω ∈ (univ.filter fun ω : Fin T → E => ω t = e), f e := by
          apply sum_congr rfl
          intro ω hω
          rw [(mem_filter.mp hω).2]
        _ = _ := by simp [sample_fiber_card, nsmul_eq_mul]
    _ = _ := by rw [mul_sum]

/-- Each coordinate of the product space is exactly uniform. -/
 theorem average_coordinate (t : Fin T) (f : E → ℝ) :
    average (fun ω : Fin T → E => f (ω t)) = average f := by
  unfold average
  rw [sum_coordinate]
  have hT : T = (T-1)+1 := by have := t.isLt; omega
  have hm : (Fintype.card E : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
  have heq : (Fintype.card E : ℝ)^T = (Fintype.card E : ℝ)^(T-1) * Fintype.card E := by
    nth_rw 1 [hT]
    rw [pow_succ]
  rw [heq]
  field_simp

/-- A base graph is represented by a finite, nonempty set of edge labels.
Taking E to be the edges of a simple graph gives exactly the paper's model. -/
structure BaseGraph (V E : Type*) where
  left : E → V
  right : E → V

variable {V : Type*} [Fintype V] [DecidableEq V]

def BaseGraph.sample (G : BaseGraph V E) (ω : Fin T → E) : Instance V T where
  left t := G.left (ω t)
  right t := G.right (ω t)

def BaseGraph.internalEdges (G : BaseGraph V E) (S : Finset V) : Finset E :=
  univ.filter fun e => G.left e ∈ S ∧ G.right e ∈ S

noncomputable def expectedOpt (G : BaseGraph V E) (T : ℕ) : ℝ :=
  average (fun ω : Fin T → E => (opt (G.sample ω) : ℝ))

omit [Fintype V] in
 theorem average_internalCount (G : BaseGraph V E) (S : Finset V) (T : ℕ) :
    average (fun ω : Fin T → E => (internalCount (G.sample ω) S : ℝ)) =
      T * ((G.internalEdges S).card : ℝ) / Fintype.card E := by
  have hsum (ω : Fin T → E) : (internalCount (G.sample ω) S : ℝ) =
      ∑ t : Fin T, if G.left (ω t) ∈ S ∧ G.right (ω t) ∈ S then (1:ℝ) else 0 := by
    simp only [internalCount, BaseGraph.sample, card_eq_sum_ones, sum_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  simp_rw [hsum]
  rw [average_sum]
  have hk (k : Fin T) :
      average (fun ω : Fin T → E => if G.left (ω k) ∈ S ∧ G.right (ω k) ∈ S then (1:ℝ) else 0) =
      average (fun e : E => if G.left e ∈ S ∧ G.right e ∈ S then (1:ℝ) else 0) :=
    average_coordinate k (fun e : E => if G.left e ∈ S ∧ G.right e ∈ S then (1:ℝ) else 0)
  simp_rw [hk]
  simp [average, BaseGraph.internalEdges, sum_boole, mul_div_assoc]

/-- Density lower bound for every subset and every number of arrivals.
Equivalent to (16) after substituting d_av = 2|E|/n and maximizing over S. -/
 theorem expected_density_lower_bound (G : BaseGraph V E) (S : Finset V) (T : ℕ) :
    T * ((G.internalEdges S).card : ℝ) / Fintype.card E ≤
      S.card * expectedOpt G T := by
  rw [← average_internalCount]
  unfold expectedOpt
  rw [← average_mul]
  apply average_mono
  intro ω
  exact_mod_cast density_le_opt (G.sample ω) S

omit [DecidableEq E] in
 theorem expectedOpt_ge_one (G : BaseGraph V E) (T : ℕ) (hT : 0 < T) :
    1 ≤ expectedOpt G T := by
  rw [← average_const (Ω := Fin T → E) (1:ℝ)]
  exact average_mono fun ω => by exact_mod_cast opt_pos (G.sample ω) hT

end GraphChoices
