import GraphChoices.Model
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.BigOperators

/-! Pairing branching factors in a left-heavy witness. At least as many small
factors as large ones suffice for geometric decay, even when a large factor
exceeds one. -/
namespace GraphChoices
open Finset

theorem paired_power_bound (a b r : ℝ) (q l : ℕ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hr : 0 ≤ r) (hql : q ≤ l)
    (hab : a*b ≤ r^2) (hbr : b ≤ r) : a^q*b^l ≤ r^(q+l) := by
  have hsplit : l = q + (l-q) := by omega
  calc
    _ = (a*b)^q * b^(l-q) := by nth_rw 1 [hsplit]; rw [pow_add, mul_pow]; ring
    _ ≤ (r^2)^q * r^(l-q) :=
      mul_le_mul (pow_le_pow_left₀ (mul_nonneg ha hb) hab q) (pow_le_pow_left₀ hb hbr (l-q))
        (pow_nonneg hb _) (by positivity)
    _ = _ := by rw [← pow_mul, ← pow_add]; congr 1; omega

 theorem two_class_product_bound {I : Type*} [Fintype I] (P : I → Prop) [DecidablePred P]
    (a b r : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hr : 0 ≤ r)
    (hab : a*b ≤ r^2) (hbr : b ≤ r)
    (hheavy : Fintype.card I ≤ 2 * (univ.filter P).card) :
    (∏ i : I, if P i then b else a) ≤ r^(Fintype.card I) := by
  classical
  let l := (univ.filter P).card
  let q := (univ.filter fun i => ¬P i).card
  have hsum : l+q = Fintype.card I := by
    simpa [l,q] using filter_card_add_filter_neg_card_eq_card (s := (univ : Finset I)) P
  have hql : q ≤ l := by dsimp [l,q] at *; omega
  have heq : (∏ i : I, if P i then b else a) = b^l*a^q := by
    rw [prod_ite]
    simp [l,q]
  rw [heq, mul_comm, ← hsum]
  have hp := paired_power_bound a b r q l ha hb hr hql hab hbr
  simpa [Nat.add_comm] using hp

 theorem subtype_product_as_ite {I : Type*} [Fintype I] (P : I → Prop) [DecidablePred P]
    (f : I → ℝ) : (∏ j : {i // P i}, f j.val) = ∏ i, if P i then f i else 1 := by
  classical
  rw [← Finset.prod_subtype (univ.filter P) (by simp) f, prod_filter]

end GraphChoices
