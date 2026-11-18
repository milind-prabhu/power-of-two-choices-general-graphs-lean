import GraphChoices.Greedy

/-! A bridge from a state-by-state execution to the indexed Greedy relation.
The increment invariant is proved equivalent to counting assigned occurrences.
-/
namespace GraphChoices
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V] {T : ℕ}

 theorem prefixLoad_succ (I : Instance V T) (a : Orientation T) (t : Fin T) (v : V) :
    prefixLoad I a (t.val+1) v = prefixLoad I a t.val v + if destination I a t = v then 1 else 0 := by
  classical
  have htime (s : Fin T) : s.val < t.val+1 ↔ s.val < t.val ∨ s = t := by
    constructor
    · intro hs
      by_cases heq : s.val = t.val
      · exact Or.inr (Fin.ext heq)
      · exact Or.inl (by omega)
    · rintro (h | rfl) <;> omega
  have hnot : t ∉ univ.filter (fun s : Fin T => s.val < t.val ∧ destination I a s = v) := by simp
  by_cases hd : destination I a t = v
  · have heq : (univ.filter fun s : Fin T => s.val < t.val+1 ∧ destination I a s = v) =
        insert t (univ.filter fun s : Fin T => s.val < t.val ∧ destination I a s = v) := by
      ext s
      simp only [mem_filter, mem_univ, true_and, mem_insert, htime]
      constructor
      · rintro ⟨h,hs⟩
        rcases h with h | rfl
        · exact Or.inr ⟨h,hs⟩
        · exact Or.inl rfl
      · rintro (rfl | h)
        · exact ⟨Or.inr rfl,hd⟩
        · exact ⟨Or.inl h.1,h.2⟩
    simp only [prefixLoad, heq, card_insert_of_notMem hnot, if_pos hd]
  · have heq : (univ.filter fun s : Fin T => s.val < t.val+1 ∧ destination I a s = v) =
        univ.filter (fun s : Fin T => s.val < t.val ∧ destination I a s = v) := by
      ext s
      simp only [mem_filter, mem_univ, true_and, htime]
      constructor
      · rintro ⟨h,hs⟩
        rcases h with h | rfl
        · exact ⟨h,hs⟩
        · exact False.elim (hd hs)
      · intro h; exact ⟨Or.inl h.1,h.2⟩
    simp only [prefixLoad, heq, if_neg hd, Nat.add_zero]

 theorem execution_counts_prefix (I : Instance V T) (a : Orientation T) (x : ℕ → V → ℕ)
    (hzero : ∀ v, x 0 v = 0)
    (hstep : ∀ t : Fin T, ∀ v, x (t.val+1) v = x t.val v + if destination I a t = v then 1 else 0)
    (k : ℕ) (hk : k ≤ T) (v : V) : x k v = prefixLoad I a k v := by
  induction k with
  | zero => simp [hzero, prefixLoad]
  | succ k ih =>
    let t : Fin T := ⟨k,by omega⟩
    have hs := hstep t v
    have hp := prefixLoad_succ I a t v
    have hi := ih (by omega)
    simpa only [t, hi, hp] using hs

 theorem isGreedy_of_execution (I : Instance V T) (a : Orientation T) (x : ℕ → V → ℕ)
    (hzero : ∀ v, x 0 v = 0)
    (hstep : ∀ t : Fin T, ∀ v, x (t.val+1) v = x t.val v + if destination I a t = v then 1 else 0)
    (hchoice : ∀ t : Fin T, ∀ v, (v = I.left t ∨ v = I.right t) →
      x t.val (destination I a t) ≤ x t.val v) : IsGreedy I a := by
  intro t v hv
  rw [← execution_counts_prefix I a x hzero hstep t.val (Nat.le_of_lt t.isLt) _,
    ← execution_counts_prefix I a x hzero hstep t.val (Nat.le_of_lt t.isLt) _]
  exact hchoice t v hv

 theorem execution_final_load (I : Instance V T) (a : Orientation T) (x : ℕ → V → ℕ)
    (hzero : ∀ v, x 0 v = 0)
    (hstep : ∀ t : Fin T, ∀ v, x (t.val+1) v = x t.val v + if destination I a t = v then 1 else 0)
    (v : V) : x T v = load I a v := by
  rw [execution_counts_prefix I a x hzero hstep T le_rfl v]
  unfold prefixLoad load
  congr 1
  ext t
  simp [t.isLt]

end GraphChoices
