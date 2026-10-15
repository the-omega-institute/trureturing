/- GID: D5/S1/Words/AdmissibleWords/KBonacciIntegerInterval
   generality: I
   mirror-B: D5/B/S1/Words/AdmissibleWords/KBonacciIntegerInterval
   mirror-E: none(waiver:pure-structural-integer-representation)
   anchors: []
   utility: none
   digest: Run-avoiding words represent the initial k-bonacci integer interval. -/

import D5.S1.Words.ClosedRunStarts

set_option autoImplicit false

namespace D5.S1.Words.AdmissibleWords.KBonacciIntegerInterval

open D5.S0.Tower.DBonacci.Names
open D5.S1.Words.ClosedRunStarts

/-- The integer value, with coordinate zero the least significant digit. -/
def integerValue (k : ℕ) {n : ℕ} (w : Fin n → Bool) : ℤ :=
  ∑ i : Fin n, if w i then (dbonacci k (i.val + 2) : ℤ) else 0

private def highValue (k : ℕ) {n : ℕ} (w : Fin n → Bool) : ℕ :=
  ∑ i : Fin n, if w i then dbonacci k (n - 1 - i.val + 2) else 0

private theorem highValue_cons (k n : ℕ) (b : Bool) (w : Fin n → Bool) :
    highValue k (Fin.cons b w) =
      (if b then dbonacci k (n + 2) else 0) + highValue k w := by
  simp only [highValue, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ,
    Fin.val_zero, Fin.val_succ, Nat.add_sub_cancel, Nat.sub_zero]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [show n - (i.val + 1) = n - 1 - i.val by omega]

private theorem bounded_value_spec (maxTrue fuel n : ℕ) :
    (∀ w : BoundedRunName maxTrue fuel n,
      highValue (maxTrue + 1) w.val < Fintype.card (BoundedRunName maxTrue fuel n)) ∧
    Function.Injective (fun w : BoundedRunName maxTrue fuel n =>
      highValue (maxTrue + 1) w.val) := by
  induction n generalizing fuel with
  | zero =>
    let : Unique (BoundedRunName maxTrue fuel 0) :=
      { default := ⟨Fin.elim0, rfl⟩
        uniq := by intro w; apply Subtype.ext; funext i; exact Fin.elim0 i }
    constructor
    · intro w
      simp [highValue, Fintype.card_unique]
    · intro a b _
      exact Subsingleton.elim a b
  | succ n ih =>
    have hc : Fintype.card (BoundedRunName maxTrue maxTrue n) =
        dbonacci (maxTrue + 1) (n + 2) :=
      (dbonacci_name_card_eq_bounded maxTrue n).symm.trans
        (dbonacci_name_card (maxTrue + 1) n)
    cases fuel with
    | zero =>
      let e := boundedRunNameZeroEquiv maxTrue n
      constructor
      · intro w
        obtain ⟨t, rfl⟩ := e.symm.surjective w
        change highValue (maxTrue + 1) (Fin.cons false t.val) < _
        simpa [highValue_cons, bounded_run_name_card_zero] using (ih maxTrue).1 t
      · intro a b he
        obtain ⟨a, rfl⟩ := e.symm.surjective a
        obtain ⟨b, rfl⟩ := e.symm.surjective b
        apply congrArg e.symm
        apply (ih maxTrue).2
        change highValue (maxTrue + 1) (Fin.cons false a.val) =
          highValue (maxTrue + 1) (Fin.cons false b.val) at he
        simpa [highValue_cons] using he
    | succ fuel =>
      let e := boundedRunNameSplitEquiv maxTrue fuel n
      constructor
      · intro w
        obtain ⟨t, rfl⟩ := e.symm.surjective w
        rcases t with t | t
        · change highValue (maxTrue + 1) (Fin.cons false t.val) < _
          simp only [highValue_cons, Bool.false_eq_true, ↓reduceIte, zero_add]
          rw [bounded_run_name_card_succ]
          exact lt_of_lt_of_le ((ih maxTrue).1 t) (Nat.le_add_right _ _)
        · change highValue (maxTrue + 1) (Fin.cons true t.val) < _
          simp only [highValue_cons, ↓reduceIte]
          rw [bounded_run_name_card_succ, hc]
          exact Nat.add_lt_add_left ((ih fuel).1 t) _
      · intro a b he
        obtain ⟨a, rfl⟩ := e.symm.surjective a
        obtain ⟨b, rfl⟩ := e.symm.surjective b
        rcases a with a | a <;> rcases b with b | b
        · apply congrArg e.symm
          apply congrArg Sum.inl
          apply (ih maxTrue).2
          change highValue (maxTrue + 1) (Fin.cons false a.val) =
            highValue (maxTrue + 1) (Fin.cons false b.val) at he
          simpa [highValue_cons] using he
        · change highValue (maxTrue + 1) (Fin.cons false a.val) =
            highValue (maxTrue + 1) (Fin.cons true b.val) at he
          have ha := (ih maxTrue).1 a
          rw [hc] at ha
          simp only [highValue_cons, Bool.false_eq_true, ↓reduceIte, zero_add] at he
          omega
        · change highValue (maxTrue + 1) (Fin.cons true a.val) =
            highValue (maxTrue + 1) (Fin.cons false b.val) at he
          have hb := (ih maxTrue).1 b
          rw [hc] at hb
          simp only [highValue_cons, Bool.false_eq_true, ↓reduceIte, zero_add] at he
          omega
        · apply congrArg e.symm
          apply congrArg Sum.inr
          apply (ih fuel).2
          change highValue (maxTrue + 1) (Fin.cons true a.val) =
            highValue (maxTrue + 1) (Fin.cons true b.val) at he
          simpa [highValue_cons] using he

private theorem scanner_iff_literal (k n : ℕ) (hk : 0 < k) (w : Fin n → Bool) :
    DBonacciAdmissible k n w ↔ ∀ s : ℕ, ¬ TrueBlock w s k := by
  by_cases hkn : k ≤ n
  · exact (closed_word_run_start_equivalence n k hk hkn w).1
  · have hshort : n < k := by omega
    have ha : DBonacciAdmissible k n w := by
      cases k with
      | zero => omega
      | succ maxTrue =>
        exact runAdmissible_eq_true_of_length_le maxTrue maxTrue n w
          (by omega) le_rfl
    exact ⟨fun _ s hb => by have := hb.1; omega, fun _ => ha⟩

private theorem avoid_reverse {n k : ℕ} (w : Fin n → Bool)
    (hw : ∀ s : ℕ, ¬ TrueBlock w s k) :
    ∀ s : ℕ, ¬ TrueBlock (fun i => w i.rev) s k := by
  intro s hb
  have hlen := hb.1
  apply hw (n - (s + k))
  refine ⟨by omega, ?_⟩
  intro j hjlo hjhi
  have hj := j.isLt
  have hrev : s ≤ j.rev.val ∧ j.rev.val < s + k := by
    simp only [Fin.val_rev]
    omega
  simpa only [Fin.rev_rev] using hb.2 j.rev hrev.1 hrev.2

private theorem integerValue_highValue (k n : ℕ) (w : Fin n → Bool) :
    integerValue k w = (highValue k (fun i => w i.rev) : ℤ) := by
  unfold integerValue highValue
  simp only [Nat.cast_sum, apply_ite, Nat.cast_zero]
  simpa only [Fin.revPerm_apply, Fin.val_rev, Nat.sub_sub, Nat.add_comm] using
    (Equiv.sum_comp (Fin.revPerm : Equiv.Perm (Fin n))
      (fun i : Fin n => if w i then (dbonacci k (i.val + 2) : ℤ) else 0)).symm

/-- The specified integer sum bijects literal no-`k`-run words with the initial interval. -/
theorem integer_value_interval_bijection (k n : ℕ) (hk : 2 ≤ k) :
    Set.BijOn (integerValue k)
      {w : Fin n → Bool | ∀ s : ℕ, ¬ TrueBlock w s k}
      (Set.Ico (0 : ℤ) (dbonacci k (n + 2) : ℤ)) := by
  cases k with
  | zero => omega
  | succ maxTrue =>
    have hc : Fintype.card (BoundedRunName maxTrue maxTrue n) =
        dbonacci (maxTrue + 1) (n + 2) :=
      (dbonacci_name_card_eq_bounded maxTrue n).symm.trans
        (dbonacci_name_card (maxTrue + 1) n)
    let f : BoundedRunName maxTrue maxTrue n →
        Fin (dbonacci (maxTrue + 1) (n + 2)) := fun w =>
      ⟨highValue (maxTrue + 1) w.val, by
        rw [← hc]
        exact (bounded_value_spec maxTrue maxTrue n).1 w⟩
    have hf : Function.Bijective f := by
      apply (Fintype.bijective_iff_injective_and_card f).2
      constructor
      · intro a b he
        exact (bounded_value_spec maxTrue maxTrue n).2 (congrArg Fin.val he)
      · rw [Fintype.card_fin, hc]
    let reverseName (w : Fin n → Bool) (hw : ∀ s : ℕ, ¬ TrueBlock w s (maxTrue + 1)) :
        BoundedRunName maxTrue maxTrue n :=
      ⟨fun i => w i.rev,
        (scanner_iff_literal (maxTrue + 1) n (by omega) _).mpr (avoid_reverse w hw)⟩
    refine ⟨?_, ?_, ?_⟩
    · intro w hw
      change 0 ≤ integerValue (maxTrue + 1) w ∧
        integerValue (maxTrue + 1) w < (dbonacci (maxTrue + 1) (n + 2) : ℤ)
      rw [integerValue_highValue]
      constructor
      · exact Nat.cast_nonneg _
      · have hbound := (f (reverseName w hw)).isLt
        change highValue (maxTrue + 1) (fun i => w i.rev) < _ at hbound
        exact_mod_cast hbound
    · intro a ha b hb he
      rw [integerValue_highValue, integerValue_highValue] at he
      have hfin : f (reverseName a ha) = f (reverseName b hb) := by
        apply Fin.ext
        change highValue (maxTrue + 1) (fun i => a i.rev) =
          highValue (maxTrue + 1) (fun i => b i.rev)
        exact_mod_cast he
      have hword := congrArg Subtype.val (hf.1 hfin)
      change (fun i : Fin n => a i.rev) = (fun i : Fin n => b i.rev) at hword
      funext i
      simpa only [Fin.rev_rev] using congrFun hword i.rev
    · intro z hz
      have hzcast : (z.toNat : ℤ) = z := Int.toNat_of_nonneg hz.1
      have hzbound : z.toNat < dbonacci (maxTrue + 1) (n + 2) := by
        have hlt := hz.2
        omega
      obtain ⟨w, hw⟩ := hf.2 ⟨z.toNat, hzbound⟩
      refine ⟨fun i => w.val i.rev, ?_, ?_⟩
      · exact avoid_reverse w.val
          ((scanner_iff_literal (maxTrue + 1) n (by omega) w.val).mp w.property)
      · rw [integerValue_highValue]
        simp only [Fin.rev_rev]
        have hv := congrArg Fin.val hw
        change highValue (maxTrue + 1) w.val = z.toNat at hv
        rw [hv, hzcast]

end D5.S1.Words.AdmissibleWords.KBonacciIntegerInterval
