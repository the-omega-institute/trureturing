/- GID: D5/S1/Digit/GoldenBase4DenseInput
   generality: I
   mirror-B: D5/B/S1/Digit/GoldenBase4DenseInput
   mirror-E: none(waiver:canonical-input-transport)
   anchors: [mathlib/module/Mathlib.Data.Nat.Fib.Zeckendorf]
   digest: The existing M01 dense Zeckendorf words have their stated Fibonacci value and legal base runs, transporting the interval machine to the exact powers-only specification. -/

import D5.S1.Digit.GoldenBase4IntervalMachine
import D5.S1.Digit.GoldenBase4AutomataOracle
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/- The M01 input and digit definitions are used unchanged. The range expansion
   below is a value lemma for an arbitrary bit family, not a new encoder.
   Canonicality and decoding come from WDigits and upstream Zeckendorf.
   The proof scripts have been logically reviewed; pinned Lean elaboration has
   not been executed in this session. No sparse minimality theorem is claimed. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Digit.GoldenBase4DenseInput

open D5.S0.Conventions
open D5.S0.Automata.TypedPartialDFAOOverBase
open D5.S1.Digit.GoldenBase4AutomataOracle
open D5.S1.Digit.GoldenBase4IntervalMachine
open scoped BigOperators

private instance : IsTrans Nat (fun a b => b + 2 ≤ a) where
  trans _ _ _ hab hbc := by omega

private theorem occupied_pairwise (n : Nat) :
    (wdigits n ++ [0]).Pairwise (fun a b => b + 2 ≤ a) := by
  simpa only [List.IsZeckendorfRep, List.isChain_iff_pairwise] using
    wdigits_isCanonical n

private theorem occupied_lower (n j : Nat) (hj : j ∈ wdigits n) : 2 ≤ j := by
  have h := (List.pairwise_append.mp (occupied_pairwise n)).2.2
  simpa using h j hj 0 (by simp)

private theorem gap_nodup (l : List Nat) :
    l.Pairwise (fun a b => b + 2 ≤ a) → l.Nodup := by
  induction l with
  | nil => simp
  | cons a l ih =>
      intro h
      obtain ⟨ha, hl⟩ := List.pairwise_cons.mp h
      apply List.nodup_cons.mpr
      refine ⟨?_, ih hl⟩
      intro hm
      have := ha a hm
      omega

private theorem gap_no_consecutive (l : List Nat) :
    l.Pairwise (fun a b => b + 2 ≤ a) → ∀ j, j ∈ l → j + 1 ∉ l := by
  induction l with
  | nil => simp
  | cons a l ih =>
      intro h
      obtain ⟨ha, hl⟩ := List.pairwise_cons.mp h
      intro j hj hk
      simp only [List.mem_cons] at hj hk
      rcases hj with rfl | hj
      · rcases hk with heq | hk
        · omega
        · have := ha (a + 1) hk
          omega
      · rcases hk with heq | hk
        · have := ha j hj
          omega
        · exact ih hl j hj hk

/-- Every occupied upstream index is inside the existing M01 display range. -/
theorem occupied_index_bounds (n j : Nat) (hj : j ∈ wdigits n) :
    2 ≤ j ∧ j < zeckendorfWordLength n + 2 := by
  have hlow := occupied_lower n j hj
  refine ⟨hlow, ?_⟩
  have hp := (List.pairwise_append.mp (occupied_pairwise n)).1
  cases hw : wdigits n with
  | nil => simp [hw] at hj
  | cons a l =>
      have ha : 2 ≤ a := occupied_lower n a (by simp [hw])
      rw [hw] at hp
      have htop := (List.pairwise_cons.mp hp).1
      have hja : j ≤ a := by
        rw [hw] at hj
        rcases List.mem_cons.mp hj with rfl | hj
        · exact le_rfl
        · have := htop j hj
          omega
      simp only [zeckendorfWordLength, hw]
      omega

/-- Evaluation of a descending dense bit display is the upstream weighted sum. -/
theorem dense_fibonacci_value (bits : Nat → Fin 2) (k : Nat) :
    (fibPair ((List.range k).reverse.map bits)).1 =
      ∑ i ∈ Finset.range k, (bits i).val * Nat.fib (i + 2) := by
  induction k with
  | zero => simp [fibPair]
  | succ k ih =>
      simp [List.range_succ, List.reverse_append, fibPair, ih,
        Finset.sum_range_succ, Nat.add_comm]

private theorem sum_toFinset_fib (l : List Nat) :
    l.Nodup → (∑ j ∈ l.toFinset, Nat.fib j) = (l.map Nat.fib).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
      intro hn
      obtain ⟨ha, hl⟩ := List.nodup_cons.mp hn
      simp [ha, ih hl]

/-- The exact input definition already used by M01 evaluates to its argument. -/
theorem zeckendorfMSDWord_value (n : Nat) :
    (fibPair (zeckendorfMSDWord n)).1 = n := by
  classical
  let k := zeckendorfWordLength n
  let s := (Finset.range k).filter (fun i => i + 2 ∈ wdigits n)
  have hb (i : Nat) : (zeckendorfBit n i).val * Nat.fib (i + 2) =
      if i + 2 ∈ wdigits n then Nat.fib (i + 2) else 0 := by
    by_cases h : i + 2 ∈ wdigits n <;> simp [zeckendorfBit, h]
  have hs : (∑ i ∈ s, Nat.fib (i + 2)) =
      ∑ j ∈ (wdigits n).toFinset, Nat.fib j := by
    apply Finset.sum_bij (fun i _ => i + 2)
    · intro i hi
      exact List.mem_toFinset.mpr (Finset.mem_filter.mp hi).2
    · intro i hi j hj hij
      omega
    · intro j hj
      have hm : j ∈ wdigits n := List.mem_toFinset.mp hj
      obtain ⟨hl, hu⟩ := occupied_index_bounds n j hm
      refine ⟨j - 2, ?_, by omega⟩
      apply Finset.mem_filter.mpr
      constructor
      · apply Finset.mem_range.mpr
        dsimp [k]
        omega
      · simpa [Nat.sub_add_cancel hl] using hm
    · intro i hi
      rfl
  rw [zeckendorfMSDWord, dense_fibonacci_value]
  simp_rw [hb]
  change (∑ i ∈ Finset.range k,
    if i + 2 ∈ wdigits n then Nat.fib (i + 2) else 0) = n
  rw [← Finset.sum_filter]
  change (∑ i ∈ s, Nat.fib (i + 2)) = n
  rw [hs, sum_toFinset_fib]
  · exact decode_wdigits n
  · exact gap_nodup _ (List.pairwise_append.mp (occupied_pairwise n)).1

private theorem bit_one_iff (n i : Nat) :
    zeckendorfBit n i = 1 ↔ i + 2 ∈ wdigits n := by simp [zeckendorfBit]

private theorem bit_zero_iff (n i : Nat) :
    zeckendorfBit n i = 0 ↔ i + 2 ∉ wdigits n := by simp [zeckendorfBit]

private theorem occupied_bits_separated (n i : Nat)
    (h : zeckendorfBit n (i + 1) = 1) : zeckendorfBit n i = 0 := by
  rw [bit_zero_iff]
  intro hi
  have sep := gap_no_consecutive _
    (List.pairwise_append.mp (occupied_pairwise n)).1 (i + 2) hi
  exact sep (by simpa [Nat.add_assoc] using (bit_one_iff n (i + 1)).mp h)

private theorem fin_two_one_of_ne_zero (a : Fin 2) (h : a ≠ 0) : a = 1 := by
  apply Fin.ext
  have ha := a.isLt
  have hn : a.val ≠ 0 := by intro hz; exact h (Fin.ext hz)
  omega

/-- A descending display of separated bits has a legal base run. The guard
handles entry from the previous-one type without introducing an illegal prefix. -/
theorem separated_bits_run (bits : Nat → Fin 2)
    (sep : ∀ i, bits (i + 1) = 1 → bits i = 0) (k : Nat)
    (q : BinaryZeckendorfState)
    (guard : q = .previousOne → ∀ i, i + 1 = k → bits i = 0) :
    ∃ b, binaryZeckendorfBase.evalFrom q
      ((List.range k).reverse.map bits) = some b := by
  induction k generalizing q with
  | zero => exact ⟨q, rfl⟩
  | succ k ih =>
      by_cases ha : bits k = 0
      · obtain ⟨b, hb⟩ := ih .previousZero (by intro h; cases h)
        refine ⟨b, ?_⟩
        simpa [List.range_succ, List.reverse_append, PartialDFA.evalFrom,
          runTransition, binaryZeckendorfBase, ha] using hb
      · have hone : bits k = 1 := fin_two_one_of_ne_zero _ ha
        have hq : q = .previousZero := by
          cases q with
          | previousZero => rfl
          | previousOne => exact False.elim (ha (guard rfl k rfl))
        have g : BinaryZeckendorfState.previousOne = .previousOne →
            ∀ i, i + 1 = k → bits i = 0 := by
          intro _ i hi
          apply sep i
          simpa [hi] using hone
        obtain ⟨b, hb⟩ := ih .previousOne g
        refine ⟨b, ?_⟩
        simpa [List.range_succ, List.reverse_append, PartialDFA.evalFrom,
          runTransition, binaryZeckendorfBase, hq, hone] using hb

/-- The existing M01 canonical input is accepted by the shared typed base. -/
theorem zeckendorfMSDWord_legal (n : Nat) :
    ∃ b, binaryZeckendorfBase.eval (zeckendorfMSDWord n) = some b := by
  exact separated_bits_run (zeckendorfBit n) (occupied_bits_separated n)
    (zeckendorfWordLength n) .previousZero (by intro h; cases h)

/-- The interval machine satisfies the original M01 power word and digit
functions, with no replacement encoder and no finite sample premise. -/
theorem base4PowerWord_correct (i : Nat) :
    machine.evalOutput (base4PowerWord i) = some (base4GoldenDigit i) := by
  obtain ⟨b, hb⟩ := zeckendorfMSDWord_legal (4 ^ i)
  obtain ⟨q, hq, hd⟩ := every_legal_word_correct
    (zeckendorfMSDWord (4 ^ i)) b hb
  rw [zeckendorfMSDWord_value] at hd
  have e1 : Real.goldenRatio * ((4 ^ i : Nat) : Real) =
      (4 : Real) ^ i * Real.goldenRatio := by push_cast; ring
  have e4 : 4 * (Real.goldenRatio * ((4 ^ i : Nat) : Real)) =
      (4 : Real) ^ (i + 1) * Real.goldenRatio := by
    push_cast
    rw [pow_succ]
    ring
  rw [e4, e1] at hd
  change base4DigitInt i = ((output q).val : Int) at hd
  have ho : output q = base4GoldenDigit i := by
    apply Fin.ext
    rw [base4GoldenDigit_val, hd]
    simp
  change (machine.run (zeckendorfMSDWord (4 ^ i))).map output =
    some (base4GoldenDigit i)
  rw [hq]
  exact congrArg some ho

/-- A concrete twenty-one-state witness with both published initial anchors. -/
theorem twenty_one_state_power_witness :
    ∃ M : TypedPartialDFAO binaryZeckendorfBase (Fin 4) (Fin 21),
      (∀ i, M.evalOutput (base4PowerWord i) = some (base4GoldenDigit i)) ∧
      M.step M.start 0 = some M.start ∧ M.output M.start = 0 := by
  exact ⟨machine, base4PowerWord_correct, rfl, rfl⟩

#print axioms zeckendorfMSDWord_value
#print axioms zeckendorfMSDWord_legal
#print axioms twenty_one_state_power_witness

end D5.S1.Digit.GoldenBase4DenseInput
