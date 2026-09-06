/- GID: D5/S1/Recurrence/ConvolutionRecurrenceOddPowersOfTwo
   generality: I
   mirror-B: D5/B/S1/Recurrence/ConvolutionRecurrenceOddPowersOfTwo
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: The convolution recurrence A397588 is odd exactly at powers of two. -/

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.ZMod.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Finset

namespace D5.S1.Recurrence.ConvolutionRecurrenceOddPowersOfTwo

/-- OEIS A397588, with its source recurrence on positive indices.
The empty sum extends the sequence by `a 0 = 0` outside the source domain. -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.lt_wfRel.wf.fix (fun n rec =>
    if n = 1 then 1 else
      (n + 1) * ∑ k ∈ (Icc 1 (n - 1)).attach,
        rec k.val (by change k.val < n; have hk := mem_Icc.mp k.property; omega) *
          rec (n - k.val) (by change n - k.val < n; have hk := mem_Icc.mp k.property; omega)) n

private theorem a_eq (n : ℕ) :
    a n = if n = 1 then 1 else
      (n + 1) * ∑ k ∈ (Icc 1 (n - 1)).attach, a k.val * a (n - k.val) := by
  exact Nat.lt_wfRel.wf.fix_eq _ n

/-- The source initial value. -/
theorem a_one : a 1 = 1 := by
  rw [a_eq]
  simp

/-- The source convolution formula at every index greater than one. -/
theorem a_recurrence {n : ℕ} (hn : 1 < n) :
    a n = (n + 1) * ∑ k ∈ Icc 1 (n - 1), a k * a (n - k) := by
  rw [a_eq, if_neg (by omega)]
  exact congrArg (fun t => (n + 1) * t)
    (sum_attach (Icc 1 (n - 1)) (fun k => a k * a (n - k)))

/-- Reflection cancels every off-diagonal convolution term modulo two. -/
theorem convolution_pairing (f : ℕ → ZMod 2) {m : ℕ} (hm : 1 ≤ m) :
    (∑ k ∈ Icc 1 (2 * m - 1), f k * f (2 * m - k)) = f m ^ 2 := by
  have hmem : m ∈ Icc 1 (2 * m - 1) := by
    simp only [mem_Icc]
    omega
  have hcancel :
      (∑ k ∈ (Icc 1 (2 * m - 1)).erase m, f k * f (2 * m - k)) = 0 := by
    apply sum_involution (fun k _ => 2 * m - k)
    · intro k hk
      have hbounds := mem_Icc.mp (mem_erase.mp hk).2
      have hreflect : 2 * m - (2 * m - k) = k := by omega
      rw [hreflect, mul_comm (f (2 * m - k)) (f k)]
      exact CharTwo.add_self_eq_zero _
    · intro k hk _
      have hb := mem_erase.mp hk
      have hbounds := mem_Icc.mp hb.2
      omega
    · intro k hk
      have hb := mem_erase.mp hk
      have hbounds := mem_Icc.mp hb.2
      simp only [mem_erase, mem_Icc]
      omega
    · intro k hk
      have hbounds := mem_Icc.mp (mem_erase.mp hk).2
      omega
  rw [← sum_erase_add _ _ hmem, hcancel, zero_add]
  rw [show 2 * m - m = m by omega, pow_two]

/-- The even-index reduction factors through the midpoint square modulo two. -/
theorem a_halving_via_square {m : ℕ} (hm : 1 ≤ m) :
    ((a (2 * m) : ZMod 2) = (a m : ZMod 2) ^ 2) ∧
      ((a m : ZMod 2) ^ 2 = (a m : ZMod 2)) := by
  constructor
  · rw [a_recurrence (by omega)]
    push_cast
    have htwo : (2 : ZMod 2) = 0 := rfl
    simp only [htwo, zero_mul, zero_add, one_mul]
    exact convolution_pairing (fun k => (a k : ZMod 2)) hm
  · exact (by decide : ∀ x : ZMod 2, x ^ 2 = x) _

/-- Halving a positive even index preserves the sequence value modulo two. -/
theorem a_halving {m : ℕ} (hm : 1 ≤ m) :
    (a (2 * m) : ZMod 2) = (a m : ZMod 2) := by
  rw [a_recurrence (by omega)]
  push_cast
  have htwo : (2 : ZMod 2) = 0 := rfl
  simp only [htwo, zero_mul, zero_add, one_mul]
  rw [convolution_pairing (fun k => (a k : ZMod 2)) hm]
  exact (by decide : ∀ x : ZMod 2, x ^ 2 = x) _

/-- At every odd index greater than one, the sequence is zero modulo two. -/
theorem a_odd_index_zero {n : ℕ} (hn : 1 < n) (hodd : Odd n) :
    (a n : ZMod 2) = 0 := by
  rw [a_recurrence hn, Nat.cast_mul]
  have hfactor : Even (n + 1) := Nat.even_add_one.mpr (Nat.not_even_iff_odd.mpr hodd)
  rw [hfactor.natCast_zmod_two, zero_mul]

/-- The parity conjecture stated in OEIS A397588 on July 3, 2026. -/
theorem a_odd_iff_power_two : ∀ n : ℕ, 1 ≤ n → (Odd (a n) ↔ ∃ r : ℕ, n = 2 ^ r) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    by_cases h1 : n = 1
    · subst n
      constructor
      · intro _
        exact ⟨0, rfl⟩
      · intro _
        rw [a_one]
        exact odd_one
    have hn1 : 1 < n := by omega
    obtain ⟨m, hnm | hnm⟩ := Nat.even_or_odd' n
    · subst n
      have hm : 1 ≤ m := by omega
      rw [← ZMod.natCast_eq_one_iff_odd, a_halving hm,
        ZMod.natCast_eq_one_iff_odd, ih m (by omega) hm]
      constructor
      · rintro ⟨r, hr⟩
        exact ⟨r + 1, by rw [hr, pow_succ, Nat.mul_comm]⟩
      · rintro ⟨r, hr⟩
        cases r with
        | zero => simp only [pow_zero] at hr; omega
        | succ r =>
          refine ⟨r, ?_⟩
          rw [pow_succ] at hr
          omega
    · subst n
      have ho : Odd (2 * m + 1) := odd_two_mul_add_one m
      constructor
      · intro ha
        have hc := ha.natCast_zmod_two
        rw [a_odd_index_zero hn1 ho] at hc
        exact (zero_ne_one hc).elim
      · rintro ⟨r, hr⟩
        exfalso
        cases r with
        | zero => simp only [pow_zero] at hr; omega
        | succ r => rw [pow_succ] at hr; omega

-- Fidelity: the hypotheses co-occur, and both sides have independent concrete values.
example : ℕ → ZMod 2 := fun _ => 1
example : ∃ m : ℕ, 1 ≤ m := ⟨1, le_rfl⟩
example : ∃ n : ℕ, 1 < n ∧ Odd n := ⟨3, by decide⟩
example : a 0 = 0 := by rw [a_eq]; simp
example : a 1 = 1 := by decide +kernel
example : a 2 = 3 := by decide +kernel
example : a 3 = 24 := by decide +kernel
example : a 4 = 285 := by decide +kernel
example : a 8 = 34237485 := by decide +kernel

#print axioms a
#print axioms a_one
#print axioms a_recurrence
#print axioms convolution_pairing
#print axioms a_halving_via_square
#print axioms a_halving
#print axioms a_odd_index_zero
#print axioms a_odd_iff_power_two

run_cmd do
  for (consumer, provider) in
      [( ``a_odd_iff_power_two, ``a_halving),
       ( ``a_odd_iff_power_two, ``a_odd_index_zero),
       ( ``a_halving_via_square, ``convolution_pairing),
       ( ``a_halving, ``convolution_pairing)] do
    let some info := (← Lean.getEnv).checked.get.find? consumer
      | throwError "Missing declaration: {consumer}"
    let some value := info.value? (allowOpaque := true)
      | throwError "Missing proof body: {consumer}"
    unless value.getUsedConstants.contains provider do
      throwError "Missing elaborated dependency: {consumer} -> {provider}"
    Lean.logInfo m!"ELABORATED_DEPENDENCY {consumer} -> {provider}"

end D5.S1.Recurrence.ConvolutionRecurrenceOddPowersOfTwo
