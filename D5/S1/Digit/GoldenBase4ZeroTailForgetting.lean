/- GID: D5/S1/Digit/GoldenBase4ZeroTailForgetting
   generality: I
   mirror-B: D5/B/S1/Digit/GoldenBase4ZeroTailForgetting
   mirror-E: none(waiver:actual-zero-tail-response)
   anchors: [mathlib/module/Mathlib.Logic.Function.Iterate]
   digest: Two or more terminal zeroes erase the transient state from the exact golden digit output; free tail readouts therefore add no constraint to a gap-only completion. -/

import D5.S1.Digit.GoldenBase4IntervalMachine
import Mathlib.Logic.Function.Iterate

/- The actual reference machine and its run semantics are reused. The finite
   table facts plus induction establish the all-depth statement. The final
   completion equivalence concerns independent readouts, not readouts required
   to come from one common recurrent zero map. No minimum-state bound is claimed.
   Logical review and exact executable checks were performed. This source has
   not been elaborated or kernel-checked in the authoring runtime. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Digit.GoldenBase4ZeroTailForgetting

open D5.S0.Automata.TypedPartialDFAOOverBase
open D5.S1.Digit.GoldenBase4IntervalMachine

private def negativeCore (q : Fin 21) : Prop := 1 ≤ q.val ∧ q.val ≤ 5
private def positiveCore (q : Fin 21) : Prop := 6 ≤ q.val ∧ q.val ≤ 9

private theorem negative_step : ∀ q : Fin 21, negativeCore q →
    positiveCore (zeroTarget q) ∧ output q = 3 := by decide

private theorem positive_step : ∀ q : Fin 21, positiveCore q →
    negativeCore (zeroTarget q) ∧ output q = 0 := by decide

private theorem enter_after_two : ∀ q : Fin 21, 14 ≤ q.val →
    negativeCore (zeroTarget (zeroTarget q)) := by decide

private def alternatingCore (n : Nat) (q : Fin 21) : Prop :=
  if n % 2 = 0 then negativeCore q else positiveCore q

private theorem alternating_step (n : Nat) (q : Fin 21)
    (h : alternatingCore n q) : alternatingCore (n + 1) (zeroTarget q) := by
  by_cases he : n % 2 = 0
  · have hn : (n + 1) % 2 ≠ 0 := by omega
    have hp : positiveCore (zeroTarget q) :=
      (negative_step q (by simpa [alternatingCore, he] using h)).1
    simpa [alternatingCore, hn] using hp
  · have hn : (n + 1) % 2 = 0 := by omega
    have hp : positiveCore q := by simpa [alternatingCore, he] using h
    simpa [alternatingCore, hn] using (positive_step q hp).1

private theorem orbit_alternates (q : Fin 21) (h : negativeCore q) (n : Nat) :
    alternatingCore n ((zeroTarget^[n]) q) := by
  induction n with
  | zero => simpa [alternatingCore] using h
  | succ n ih =>
      have hs : (zeroTarget^[n + 1]) q = zeroTarget ((zeroTarget^[n]) q) := by
        rw [Nat.add_comm n 1, Function.iterate_add_apply]
        rfl
      rw [hs]
      exact alternating_step n _ ih

private theorem zero_run (q : Fin 21) (n : Nat) :
    machine.runFrom q (List.replicate n 0) = some ((zeroTarget^[n]) q) := by
  induction n generalizing q with
  | zero => rfl
  | succ n ih =>
      change machine.runFrom (zeroTarget q) (List.replicate n 0) = _
      simpa only [Function.iterate_succ_apply] using ih (zeroTarget q)

/-- The digit determined solely by the parity of at least two terminal zeroes. -/
def longTailDigit (n : Nat) : Fin 4 := if n % 2 = 0 then 3 else 0

/-- Every previous-one reference state has the same output after n+2 zeroes.
The statement covers all depths and uses the original Option-valued run. -/
theorem zero_tail_output (q : Fin 21) (hq : 14 ≤ q.val) (n : Nat) :
    (machine.runFrom q (List.replicate (n + 2) 0)).map output =
      some (longTailDigit (n + 2)) := by
  have h := orbit_alternates (zeroTarget (zeroTarget q)) (enter_after_two q hq) n
  have hs : (zeroTarget^[n + 2]) q =
      (zeroTarget^[n]) (zeroTarget (zeroTarget q)) := by
    rw [Function.iterate_add_apply]
    rfl
  rw [zero_run, hs]
  simp only [Option.map_some]
  apply congrArg some
  by_cases he : n % 2 = 0
  · have hp : (n + 2) % 2 = 0 := by omega
    have hn : negativeCore ((zeroTarget^[n]) (zeroTarget (zeroTarget q))) := by
      simpa [alternatingCore, he] using h
    simpa [longTailDigit, hp] using (negative_step _ hn).2
  · have hp : (n + 2) % 2 ≠ 0 := by omega
    have hn : positiveCore ((zeroTarget^[n]) (zeroTarget (zeroTarget q))) := by
      simpa [alternatingCore, he] using h
    simpa [longTailDigit, hp] using (positive_step _ hn).2

/-- The same parity law is the exact arithmetic digit of every successful
prefix ending in the previous-one fiber, followed by at least two zeroes. -/
theorem zero_tail_arithmetic_digit (prefix : List (Fin 2)) (q : Fin 21)
    (hp : machine.run prefix = some q) (hq : 14 ≤ q.val) (n : Nat) :
    ⌊4 * (Real.goldenRatio * (fibPair (prefix ++ List.replicate (n + 2) 0)).1)⌋ -
      4 * ⌊Real.goldenRatio * (fibPair (prefix ++ List.replicate (n + 2) 0)).1⌋ =
        ((longTailDigit (n + 2)).val : Int) := by
  have hr : machine.run (prefix ++ List.replicate (n + 2) 0) =
      some ((zeroTarget^[n + 2]) q) := by
    change machine.runFrom machine.start (prefix ++ List.replicate (n + 2) 0) = _
    rw [machine.runFrom_append]
    change (machine.run prefix).bind _ = _
    rw [hp]
    exact zero_run q (n + 2)
  have ho : output ((zeroTarget^[n + 2]) q) = longTailDigit (n + 2) := by
    simpa only [zero_run, Option.map_some, Option.some.injEq] using
      zero_tail_output q hq n
  exact (successful_run_digit _ _ hr).trans
    (congrArg (fun d : Fin 4 => (d.val : Int)) ho)

/-- A free family of terminal readouts can always absorb the long-tail labels.
Thus these observations impose no further restriction on any fixed trace or
shared gap maps, beyond the observations at tail lengths zero and one. -/
theorem free_tail_completion_iff {Index State : Type*}
    (trace : Index → State) (tail : Index → Nat) (label : Index → Fin 4)
    (G E : State → Fin 4)
    (longLabels : ∀ i, 2 ≤ tail i → label i = longTailDigit (tail i)) :
    (∃ readout : Nat → State → Fin 4,
      readout 0 = G ∧ readout 1 = E ∧
      ∀ i, readout (tail i) (trace i) = label i) ↔
    (∀ i, tail i = 0 → G (trace i) = label i) ∧
      (∀ i, tail i = 1 → E (trace i) = label i) := by
  constructor
  · rintro ⟨readout, hG, hE, fits⟩
    constructor
    · intro i hi
      simpa only [hi, hG] using fits i
    · intro i hi
      simpa only [hi, hE] using fits i
  · rintro ⟨hG, hE⟩
    let readout : Nat → State → Fin 4 := fun k q =>
      if k = 0 then G q else if k = 1 then E q else longTailDigit k
    refine ⟨readout, ?_, ?_, ?_⟩
    · funext q
      simp [readout]
    · funext q
      simp [readout]
    · intro i
      by_cases hz : tail i = 0
      · simpa [readout, hz] using hG i hz
      · by_cases ho : tail i = 1
        · simpa [readout, hz, ho] using hE i ho
        · simpa [readout, hz, ho] using (longLabels i (by omega)).symm

#print axioms zero_tail_output
#print axioms zero_tail_arithmetic_digit
#print axioms free_tail_completion_iff

end D5.S1.Digit.GoldenBase4ZeroTailForgetting
