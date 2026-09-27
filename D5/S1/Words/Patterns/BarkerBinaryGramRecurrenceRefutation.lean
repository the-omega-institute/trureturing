/- GID: D5/S1/Words/Patterns/BarkerBinaryGramRecurrenceRefutation
   generality: I
   mirror-B: D5/B/S1/Words/Patterns/BarkerBinaryGramRecurrenceRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=bounded-enumeration; basis=refutes=gid:D5/S1/Words/Patterns/BarkerBinaryGramRecurrenceRefutation.claim; result=D5/S1/Words/Patterns/BarkerBinaryGramRecurrenceRefutation.result; claim=D5/S1/Words/Patterns/BarkerBinaryGramRecurrenceRefutation.claim
   digest: The n = 4 term refutes Barker's published recurrence for OEIS A181278. -/

import Mathlib.Data.List.Count

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.Patterns.BarkerBinaryGramRecurrenceRefutation

/-!
OEIS A181278 counts ordered pairs of length-`n` binary rows. The rows are
strictly increasing, while the rows of their Gram matrix modulo two are
strictly decreasing in lexicographic order, with the first Gram entry as the
high digit.

Colin Barker's published recurrence is stated for `n > 3`. At `n = 4`, its
left side is `48`, while its right side is `4 * 11 + 4 * 3 = 56` because the
term at index one is zero.
-/

/-- The number of ordered binary row pairs satisfying the A181278 row and
modulo-two Gram-row order conditions. -/
def a181278 (n : Nat) : Nat :=
  ((List.range (2 ^ n)).product (List.range (2 ^ n))).countP fun (p : Nat × Nat) =>
    let parity (r : Nat) := ((List.range n).filter (fun i => r.testBit i)).length % 2
    let dot := ((List.range n).filter (fun i => p.1.testBit i && p.2.testBit i)).length % 2
    decide (And (p.1 < p.2) (2 * parity p.1 + dot > 2 * dot + parity p.2))

/-- Barker's published recurrence, with `n > 3` written as `4 <= n` and
without subtraction of natural-valued sequence terms. -/
def claim : Prop :=
  forall n : Nat, 4 <= n ->
    a181278 n + 16 * a181278 (n - 3) =
      4 * a181278 (n - 1) + 4 * a181278 (n - 2)

/-- The published recurrence fails at `n = 4`. -/
theorem result : Not claim := by
  have h1 : a181278 1 = 0 := by decide +kernel
  have h2 : a181278 2 = 3 := by decide +kernel
  have h3 : a181278 3 = 11 := by decide +kernel
  have h4 : a181278 4 = 48 := by decide +kernel
  intro hclaim
  have hrec := hclaim 4 (by decide +kernel)
  rw [show (4 : Nat) - 3 = 1 from rfl, show (4 : Nat) - 1 = 3 from rfl,
    show (4 : Nat) - 2 = 2 from rfl] at hrec
  rw [h4, h3, h2, h1] at hrec
  exact (by decide +kernel : Not ((48 : Nat) = 56)) hrec

#print axioms a181278
#print axioms claim
#print axioms result

end D5.S1.Words.Patterns.BarkerBinaryGramRecurrenceRefutation
