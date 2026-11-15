/- GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233158Row
   generality: I
   mirror-B: D5/B/S3/Combinatorics/TraceAvoidingArrays/HardinA233158Row
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233158Row.result; premises=D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233260Literal.pair_base
   digest: The literal 5-row three-state strip satisfies Hardin's order-7 recurrence. -/

/-
admission_basis: open-problem-resolution (#29231; Proved)
escape_witness: none (the alternating label equivalence and frozen proper-colouring
owner supply the count; the recurrence uses only a fixed finite identity and normalization).
U5: proof_shape=bind-only; consumers=counting_bridge, result
counting_bridge: proof_shape=bind-only; consumers=result
result: proof_shape=bind-only; consumers=Reg.Recurrence.family
-/
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233155ColumnTransfer
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233260Literal
import Mathlib.Tactic

/-! Alternating column labels identify sum exclusion with proper colouring. -/
namespace D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233158Row
open D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233155RowTransfer
open D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233155ColumnTransfer
open D5.S3.Combinatorics.TraceAvoidingArrays
open scoped BigOperators
set_option maxRecDepth 100000

def U5 (n : ℕ) : ℕ := HardinA233155RowTransfer.T n 5

private theorem counting_bridge (n : ℕ) : U5 n = HardinA233260Literal.L n := by
  classical
  rw [U5, T, HardinA233260Literal.L, ← Fintype.card_subtype, ← Fintype.card_subtype]
  exact Fintype.card_congr (properEquiv 5 n)

set_option maxHeartbeats 10000000 in
theorem result (n : ℕ) : (U5 (n + 12) : ℤ) =
    16 * (U5 (n + 11) : ℤ) - 64 * (U5 (n + 10) : ℤ) + 76 * (U5 (n + 9) : ℤ) + 17 * (U5 (n + 8) : ℤ)
    - 84 * (U5 (n + 7) : ℤ) + 48 * (U5 (n + 6) : ℤ) - 8 * (U5 (n + 5) : ℤ) := by
  simp_rw [counting_bridge]
  cases n with
  | zero =>
    have h := HardinA233260Literal.pair_base
    norm_num only [Nat.zero_add]
    linarith only [h]
  | succ n =>
    have h := HardinA233260Literal.pair_tail n
    simp only [Nat.succ_eq_add_one, Nat.add_assoc]
    linarith only [h]

end D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233158Row
