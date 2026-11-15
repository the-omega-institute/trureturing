/- GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233156Row
   generality: I
   mirror-B: D5/B/S3/Combinatorics/TraceAvoidingArrays/HardinA233156Row
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233156Row.result; premises=D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233258PairTransfer.count_transfer
   digest: The literal 3-row three-state strip satisfies Hardin's order-2 recurrence. -/

/-
admission_basis: open-problem-resolution (#29231; Proved)
escape_witness: none (the alternating label equivalence and frozen proper-colouring
owner supply the count; the recurrence uses only a fixed finite identity and normalization).
U3: proof_shape=bind-only; consumers=counting_bridge, result
counting_bridge: proof_shape=bind-only; consumers=result
result: proof_shape=bind-only; consumers=Reg.Recurrence.family
-/
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233155ColumnTransfer
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233258PairTransfer
import Mathlib.Tactic

/-! Alternating column labels identify sum exclusion with proper colouring. -/
namespace D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233156Row
open D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233155RowTransfer
open D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233155ColumnTransfer
open D5.S3.Combinatorics.TraceAvoidingArrays
open scoped BigOperators
set_option maxRecDepth 100000

def U3 (n : ℕ) : ℕ := HardinA233155RowTransfer.T n 3

private theorem counting_bridge (n : ℕ) : U3 n = HardinA233258PairTransfer.L n := by
  classical
  rw [U3, T, HardinA233258PairTransfer.L, ← Fintype.card_subtype, ← Fintype.card_subtype]
  exact Fintype.card_congr (properEquiv 3 n)

set_option maxHeartbeats 10000000 in
theorem result (n : ℕ) : (U3 (n + 5) : ℤ) =
    5 * (U3 (n + 4) : ℤ) - 2 * (U3 (n + 3) : ℤ) := by
  simp_rw [counting_bridge]
  let Q := HardinA233258PairTransfer.Q
  let w := HardinA233258PairTransfer.weights
  cases n with
  | zero =>
    have h1 := HardinA233258PairTransfer.initial_values (1 : Fin 6)
    have h2 := HardinA233258PairTransfer.initial_values (2 : Fin 6)
    have h3 := HardinA233258PairTransfer.initial_values (3 : Fin 6)
    change (HardinA233258PairTransfer.L 3 : ℤ) = 432 at h1
    change (HardinA233258PairTransfer.L 4 : ℤ) = 1944 at h2
    change (HardinA233258PairTransfer.L 5 : ℤ) = 8856 at h3
    rw [h1, h2, h3]
    norm_num
  | succ n =>
    have hc : (Q ^ (2 + 2)).mulVec (1 : Fin 5 → ℤ) =
        ∑ j : Fin 2, (![-2, 5] : Fin 2 → ℤ) j •
          (Q ^ (2 + j.val)).mulVec (1 : Fin 5 → ℤ) := by
      rw [show 2 + 2 = (4 : Fin 6).val from rfl,
        HardinA233258PairTransfer.powers_table]
      have hh (j : Fin 2) : (Q ^ (2 + j.val)).mulVec (1 : Fin 5 → ℤ) =
          HardinA233258PairTransfer.W ⟨2 + j.val, by omega⟩ :=
        HardinA233258PairTransfer.powers_table ⟨2 + j.val, by omega⟩
      simp_rw [hh]
      exact List.ofFn_inj.mp (by decide +kernel)
    have h := TransferMatrix.scalarRelationShift Q w 2 2
      (![-2, 5] : Fin 2 → ℤ) hc n
    have hb (k : ℕ) : dotProduct w ((Q ^ k).mulVec (1 : Fin 5 → ℤ)) =
        (HardinA233258PairTransfer.L (k + 2) : ℤ) :=
      (HardinA233258PairTransfer.count_transfer k).symm
    simp_rw [hb] at h
    norm_num only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ,
      Matrix.cons_val_zero, Matrix.cons_val_succ, Finset.sum_empty,
      add_zero, Nat.add_assoc] at h
    simp only [Nat.succ_eq_add_one, Nat.add_assoc]
    linarith only [h]

end D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233156Row
