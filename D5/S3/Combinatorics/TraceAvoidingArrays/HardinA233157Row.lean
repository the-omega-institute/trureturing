/- GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233157Row
   generality: I
   mirror-B: D5/B/S3/Combinatorics/TraceAvoidingArrays/HardinA233157Row
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233157Row.result; premises=D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233157Row.finite_certificate
   digest: The literal 4-row three-state strip satisfies Hardin's order-3 recurrence. -/

/-
admission_basis: open-problem-resolution (#29231; Proved)
escape_witness: none (properEquiv and the frozen A233259 count supply the all-length
bridge; the finite relation uses the frozen Q, W and powers_table by normalization).
U4: proof_shape=bind-only; consumers=counting_bridge, result
finite_certificate: proof_shape=bind-only; consumers=result
counting_bridge: proof_shape=bind-only; consumers=result
result: proof_shape=bind-only; consumers=Reg.Recurrence.family
-/
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233155ColumnTransfer
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233259PairTransferCore
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233259PairTransferPowers
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233259PairTransferCount
import D5.S3.Combinatorics.TraceAvoidingArrays.TransferMatrix
import Mathlib.Tactic

/-! Alternating column labels identify sum exclusion with proper colouring. -/
namespace D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233157Row
open D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233155RowTransfer
open D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233155ColumnTransfer (properEquiv)
open D5.S3.Combinatorics.TraceAvoidingArrays
open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233259PairTransferCore
  (Q Proper L weights)
open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233259PairTransferPowers
  (W powers_table)
open scoped BigOperators
set_option maxRecDepth 100000

def U4 (n : ℕ) : ℕ := HardinA233155RowTransfer.T n 4

set_option maxHeartbeats 10000000 in
theorem finite_certificate :
    (Q ^ (4 + 3)).mulVec (1 : Fin 14 → ℤ) =
      ∑ j : Fin 3, (![6, -15, 9] : Fin 3 → ℤ) j •
        (Q ^ (4 + j.val)).mulVec (1 : Fin 14 → ℤ) := by
  rw [show 4 + 3 = (7 : Fin 9).val from rfl, powers_table]
  have hh (j : Fin 3) : (Q ^ (4 + j.val)).mulVec (1 : Fin 14 → ℤ) =
      W ⟨4 + j.val, by omega⟩ := powers_table ⟨4 + j.val, by omega⟩
  simp_rw [hh]
  exact List.ofFn_inj.mp (by decide +kernel)

private theorem counting_bridge (n : ℕ) :
    (U4 (n + 2) : ℤ) = dotProduct weights
      ((Q ^ n).mulVec (1 : Fin 14 → ℤ)) := by
  classical
  have hc (m : ℕ) : U4 m = L m := by
    rw [U4, T, L, ← Fintype.card_subtype, ← Fintype.card_subtype]
    let e : {f : Fin 4 × Fin m → Fin 3 // Legal f} ≃
        {P : Fin 4 × Fin m → Fin 3 // Proper P} :=
      (properEquiv 4 m).trans (Equiv.subtypeEquiv (Equiv.refl _)
        (fun P => by
          constructor
          · intro h j hj r s hrs
            exact h j hj s r (by rcases hrs with h | h; exact Or.inl h.symm; exact Or.inr h.symm)
          · intro h j hj r s hrs
            exact h j hj s r (by rcases hrs with h | h; exact Or.inl h.symm; exact Or.inr h.symm)))
    exact Fintype.card_congr e
  rw [hc]
  exact HardinA233259PairTransferCount.count_transfer n

set_option maxHeartbeats 10000000 in
theorem result (n : ℕ) : (U4 (n + 8) : ℤ) =
    9 * (U4 (n + 7) : ℤ) - 15 * (U4 (n + 6) : ℤ) + 6 * (U4 (n + 5) : ℤ) := by
  cases n with
  | zero =>
    norm_num only [Nat.zero_add]
    rw [counting_bridge 6, counting_bridge 5, counting_bridge 4, counting_bridge 3]
    rw [show 6 = (6 : Fin 9).val from rfl, powers_table,
      show 5 = (5 : Fin 9).val from rfl, powers_table,
      show 4 = (4 : Fin 9).val from rfl, powers_table,
      show 3 = (3 : Fin 9).val from rfl, powers_table]
    decide +kernel
  | succ n =>
    have h := TransferMatrix.scalarRelationShift Q weights 3 4
      (![6, -15, 9] : Fin 3 → ℤ) finite_certificate n
    have hb (j : ℕ) : dotProduct weights
        ((Q ^ (n + 4 + j)).mulVec (1 : Fin 14 → ℤ)) =
          (U4 (n + 4 + j + 2) : ℤ) := (counting_bridge _).symm
    simp_rw [hb] at h
    norm_num only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ,
      Matrix.cons_val_zero, Matrix.cons_val_succ, Finset.sum_empty,
      add_zero, Nat.add_assoc] at h
    simp only [Nat.succ_eq_add_one, Nat.add_assoc]
    linarith only [h]

end D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233157Row
