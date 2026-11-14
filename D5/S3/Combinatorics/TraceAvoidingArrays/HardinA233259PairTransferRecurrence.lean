/- GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233259PairTransferRecurrence
   generality: G
   mirror-B: D5/B/S3/Combinatorics/TraceAvoidingArrays/HardinA233259PairTransferRecurrence
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233259PairTransferRecurrence.shifted; premises=D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233259PairTransferPowers.power_polynomial,D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233259PairTransferCount.count_transfer
   digest: Four-row scalar transfer recurrence for A233259. -/
/-
admission_basis: escape-witness
escape_witness: Powers.power_polynomial on the successor path; Base.initial_values and its certified one-sided table inputs on the zero path
shifted: proof_shape=content; consumers=recurrence
recurrence: proof_shape=content; consumers=HardinA233259Strip.finite_certificate, HardinA233259Strip.result
-/
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233259PairTransferCore
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233259PairTransferCount
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233259PairTransferPowers
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233259PairTransferBase
import D5.S3.Combinatorics.TraceAvoidingArrays.TransferMatrix

open scoped BigOperators
namespace D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233259PairTransferRecurrence
open HardinA233259PairTransferCore
open HardinA233259PairTransferCount (count_transfer)
open HardinA233259PairTransferPowers (coefficients power_polynomial)
open HardinA233259PairTransferBase (initial_values)

private theorem shifted (n : ℕ) : (L (n+10) : ℤ) + 6 =
    10 * ((L (n+9) : ℤ) + 6) - 24 * ((L (n+8) : ℤ) + 6) +
      21 * ((L (n+7) : ℤ) + 6) - 6 * ((L (n+6) : ℤ) + 6) := by
  have h := TransferMatrix.scalarRelationShift Q weights 4 4 coefficients power_polynomial n
  have hs (X : Fin 4 → ℤ) :
      (∑ j : Fin 4, coefficients j * X j) =
        -6 * X 0 + 21 * X 1 - 24 * X 2 + 10 * X 3 := by
    norm_num [coefficients, Fin.sum_univ_succ]
    ring
  rw [hs] at h
  have ht (k : ℕ) : dotProduct weights ((Q^k).mulVec (1 : Fin 14 → ℤ)) =
      (L (k+2) : ℤ) := (count_transfer k).symm
  rw [show (0 : Fin 4).val = 0 from rfl, show (1 : Fin 4).val = 1 from rfl,
    show (2 : Fin 4).val = 2 from rfl, show (3 : Fin 4).val = 3 from rfl] at h
  rw [show n+4+4 = n+8 by omega, show n+4+0 = n+4 by omega,
    show n+4+1 = n+5 by omega, show n+4+2 = n+6 by omega,
    show n+4+3 = n+7 by omega] at h
  rw [ht (n+8), ht (n+4), ht (n+5), ht (n+6), ht (n+7)] at h
  norm_num [Nat.add_assoc] at h ⊢
  omega

theorem recurrence (n : ℕ) : (L (n+9) : ℤ) + 6 =
    10 * ((L (n+8) : ℤ) + 6) - 24 * ((L (n+7) : ℤ) + 6) +
      21 * ((L (n+6) : ℤ) + 6) - 6 * ((L (n+5) : ℤ) + 6) := by
  cases n with
  | zero =>
    have h3 : (L 5 : ℤ) = 121176 := by
      exact initial_values ⟨3, by omega⟩
    have h4 : (L 6 : ℤ) = 842616 := by
      exact initial_values ⟨4, by omega⟩
    have h5 : (L 7 : ℤ) = 5871528 := by
      exact initial_values ⟨5, by omega⟩
    have h6 : (L 8 : ℤ) = 40931568 := by
      exact initial_values ⟨6, by omega⟩
    have h7 : (L 9 : ℤ) = 285366888 := by
      exact initial_values ⟨7, by omega⟩
    norm_num only [Nat.zero_add] at ⊢
    omega
  | succ n =>
    have h := shifted n
    simpa only [Nat.succ_add, Nat.add_assoc] using h

end D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233259PairTransferRecurrence
