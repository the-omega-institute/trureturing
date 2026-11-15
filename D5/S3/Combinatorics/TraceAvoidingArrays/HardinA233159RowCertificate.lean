/- GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233159RowCertificate
   generality: I
   mirror-B: D5/B/S3/Combinatorics/TraceAvoidingArrays/HardinA233159RowCertificate
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233159Row.result; premises=D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233159Row.finite_certificate
   digest: A finite column quotient supplies the order-nine recurrence for six-row strips. -/

/-
admission_basis: open-problem-resolution (#29231; Proved)
escape_witness: none (bind-only: the quotient and sparse-action identities follow from
pinned List and Finset sum identities; consumed on the live certificate path of
HardinA233159Row.result).
successor_table: proof_shape=bind-only; consumers=representative_rows
representative_rows: proof_shape=bind-only; consumers=row_counts, mulVec_successors
row_counts: proof_shape=bind-only; consumers=quotient_certificate
classCodes: proof_shape=bind-only; consumers=class_codes, initial_weights
class_codes: proof_shape=bind-only; consumers=initial_weights
initial_weights: proof_shape=bind-only; consumers=quotient_certificate
mulVec_successors: proof_shape=bind-only; consumers=quotient_certificate
quotient_certificate: proof_shape=bind-only; consumers=HardinA233159Row.finite_certificate, HardinA233159Row.powers_table
-/
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233155RowTransfer
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233155ColumnTransfer
import Mathlib.Tactic
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233159Rows

/-! Finite successor lists determine the quotient and its sparse action. -/
namespace D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233159RowCertificate
open D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233155RowTransfer
open D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233155ColumnTransfer
open D5.S3.Combinatorics.TraceAvoidingArrays
open scoped BigOperators
set_option maxRecDepth 100000
open D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233159Rows
set_option maxHeartbeats 10000000 in
private theorem successor_table : ∀ i : Fin 122,
    successorClasses classify (representatives i) = successors i := by
  intro i
  fin_cases i <;> decide +kernel

set_option maxHeartbeats 10000000 in
private theorem representative_rows : ∀ i s : Fin 122,
    ((successorClasses classify (representatives i)).map
      (fun j => if j = s then (1 : ℤ) else 0)).sum = quotient i s := by
  intro i s
  rw [successor_table]
  rfl
set_option maxHeartbeats 10000000 in
private theorem row_counts : ∀ r : Row 6, ∀ s : Fin 122,
    (∑ c : Row 6, if columnCompatible r c ∧ classify c = s then (1 : ℤ) else 0) =
      quotient (classify r) s :=
  quotient_rows 6 122 classify representatives quotient equality_classes.1
    equality_classes.2 representative_rows

private def classCodes : List (Fin 122) :=
  [0, 81, 81, 41, 27, 121, 41, 121, 27, 14, 54, 108, 68, 9, 94, 95, 67, 40, 14, 108, 54, 95, 40, 67,
    68, 94, 9, 5, 72, 90, 50, 18, 112, 59, 103, 36, 23, 45, 117, 77, 3, 85, 113, 49, 31, 32, 99, 63,
    104, 22, 58, 86, 76, 13, 5, 90, 72, 59, 36, 103, 50, 112, 18, 32, 63, 99, 86, 13, 76, 104, 58,
    22, 23, 117, 45, 113, 31, 49, 77, 85, 3, 2, 78, 84, 44, 24, 118, 47, 115, 30, 17, 51, 111, 71,
    6, 91, 101, 61, 37, 20, 105, 57, 98, 34, 64, 74, 88, 12, 8, 69, 93, 53, 15, 109, 65, 97, 39, 26,
    42, 120, 80, 1, 82, 119, 43, 28, 38, 96, 66, 107, 16, 55, 92, 70, 10, 11, 87, 75, 62, 33, 100,
    56, 106, 21, 35, 60, 102, 89, 7, 73, 110, 52, 19, 29, 114, 48, 116, 25, 46, 83, 79, 4, 2, 84,
    78, 47, 30, 115, 44, 118, 24, 20, 57, 105, 74, 12, 88, 98, 64, 34, 17, 111, 51, 101, 37, 61, 71,
    91, 6, 11, 75, 87, 56, 21, 106, 62, 100, 33, 29, 48, 114, 83, 4, 79, 116, 46, 25, 35, 102, 60,
    110, 19, 52, 89, 73, 7, 8, 93, 69, 65, 39, 97, 53, 109, 15, 38, 66, 96, 92, 10, 70, 107, 55, 16,
    26, 120, 42, 119, 28, 43, 80, 82, 1, 1, 80, 82, 42, 26, 120, 43, 119, 28, 15, 53, 109, 69, 8,
    93, 97, 65, 39, 16, 107, 55, 96, 38, 66, 70, 92, 10, 6, 71, 91, 51, 17, 111, 61, 101, 37, 24,
    44, 118, 78, 2, 84, 115, 47, 30, 34, 98, 64, 105, 20, 57, 88, 74, 12, 7, 89, 73, 60, 35, 102,
    52, 110, 19, 33, 62, 100, 87, 11, 75, 106, 56, 21, 25, 116, 46, 114, 29, 48, 79, 83, 4, 3, 77,
    85, 45, 23, 117, 49, 113, 31, 18, 50, 112, 72, 5, 90, 103, 59, 36, 22, 104, 58, 99, 32, 63, 76,
    86, 13, 9, 68, 94, 54, 14, 108, 67, 95, 40, 27, 41, 121, 81, 0, 81, 121, 41, 27, 40, 95, 67,
    108, 14, 54, 94, 68, 9, 13, 86, 76, 63, 32, 99, 58, 104, 22, 36, 59, 103, 90, 5, 72, 112, 50,
    18, 31, 113, 49, 117, 23, 45, 85, 77, 3, 4, 83, 79, 48, 29, 114, 46, 116, 25, 21, 56, 106, 75,
    11, 87, 100, 62, 33, 19, 110, 52, 102, 35, 60, 73, 89, 7, 12, 74, 88, 57, 20, 105, 64, 98, 34,
    30, 47, 115, 84, 2, 78, 118, 44, 24, 37, 101, 61, 111, 17, 51, 91, 71, 6, 10, 92, 70, 66, 38,
    96, 55, 107, 16, 39, 65, 97, 93, 8, 69, 109, 53, 15, 28, 119, 43, 120, 26, 42, 82, 80, 1, 1, 82,
    80, 43, 28, 119, 42, 120, 26, 16, 55, 107, 70, 10, 92, 96, 66, 38, 15, 109, 53, 97, 39, 65, 69,
    93, 8, 7, 73, 89, 52, 19, 110, 60, 102, 35, 25, 46, 116, 79, 4, 83, 114, 48, 29, 33, 100, 62,
    106, 21, 56, 87, 75, 11, 6, 91, 71, 61, 37, 101, 51, 111, 17, 34, 64, 98, 88, 12, 74, 105, 57,
    20, 24, 118, 44, 115, 30, 47, 78, 84, 2, 4, 79, 83, 46, 25, 116, 48, 114, 29, 19, 52, 110, 73,
    7, 89, 102, 60, 35, 21, 106, 56, 100, 33, 62, 75, 87, 11, 10, 70, 92, 55, 16, 107, 66, 96, 38,
    28, 43, 119, 82, 1, 80, 120, 42, 26, 39, 97, 65, 109, 15, 53, 93, 69, 8, 12, 88, 74, 64, 34, 98,
    57, 105, 20, 37, 61, 101, 91, 6, 71, 111, 51, 17, 30, 115, 47, 118, 24, 44, 84, 78, 2, 3, 85,
    77, 49, 31, 113, 45, 117, 23, 22, 58, 104, 76, 13, 86, 99, 63, 32, 18, 112, 50, 103, 36, 59, 72,
    90, 5, 13, 76, 86, 58, 22, 104, 63, 99, 32, 31, 49, 113, 85, 3, 77, 117, 45, 23, 36, 103, 59,
    112, 18, 50, 90, 72, 5, 9, 94, 68, 67, 40, 95, 54, 108, 14, 40, 67, 95, 94, 9, 68, 108, 54, 14,
    27, 121, 41, 121, 27, 41, 81, 81, 0]

set_option maxHeartbeats 10000000 in
private theorem class_codes :
    (List.finRange 729).map (fun c => classify (decode 6 c)) = classCodes := by
  decide +kernel

set_option maxHeartbeats 10000000 in
private theorem initial_weights : ∀ s : Fin 122,
    (∑ c : Row 6, if classify c = s then (1 : ℤ) else 0) = weights s := by
  intro s
  rw [← (finFunctionFinEquiv (m := 3) (n := 6)).symm.sum_comp]
  rw [← List.sum_ofFn, List.ofFn_eq_map]
  have he : ((List.finRange 729).map (fun c =>
      if classify (decode 6 c) = s then (1 : ℤ) else 0)) =
      classCodes.map (fun j => if j = s then (1 : ℤ) else 0) := by
    rw [← class_codes, List.map_map]
    simp only [Function.comp_def]
  change ((List.finRange 729).map (fun c =>
    if classify (decode 6 c) = s then (1 : ℤ) else 0)).sum = _
  rw [he]
  have ht : ∀ s : Fin 122,
      (classCodes.map (fun j => if j = s then (1 : ℤ) else 0)).sum = weights s := by
    intro t
    fin_cases t <;> decide +kernel
  exact ht s

set_option maxHeartbeats 10000000 in
private theorem mulVec_successors (v : Fin 122 → ℤ) (i : Fin 122) :
    quotient.mulVec v i = ((successors i).map v).sum := by
  have hq (s : Fin 122) : quotient i s =
      ((successors i).map (fun j => if j = s then (1 : ℤ) else 0)).sum := by
    rw [← representative_rows i s, successor_table]
  change (∑ s : Fin 122, quotient i s * v s) = _
  simp_rw [hq]
  simp_rw [← List.sum_map_mul_right]
  have hs : ((successors i).map
      (fun j => ∑ s : Fin 122, (if j = s then (1 : ℤ) else 0) * v s)).sum =
      ∑ s : Fin 122, ((successors i).map
        (fun j => (if j = s then (1 : ℤ) else 0) * v s)).sum := by
    simpa only [Multiset.map_coe, Multiset.sum_coe] using
      (Multiset.sum_map_sum (m := (successors i : Multiset (Fin 122)))
        (s := Finset.univ) (f := fun j s => (if j = s then (1 : ℤ) else 0) * v s))
  rw [← hs]
  simp [ite_mul]

theorem quotient_certificate :
    (∀ r : Row 6, ∀ s : Fin 122,
      (∑ c : Row 6, if columnCompatible r c ∧ classify c = s then (1 : ℤ) else 0) =
        quotient (classify r) s) ∧
    (∀ s : Fin 122, (∑ c : Row 6, if classify c = s then (1 : ℤ) else 0) = weights s) ∧
    (∀ (v : Fin 122 → ℤ) (i : Fin 122),
      quotient.mulVec v i = ((successors i).map v).sum) :=
  ⟨row_counts, initial_weights, mulVec_successors⟩

end D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233159RowCertificate
