/- GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233159Rows
   generality: I
   mirror-B: D5/B/S3/Combinatorics/TraceAvoidingArrays/HardinA233159Rows
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233159Row.result; premises=D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233159Row.finite_certificate
   digest: A finite column quotient supplies the order-nine recurrence for six-row strips. -/

/-
admission_basis: open-problem-resolution (#29231; Proved)
escape_witness: none (finite equality-pattern normalization only)
All declarations normalize finite equality tests, tables and logical packaging.
U6: proof_shape=bind-only; consumers=HardinA233159Row.counting_bridge, HardinA233159Row.result
classes: proof_shape=bind-only; consumers=classify
classify: proof_shape=bind-only; consumers=class_invariant, class_representative, HardinA233159RowCertificate.successor_table, HardinA233159RowCertificate.class_codes
representatives: proof_shape=bind-only; consumers=class_representative, HardinA233159RowCertificate.successor_table
quotient: proof_shape=bind-only; consumers=HardinA233159RowCertificate.representative_rows, HardinA233159RowCertificate.mulVec_successors, HardinA233159Row.finite_certificate
weights: proof_shape=bind-only; consumers=HardinA233159RowCertificate.initial_weights, HardinA233159Row.counting_bridge
successors: proof_shape=bind-only; consumers=quotient, HardinA233159RowCertificate.successor_table, HardinA233159Row.powers_table
class_invariant: proof_shape=bind-only; consumers=equality_classes
class_representative: proof_shape=bind-only; consumers=equality_classes
equality_classes: proof_shape=bind-only; consumers=HardinA233159RowCertificate.row_counts
-/
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233155RowTransfer
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233155ColumnTransfer
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233179PairTransfer
import Mathlib.Tactic

/-! Equality patterns classify all six-entry columns. -/
namespace D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233159Rows
open D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233155RowTransfer
open D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233155ColumnTransfer
open D5.S3.Combinatorics.TraceAvoidingArrays
open scoped BigOperators
set_option maxRecDepth 100000
def U6 (n : ℕ) : ℕ := HardinA233155RowTransfer.T n 6

def classes (a b c d e f : Fin 3) : Fin 122 :=
  HardinA233179PairTransfer.orbit (a, b, c, d, e, f)

def classify (r : Row 6) : Fin 122 := classes (r 0) (r 1) (r 2) (r 3) (r 4) (r 5)

def representatives (i : Fin 122) : Row 6 :=
  HardinA233179PairTransfer.column (HardinA233179PairTransfer.representatives i)

def weights : Fin 122 → ℤ := ![3, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6,
    6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6,
    6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6,
    6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6,
    6, 6, 6]

def successors : Fin 122 → List (Fin 122) :=
  ![[0, 81, 41, 27, 14, 54, 68, 9, 5, 72, 50, 18, 23, 45, 77, 3, 2, 78, 44, 24, 17, 51, 71, 6, 8,
    69, 53, 15, 26, 42, 80, 1, 1, 80, 42, 26, 15, 53, 69, 8, 6, 71, 51, 17, 24, 44, 78, 2, 3, 77,
    45, 23, 18, 50, 72, 5, 9, 68, 54, 14, 27, 41, 81, 0], [0, 81, 41, 27, 14, 54, 68, 9, 5, 72, 50,
    18, 23, 45, 77, 3, 1, 82, 43, 28, 16, 55, 70, 10, 7, 73, 52, 19, 25, 46, 79, 4], [0, 81, 41, 27,
    14, 54, 68, 9, 1, 80, 42, 26, 15, 53, 69, 8], [0, 81, 41, 27, 14, 54, 68, 9, 2, 84, 47, 30, 20,
    57, 74, 12, 1, 82, 43, 28, 16, 55, 70, 10, 3, 85, 49, 31, 22, 58, 76, 13], [4, 83, 48, 29, 21,
    56, 75, 11, 3, 85, 49, 31, 22, 58, 76, 13], [0, 81, 41, 27, 2, 78, 44, 24, 1, 80, 42, 26, 3, 77,
    45, 23], [0, 81, 41, 27, 1, 82, 43, 28], [3, 77, 45, 23, 4, 79, 46, 25], [0, 81, 41, 27, 5, 90,
    59, 36, 1, 80, 42, 26, 7, 89, 60, 35], [0, 81, 41, 27, 5, 90, 59, 36, 2, 84, 47, 30, 8, 93, 65,
    39, 1, 82, 43, 28, 6, 91, 61, 37, 3, 85, 49, 31, 9, 94, 67, 40], [4, 83, 48, 29, 10, 92, 66, 38,
    3, 85, 49, 31, 9, 94, 67, 40], [11, 87, 62, 33, 13, 86, 63, 32], [8, 93, 65, 39, 9, 94, 67, 40],
    [13, 86, 63, 32, 10, 92, 66, 38, 12, 88, 64, 34, 9, 94, 67, 40], [0, 81, 5, 72, 2, 78, 8, 69, 1,
    80, 6, 71, 3, 77, 9, 68], [0, 81, 5, 72, 1, 82, 7, 73], [3, 77, 9, 68, 4, 79, 10, 70], [0, 81,
    1, 80], [0, 81, 2, 84, 1, 82, 3, 85], [4, 83, 3, 85], [8, 69, 9, 68], [11, 75, 13, 76], [9, 68,
    12, 74, 10, 70, 13, 76], [0, 81, 14, 108, 2, 78, 20, 105, 1, 80, 16, 107, 3, 77, 22, 104], [0,
    81, 14, 108, 1, 82, 15, 109], [3, 77, 22, 104, 4, 79, 21, 106], [0, 81, 14, 108, 5, 90, 23, 117,
    1, 80, 16, 107, 7, 89, 25, 116], [0, 81, 14, 108, 5, 90, 23, 117, 2, 84, 17, 111, 8, 93, 26,
    120, 1, 82, 15, 109, 6, 91, 24, 118, 3, 85, 18, 112, 9, 94, 27, 121], [4, 83, 19, 110, 10, 92,
    28, 119, 3, 85, 18, 112, 9, 94, 27, 121], [11, 87, 29, 114, 13, 86, 31, 113], [8, 93, 26, 120,
    9, 94, 27, 121], [13, 86, 31, 113, 10, 92, 28, 119, 12, 88, 30, 115, 9, 94, 27, 121], [32, 99,
    38, 96, 34, 98, 40, 95], [32, 99, 33, 100], [40, 95, 39, 97], [23, 117, 25, 116], [23, 117, 26,
    120, 24, 118, 27, 121], [28, 119, 27, 121], [38, 96, 29, 114, 40, 95, 31, 113], [35, 102, 26,
    120, 36, 103, 27, 121], [40, 95, 31, 113, 37, 101, 28, 119, 39, 97, 30, 115, 36, 103, 27, 121],
    [0, 14, 5, 23, 2, 17, 8, 26, 1, 15, 6, 24, 3, 18, 9, 27], [0, 14, 5, 23, 1, 16, 7, 25], [3, 18,
    9, 27, 4, 19, 10, 28], [0, 14, 1, 15], [0, 14, 2, 20, 1, 16, 3, 22], [4, 21, 3, 22], [8, 26, 9,
    27], [11, 29, 13, 31], [9, 27, 12, 30, 10, 28, 13, 31], [0, 2, 1, 3], [0, 1], [3, 4], [0, 5, 1,
    7], [0, 5, 2, 8, 1, 6, 3, 9], [4, 10, 3, 9], [11, 13], [8, 9], [13, 10, 12, 9], [23, 26, 24,
    27], [23, 25], [27, 28], [32, 33], [32, 38, 34, 40], [39, 40], [26, 35, 27, 36], [29, 38, 31,
    40], [27, 36, 30, 39, 28, 37, 31, 40], [0, 41, 5, 59, 2, 47, 8, 65, 1, 43, 6, 61, 3, 49, 9, 67],
    [0, 41, 5, 59, 1, 42, 7, 60], [3, 49, 9, 67, 4, 48, 10, 66], [0, 41, 1, 43], [0, 41, 2, 44, 1,
    42, 3, 45], [4, 46, 3, 45], [8, 65, 9, 67], [11, 62, 13, 63], [9, 67, 12, 64, 10, 66, 13, 63],
    [0, 41, 14, 68, 2, 47, 20, 74, 1, 43, 16, 70, 3, 49, 22, 76], [0, 41, 14, 68, 1, 42, 15, 69],
    [3, 49, 22, 76, 4, 48, 21, 75], [0, 41, 14, 68, 5, 50, 23, 77, 1, 43, 16, 70, 7, 52, 25, 79],
    [0, 41, 14, 68, 5, 50, 23, 77, 2, 44, 17, 71, 8, 53, 26, 80, 1, 42, 15, 69, 6, 51, 24, 78, 3,
    45, 18, 72, 9, 54, 27, 81], [4, 46, 19, 73, 10, 55, 28, 82, 3, 45, 18, 72, 9, 54, 27, 81], [11,
    56, 29, 83, 13, 58, 31, 85], [8, 53, 26, 80, 9, 54, 27, 81], [13, 58, 31, 85, 10, 55, 28, 82,
    12, 57, 30, 84, 9, 54, 27, 81], [32, 86, 38, 92, 34, 88, 40, 94], [32, 86, 33, 87], [40, 94, 39,
    93], [23, 77, 25, 79], [23, 77, 26, 80, 24, 78, 27, 81], [28, 82, 27, 81], [38, 92, 29, 83, 40,
    94, 31, 85], [35, 89, 26, 80, 36, 90, 27, 81], [40, 94, 31, 85, 37, 91, 28, 82, 39, 93, 30, 84,
    36, 90, 27, 81], [95, 113, 101, 119, 97, 115, 103, 121], [95, 113, 96, 114], [103, 121, 102,
    120], [95, 97], [95, 98, 96, 99], [100, 99], [119, 121], [116, 117], [121, 118, 120, 117], [68,
    74, 70, 76], [68, 69], [76, 75], [68, 77, 70, 79], [68, 77, 71, 80, 69, 78, 72, 81], [73, 82,
    72, 81], [83, 85], [80, 81], [85, 82, 84, 81], [113, 86, 119, 92, 115, 88, 121, 94], [113, 86,
    114, 87], [121, 94, 120, 93], [104, 77, 106, 79], [104, 77, 107, 80, 105, 78, 108, 81], [109,
    82, 108, 81], [119, 92, 110, 83, 121, 94, 112, 85], [116, 89, 107, 80, 117, 90, 108, 81], [121,
    94, 112, 85, 118, 91, 109, 82, 120, 93, 111, 84, 117, 90, 108, 81]]

def quotient : Matrix (Fin 122) (Fin 122) ℤ := fun i s =>
  ((successors i).map (fun j => if j = s then (1 : ℤ) else 0)).sum

set_option maxHeartbeats 10000000 in
private theorem class_invariant : ∀ (e : Equiv.Perm (Fin 3)) (r : Row 6),
    classify (relabel e r) = classify r := by
  intro e r
  change classes (e (r 0)) (e (r 1)) (e (r 2)) (e (r 3)) (e (r 4)) (e (r 5)) = _
  simp only [classify, classes, HardinA233179PairTransfer.orbit,
    HardinA233179PairTransfer.column, Matrix.cons_val, e.injective.eq_iff]
  rfl

set_option maxHeartbeats 10000000 in
private theorem class_representative : ∀ r : Row 6, ∃ e : Equiv.Perm (Fin 3),
    relabel e r = representatives (classify r) := by
  intro r
  obtain ⟨e, he⟩ := HardinA233179PairTransfer.class_rep (r 0, r 1, r 2, r 3, r 4, r 5)
  refine ⟨e, funext fun i => ?_⟩
  have h := congrArg (fun c => HardinA233179PairTransfer.column c i) he
  fin_cases i <;> exact h

theorem equality_classes :
    (∀ (e : Equiv.Perm (Fin 3)) (r : Row 6), classify (relabel e r) = classify r) ∧
    (∀ r : Row 6, ∃ e : Equiv.Perm (Fin 3), relabel e r = representatives (classify r)) :=
  ⟨class_invariant, class_representative⟩

end D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233159Rows
