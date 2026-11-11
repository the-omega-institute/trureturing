/- GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233158Row
   generality: I
   mirror-B: D5/B/S3/Combinatorics/TraceAvoidingArrays/HardinA233158Row
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233158Row.result; premises=D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233158Row.finite_certificate
   digest: The literal 5-row three-state strip satisfies Hardin's order-7 recurrence. -/

/-
admission_basis: open-problem-resolution (#29231; Proved)
escape_witness: none
The equality-pattern tables and power identities normalize finite arithmetic.
U5: proof_shape=bind-only; consumers=counting_bridge, result
classes: proof_shape=bind-only; consumers=classify
classify: proof_shape=bind-only; consumers=class_invariant, class_representative, successor_table, initial_weights, finite_certificate
representatives: proof_shape=bind-only; consumers=class_representative, successor_table
quotient: proof_shape=bind-only; consumers=row_counts, powers_table, finite_certificate, result
weights: proof_shape=bind-only; consumers=initial_weights, finite_certificate, result
successors: proof_shape=bind-only; consumers=successor_table, representative_rows
class_invariant: proof_shape=bind-only; consumers=row_counts
class_representative: proof_shape=bind-only; consumers=row_counts
successor_table: proof_shape=bind-only; consumers=representative_rows
representative_rows: proof_shape=bind-only; consumers=row_counts
row_counts: proof_shape=bind-only; consumers=finite_certificate
initial_weights: proof_shape=bind-only; consumers=finite_certificate
W: proof_shape=bind-only; consumers=powers_table, vector_relation
powers_table: proof_shape=bind-only; consumers=vector_relation
vector_relation: proof_shape=bind-only; consumers=finite_certificate
finite_certificate: proof_shape=bind-only; consumers=counting_bridge, result
counting_bridge: proof_shape=bind-only; consumers=result
result: proof_shape=bind-only; consumers=Reg.Recurrence.family
-/
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233155RowTransfer
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233155ColumnTransfer
import D5.S3.Combinatorics.TraceAvoidingArrays.TransferMatrix
import Mathlib.Tactic

/-! Equality patterns give a finite quotient of the unrestricted columns. -/
namespace D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233158Row
open D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233155RowTransfer
open D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233155ColumnTransfer
open D5.S3.Combinatorics.TraceAvoidingArrays
open scoped BigOperators
set_option maxRecDepth 100000

def U5 (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun f : Fin 5 × Fin n → Fin 3 => Legal f)).card

def classes : Fin 3 → Fin 3 → Fin 3 → Fin 3 → Fin 3 → Fin 41 :=
  ![![![![![0, 1, 1], ![2, 3, 4], ![2, 4, 3]], ![![5, 6, 7], ![8, 9, 10], ![11, 12, 13]], ![![5, 7,
    6], ![11, 13, 12], ![8, 10, 9]]], ![![![14, 15, 16], ![17, 18, 19], ![20, 21, 22]], ![![23, 24,
    25], ![26, 27, 28], ![29, 30, 31]], ![![32, 33, 34], ![35, 36, 37], ![38, 39, 40]]], ![![![14,
    16, 15], ![20, 22, 21], ![17, 19, 18]], ![![32, 34, 33], ![38, 40, 39], ![35, 37, 36]], ![![23,
    25, 24], ![29, 31, 30], ![26, 28, 27]]]], ![![![![27, 26, 28], ![24, 23, 25], ![30, 29, 31]],
    ![![18, 17, 19], ![15, 14, 16], ![21, 20, 22]], ![![36, 35, 37], ![33, 32, 34], ![39, 38, 40]]],
    ![![![9, 8, 10], ![6, 5, 7], ![12, 11, 13]], ![![3, 2, 4], ![1, 0, 1], ![4, 2, 3]], ![![13, 11,
    12], ![7, 5, 6], ![10, 8, 9]]], ![![![40, 38, 39], ![34, 32, 33], ![37, 35, 36]], ![![22, 20,
    21], ![16, 14, 15], ![19, 17, 18]], ![![31, 29, 30], ![25, 23, 24], ![28, 26, 27]]]],
    ![![![![27, 28, 26], ![30, 31, 29], ![24, 25, 23]], ![![36, 37, 35], ![39, 40, 38], ![33, 34,
    32]], ![![18, 19, 17], ![21, 22, 20], ![15, 16, 14]]], ![![![40, 39, 38], ![37, 36, 35], ![34,
    33, 32]], ![![31, 30, 29], ![28, 27, 26], ![25, 24, 23]], ![![22, 21, 20], ![19, 18, 17], ![16,
    15, 14]]], ![![![9, 10, 8], ![12, 13, 11], ![6, 7, 5]], ![![13, 12, 11], ![10, 9, 8], ![7, 6,
    5]], ![![3, 4, 2], ![4, 3, 2], ![1, 1, 0]]]]]
def classify (r : Row 5) : Fin 41 := classes (r 0) (r 1) (r 2) (r 3) (r 4)
def representatives : Fin 41 → Row 5 :=
  ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 1], ![0, 0, 0, 1, 0], ![0, 0, 0, 1, 1], ![0, 0, 0, 1, 2], ![0,
    0, 1, 0, 0], ![0, 0, 1, 0, 1], ![0, 0, 1, 0, 2], ![0, 0, 1, 1, 0], ![0, 0, 1, 1, 1], ![0, 0, 1,
    1, 2], ![0, 0, 1, 2, 0], ![0, 0, 1, 2, 1], ![0, 0, 1, 2, 2], ![0, 1, 0, 0, 0], ![0, 1, 0, 0, 1],
    ![0, 1, 0, 0, 2], ![0, 1, 0, 1, 0], ![0, 1, 0, 1, 1], ![0, 1, 0, 1, 2], ![0, 1, 0, 2, 0], ![0,
    1, 0, 2, 1], ![0, 1, 0, 2, 2], ![0, 1, 1, 0, 0], ![0, 1, 1, 0, 1], ![0, 1, 1, 0, 2], ![0, 1, 1,
    1, 0], ![0, 1, 1, 1, 1], ![0, 1, 1, 1, 2], ![0, 1, 1, 2, 0], ![0, 1, 1, 2, 1], ![0, 1, 1, 2, 2],
    ![0, 1, 2, 0, 0], ![0, 1, 2, 0, 1], ![0, 1, 2, 0, 2], ![0, 1, 2, 1, 0], ![0, 1, 2, 1, 1], ![0,
    1, 2, 1, 2], ![0, 1, 2, 2, 0], ![0, 1, 2, 2, 1], ![0, 1, 2, 2, 2]]
def quotient : Matrix (Fin 41) (Fin 41) ℤ :=
  ![![2, 2, 2, 2, 0, 2, 2, 0, 2, 2, 0, 0, 0, 0, 2, 2, 0, 2, 2, 0, 0, 0, 0, 2, 2, 0, 2, 2, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 0, 0, 1, 0, 1, 0, 1, 1, 0,
    0, 0, 1, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0,
    0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1,
    1, 1, 1, 0, 0, 0, 0, 0, 1, 1, 0, 1, 1, 1, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0,
    0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1,
    0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0,
    1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0], ![1, 1, 1, 1, 0,
    1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1,
    1, 0, 1, 1], ![0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0,
    0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    1, 1], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1], ![1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 1, 0, 1, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0,
    0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0,
    1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0,
    0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
    1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 1,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0], ![1, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0,
    1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 1, 0, 0,
    0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0,
    1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 1, 0, 1, 0, 0, 0, 1, 0, 1], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1], ![0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0,
    0, 0, 0, 1, 0, 1], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1]]
def weights : Fin 41 → ℤ := ![3, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6,
    6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6]
private def successors : Fin 41 → List (Fin 41) :=
  ![[0, 27, 14, 9, 5, 18, 23, 3, 2, 24, 17, 6, 8, 15, 26, 1, 1, 26, 15, 8, 6, 17, 24, 2, 3, 23, 18,
    5, 9, 14, 27, 0], [0, 27, 14, 9, 5, 18, 23, 3, 1, 28, 16, 10, 7, 19, 25, 4], [0, 27, 14, 9, 1,
    26, 15, 8], [0, 27, 14, 9, 2, 30, 20, 12, 1, 28, 16, 10, 3, 31, 22, 13], [4, 29, 21, 11, 3, 31,
    22, 13], [0, 27, 2, 24, 1, 26, 3, 23], [0, 27, 1, 28], [3, 23, 4, 25], [0, 27, 5, 36, 1, 26, 7,
    35], [0, 27, 5, 36, 2, 30, 8, 39, 1, 28, 6, 37, 3, 31, 9, 40], [4, 29, 10, 38, 3, 31, 9, 40],
    [11, 33, 13, 32], [8, 39, 9, 40], [13, 32, 10, 38, 12, 34, 9, 40], [0, 5, 2, 8, 1, 6, 3, 9], [0,
    5, 1, 7], [3, 9, 4, 10], [0, 1], [0, 2, 1, 3], [4, 3], [8, 9], [11, 13], [9, 12, 10, 13], [0,
    14, 2, 20, 1, 16, 3, 22], [0, 14, 1, 15], [3, 22, 4, 21], [0, 14, 5, 23, 1, 16, 7, 25], [0, 14,
    5, 23, 2, 17, 8, 26, 1, 15, 6, 24, 3, 18, 9, 27], [4, 19, 10, 28, 3, 18, 9, 27], [11, 29, 13,
    31], [8, 26, 9, 27], [13, 31, 10, 28, 12, 30, 9, 27], [32, 38, 34, 40], [32, 33], [40, 39], [23,
    25], [23, 26, 24, 27], [28, 27], [38, 29, 40, 31], [35, 26, 36, 27], [40, 31, 37, 28, 39, 30,
    36, 27]]

set_option maxHeartbeats 10000000 in
private theorem class_invariant : ∀ (e : Equiv.Perm (Fin 3)) (r : Row 5),
    classify (relabel e r) = classify r := by decide +kernel
set_option maxHeartbeats 10000000 in
private theorem class_representative : ∀ r : Row 5, ∃ e : Equiv.Perm (Fin 3),
    relabel e r = representatives (classify r) := by decide +kernel
set_option maxHeartbeats 10000000 in
private theorem successor_table : ∀ i : Fin 41,
    successorClasses classify (representatives i) = successors i := by decide +kernel
set_option maxHeartbeats 10000000 in
private theorem representative_rows : ∀ i s : Fin 41,
    ((successorClasses classify (representatives i)).map
      (fun j => if j = s then (1 : ℤ) else 0)).sum = quotient i s := by
  have ht : List.ofFn (fun i : Fin 41 => List.ofFn (fun s : Fin 41 =>
      ((successors i).map (fun j => if j = s then (1 : ℤ) else 0)).sum)) =
      List.ofFn (fun i : Fin 41 => List.ofFn (fun s : Fin 41 => quotient i s)) := rfl
  intro i s
  rw [successor_table]
  exact congrFun (List.ofFn_inj.mp (congrFun (List.ofFn_inj.mp ht) i)) s
set_option maxHeartbeats 10000000 in
private theorem row_counts : ∀ r : Row 5, ∀ s : Fin 41,
    (∑ c : Row 5, if columnCompatible r c ∧ classify c = s then (1 : ℤ) else 0) =
      quotient (classify r) s :=
  quotient_rows 5 41 classify representatives quotient class_invariant
    class_representative representative_rows
set_option maxHeartbeats 10000000 in
private theorem initial_weights : ∀ s : Fin 41,
    (∑ c : Row 5, if classify c = s then (1 : ℤ) else 0) = weights s := by
  intro s
  rw [← (finFunctionFinEquiv (m := 3) (n := 5)).symm.sum_comp]
  rw [← List.sum_ofFn, List.ofFn_eq_map]
  revert s
  decide +kernel
private def W : Fin 12 → Fin 41 → ℤ :=
  ![![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1], ![32, 16, 8, 16, 8, 8, 4, 4, 8, 16, 8, 4, 4, 8, 8, 4, 4, 2, 4, 2,
    2, 2, 4, 8, 4, 4, 8, 16, 8, 4, 4, 8, 4, 2, 2, 2, 4, 2, 4, 4, 8], ![324, 162, 108, 162, 54, 108,
    72, 36, 90, 162, 72, 18, 36, 54, 108, 60, 48, 48, 72, 24, 24, 12, 36, 90, 60, 30, 84, 162, 78,
    24, 48, 72, 18, 6, 12, 12, 36, 24, 24, 30, 54], ![3744, 1692, 1152, 1656, 432, 1152, 726, 336,
    924, 1692, 624, 96, 336, 432, 1188, 630, 450, 486, 756, 216, 252, 72, 324, 972, 654, 264, 906,
    1872, 786, 168, 498, 684, 108, 24, 84, 120, 396, 240, 174, 294, 504], ![40404, 17832, 12648,
    17382, 3864, 12648, 8094, 3324, 10218, 18012, 5934, 660, 3414, 3954, 12738, 6924, 4404, 5436,
    8244, 2088, 2616, 528, 3084, 10458, 7254, 2484, 9798, 20202, 8034, 1380, 5394, 6924, 870, 132,
    798, 1236, 4404, 2658, 1530, 3294, 5274], ![436584, 188052, 136128, 182976, 37776, 135978,
    86472, 34188, 109848, 193422, 60300, 5616, 36798, 39786, 137238, 74208, 45192, 58236, 88266,
    21246, 28230, 4614, 31314, 111108, 77898, 24858, 104292, 218292, 83760, 12918, 58230, 71868,
    8472, 1002, 8568, 12942, 47712, 28236, 15108, 35640, 56184], ![4677996, 1999236, 1461936,
    1948170, 386868, 1455330, 926688, 356718, 1178040, 2069382, 630552, 54876, 395094, 418638,
    1469460, 794802, 474474, 624636, 943740, 220752, 303270, 45402, 330306, 1185714, 836082, 256680,
    1113198, 2338998, 886038, 130188, 625854, 762456, 88332, 9474, 91824, 135966, 511590, 302052,
    156078, 383238, 599922], ![50046816, 21300108, 15641112, 20791860, 4076904, 15561330, 9902268,
    3777432, 12589032, 22126926, 6683616, 571320, 4230582, 4449822, 15716778, 8489280, 5034972,
    6677232, 10087338, 2335038, 3247422, 473514, 3513666, 12664848, 8941494, 2710746, 11875608,
    25023408, 9424500, 1366158, 6699618, 8127012, 936156, 97806, 983160, 1442394, 5473992, 3225036,
    1648644, 4099752, 6410148], ![534870876, 227362620, 167167956, 222058218, 43370256, 166285254,
    105794832, 40244358, 134501088, 236442918, 71231268, 6055104, 45225858, 47469054, 167959452,
    90685686, 53679306, 71346924, 107779896, 24868764, 34715958, 5021142, 37490946, 135292734,
    95552982, 28855944, 126813030, 267435438, 100549590, 14514312, 71614974, 86765484, 9978108,
    1033962, 10509900, 15375594, 58505358, 34447908, 17551962, 43815402, 68483466], ![5714699808,
    2428286892, 1786071108, 2372039916, 462744516, 1776553854, 1130218524, 429577152, 1436892528,
    2526101382, 760417884, 64536228, 483242874, 506892534, 1794483762, 968763108, 573102660,
    762233496, 1151459670, 265428474, 370944006, 53524158, 400369098, 1445305332, 1020878634,
    307940562, 1354550544, 2857349904, 1073736348, 154803954, 765192474, 926734584, 106523436,
    11012070, 112298868, 164148678, 625094184, 367985028, 187315224, 468129420, 731617620],
    ![61051776924, 25939228116, 19081127928, 25339665234, 4941644988, 18979182138, 12074072952,
    4588030326, 15350261016, 26986703574, 8121775080, 688964268, 5162740950, 5414409822,
    19170864012, 10349117706, 6121303698, 8142986700, 12301097724, 2834784432, 3962993910,
    571428762, 4276654674, 15439997250, 10906233570, 3288677688, 14469950022, 30525888462,
    11469278094, 1652967300, 8174894358, 9899667984, 1137755148, 117535506, 1199747040, 1753245894,
    6678084414, 3931086252, 2000471382, 5001143310, 7815839562], ![652216306656, 277099897740,
    203843789832, 270698972820, 52785403032, 202753867506, 128986171596, 49009985160, 163985386296,
    288297900318, 86758735104, 7358664744, 55153947462, 57839442558, 204802017882, 110558217504,
    65389788876, 86991005040, 131411798202, 30281310222, 42336964590, 6103374090, 45685629426,
    164943614496, 116510986758, 35129393658, 154579060152, 326108153328, 122520837588, 17656009374,
    87332803074, 105755358324, 12153813132, 1255290654, 12816982872, 18728674938, 71342069304,
    41995166556, 21368946228, 53427168792, 83495882436]]
set_option maxHeartbeats 10000000 in
private theorem powers_table : ∀ j : Fin 12,
    (quotient ^ j.val).mulVec (1 : Fin 41 → ℤ) = W j := by
  apply TransferMatrix.tabulatedPowers
  · exact List.ofFn_inj.mp rfl
  · intro j
    fin_cases j <;> exact List.ofFn_inj.mp rfl
set_option maxHeartbeats 10000000 in
private theorem vector_relation :
    (quotient ^ (4 + 7)).mulVec (1 : Fin 41 → ℤ) =
      ∑ j : Fin 7, (![-8, 48, -84, 17, 76, -64, 16] : Fin 7 → ℤ) j •
        (quotient ^ (4 + j.val)).mulVec (1 : Fin 41 → ℤ) := by
  rw [show 4 + 7 = (11 : Fin 12).val from rfl, powers_table]
  have hh (j : Fin 7) : (quotient ^ (4 + j.val)).mulVec (1 : Fin 41 → ℤ) =
      W ⟨4 + j.val, by omega⟩ := powers_table ⟨4 + j.val, by omega⟩
  simp_rw [hh]
  exact List.ofFn_inj.mp (by decide +kernel)

set_option maxHeartbeats 10000000 in
theorem finite_certificate :
    (∀ r : Row 5, ∀ s : Fin 41,
      (∑ c : Row 5, if columnCompatible r c ∧ classify c = s then (1 : ℤ) else 0) =
        quotient (classify r) s) ∧
    (∀ s : Fin 41, (∑ c : Row 5, if classify c = s then (1 : ℤ) else 0) = weights s) ∧
    (quotient ^ (4 + 7)).mulVec (1 : Fin 41 → ℤ) =
      ∑ j : Fin 7, (![-8, 48, -84, 17, 76, -64, 16] : Fin 7 → ℤ) j •
        (quotient ^ (4 + j.val)).mulVec (1 : Fin 41 → ℤ) :=
  ⟨row_counts, initial_weights, vector_relation⟩

set_option maxHeartbeats 10000000 in
private theorem counting_bridge (n : ℕ) :
    (U5 (n + 2) : ℤ) = dotProduct weights
      ((quotient ^ (n + 1)).mulVec (1 : Fin 41 → ℤ)) :=
  count_transfer 5 41 classify quotient weights
    finite_certificate.1 finite_certificate.2.1 n

set_option maxHeartbeats 10000000 in
theorem result (n : ℕ) : (U5 (n + 12) : ℤ) =
    16 * (U5 (n + 11) : ℤ) - 64 * (U5 (n + 10) : ℤ) + 76 * (U5 (n + 9) : ℤ) + 17 * (U5 (n + 8) : ℤ)
    - 84 * (U5 (n + 7) : ℤ) + 48 * (U5 (n + 6) : ℤ) - 8 * (U5 (n + 5) : ℤ) := by
  have h := TransferMatrix.scalarRelationShift quotient weights 7 4
    (![-8, 48, -84, 17, 76, -64, 16] : Fin 7 → ℤ) finite_certificate.2.2 n
  have hb (j : ℕ) : dotProduct weights
      ((quotient ^ (n + 4 + j)).mulVec (1 : Fin 41 → ℤ)) =
        (U5 (n + 4 + j + 1) : ℤ) := by
    rw [show n + 4 + j = (n + 3 + j) + 1 by omega]
    exact (counting_bridge (n + 3 + j)).symm
  simp_rw [hb] at h
  norm_num only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Finset.sum_empty,
    add_zero, Nat.add_assoc] at h
  linarith only [h]

end D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233158Row
