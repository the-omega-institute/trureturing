/- GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233157Row
   generality: I
   mirror-B: D5/B/S3/Combinatorics/TraceAvoidingArrays/HardinA233157Row
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233157Row.result; premises=D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233157Row.finite_certificate
   digest: The literal 4-row three-state strip satisfies Hardin's order-3 recurrence. -/

/-
admission_basis: open-problem-resolution (#29231; Proved)
escape_witness: counting_bridge -> HardinA233155ColumnTransfer.count_transfer ->
TransferMatrix.cardMatrix -> TransferMatrix.cont_matrix (W2: induction over every
continuation length). TransferMatrix is unfrozen on the protected baseline.
The fixed-index power tables and certificates are bind-only.
U4: proof_shape=bind-only; consumers=counting_bridge, result
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
counting_bridge: proof_shape=content; consumers=result
result: proof_shape=content; consumers=Reg.Recurrence.family
-/
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233155RowTransfer
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233155ColumnTransfer
import D5.S3.Combinatorics.TraceAvoidingArrays.TransferMatrix
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177PairTransfer
import Mathlib.Tactic

/-! Equality patterns give a finite quotient of the unrestricted columns. -/
namespace D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233157Row
open D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233155RowTransfer
open D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233155ColumnTransfer
open D5.S3.Combinatorics.TraceAvoidingArrays
open scoped BigOperators
set_option maxRecDepth 100000

def U4 (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun f : Fin 4 × Fin n → Fin 3 => Legal f)).card

def classes (a b c d : Fin 3) : Fin 14 :=
  HardinA233177PairTransfer.cls (a, b, c, d)

def classify (r : Row 4) : Fin 14 := classes (r 0) (r 1) (r 2) (r 3)
def representatives (i : Fin 14) : Row 4 :=
  HardinA233177PairTransfer.column (HardinA233177PairTransfer.representatives i)

def quotient : Matrix (Fin 14) (Fin 14) ℤ :=
  ![![2, 2, 2, 2, 0, 2, 2, 0, 2, 2, 0, 0, 0, 0], ![1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 0, 0], ![1,
    1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0], ![1, 1, 1, 1, 0, 0, 0, 0, 0, 1, 1, 0, 1, 1], ![0, 0, 0,
    1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1], ![1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 1, 0,
    1, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0], ![0, 0, 0, 1, 1, 0, 0, 0, 0,
    1, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0,
    0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 1]]
def weights : Fin 14 → ℤ := ![3, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6]
private def successors : Fin 14 → List (Fin 14) :=
  ![[0, 9, 5, 3, 2, 6, 8, 1, 1, 8, 6, 2, 3, 5, 9, 0], [0, 9, 5, 3, 1, 10, 7, 4], [0, 9, 1, 8], [0,
    9, 2, 12, 1, 10, 3, 13], [4, 11, 3, 13], [0, 2, 1, 3], [0, 1], [3, 4], [0, 5, 1, 7], [0, 5, 2,
    8, 1, 6, 3, 9], [4, 10, 3, 9], [11, 13], [8, 9], [13, 10, 12, 9]]

set_option maxHeartbeats 10000000 in
private theorem class_invariant : ∀ (e : Equiv.Perm (Fin 3)) (r : Row 4),
    classify (relabel e r) = classify r := by
  intro e r
  exact HardinA233177PairTransfer.class_relabel e (r 0, r 1, r 2, r 3)
set_option maxHeartbeats 10000000 in
private theorem class_representative : ∀ r : Row 4, ∃ e : Equiv.Perm (Fin 3),
    relabel e r = representatives (classify r) := by
  intro r
  obtain ⟨e, he⟩ := HardinA233177PairTransfer.class_rep (r 0, r 1, r 2, r 3)
  refine ⟨e, funext fun i => ?_⟩
  have h := congrArg (fun c => HardinA233177PairTransfer.column c i) he
  fin_cases i <;> exact h
set_option maxHeartbeats 10000000 in
private theorem successor_table : ∀ i : Fin 14,
    successorClasses classify (representatives i) = successors i := by decide +kernel
set_option maxHeartbeats 10000000 in
private theorem representative_rows : ∀ i s : Fin 14,
    ((successorClasses classify (representatives i)).map
      (fun j => if j = s then (1 : ℤ) else 0)).sum = quotient i s := by
  have ht : List.ofFn (fun i : Fin 14 => List.ofFn (fun s : Fin 14 =>
      ((successors i).map (fun j => if j = s then (1 : ℤ) else 0)).sum)) =
      List.ofFn (fun i : Fin 14 => List.ofFn (fun s : Fin 14 => quotient i s)) := rfl
  intro i s
  rw [successor_table]
  exact congrFun (List.ofFn_inj.mp (congrFun (List.ofFn_inj.mp ht) i)) s
set_option maxHeartbeats 10000000 in
private theorem row_counts : ∀ r : Row 4, ∀ s : Fin 14,
    (∑ c : Row 4, if columnCompatible r c ∧ classify c = s then (1 : ℤ) else 0) =
      quotient (classify r) s :=
  quotient_rows 4 14 classify representatives quotient class_invariant
    class_representative representative_rows
set_option maxHeartbeats 10000000 in
private theorem initial_weights : ∀ s : Fin 14,
    (∑ c : Row 4, if classify c = s then (1 : ℤ) else 0) = weights s := by
  intro s
  rw [← (finFunctionFinEquiv (m := 3) (n := 4)).symm.sum_comp]
  rw [← List.sum_ofFn, List.ofFn_eq_map]
  revert s
  decide +kernel
private def W : Fin 8 → Fin 14 → ℤ :=
  ![![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], ![16, 8, 4, 8, 4, 4, 2, 2, 4, 8, 4, 2, 2, 4],
    ![108, 54, 36, 54, 18, 36, 24, 12, 30, 54, 24, 6, 12, 18], ![792, 360, 246, 360, 96, 252, 162,
    72, 210, 396, 150, 24, 84, 108], ![5556, 2478, 1758, 2496, 588, 1758, 1152, 456, 1476, 2778,
    1002, 132, 606, 738], ![38904, 17112, 12288, 17412, 3954, 12288, 8034, 3084, 10248, 19452, 6864,
    870, 4254, 5124], ![271476, 119070, 85716, 121410, 27360, 85716, 56016, 21366, 71388, 135738,
    47682, 5994, 29700, 35694], ![1893060, 829818, 597672, 846486, 190458, 597672, 390546, 148770,
    497628, 946530, 332190, 41688, 207126, 248814]]
set_option maxHeartbeats 10000000 in
private theorem powers_table : ∀ j : Fin 8,
    (quotient ^ j.val).mulVec (1 : Fin 14 → ℤ) = W j := by
  apply TransferMatrix.tabulatedPowers
  · exact List.ofFn_inj.mp rfl
  · intro j
    fin_cases j <;> exact List.ofFn_inj.mp rfl
set_option maxHeartbeats 10000000 in
private theorem vector_relation :
    (quotient ^ (4 + 3)).mulVec (1 : Fin 14 → ℤ) =
      ∑ j : Fin 3, (![6, -15, 9] : Fin 3 → ℤ) j •
        (quotient ^ (4 + j.val)).mulVec (1 : Fin 14 → ℤ) := by
  rw [show 4 + 3 = (7 : Fin 8).val from rfl, powers_table]
  have hh (j : Fin 3) : (quotient ^ (4 + j.val)).mulVec (1 : Fin 14 → ℤ) =
      W ⟨4 + j.val, by omega⟩ := powers_table ⟨4 + j.val, by omega⟩
  simp_rw [hh]
  exact List.ofFn_inj.mp (by decide +kernel)

set_option maxHeartbeats 10000000 in
theorem finite_certificate :
    (∀ r : Row 4, ∀ s : Fin 14,
      (∑ c : Row 4, if columnCompatible r c ∧ classify c = s then (1 : ℤ) else 0) =
        quotient (classify r) s) ∧
    (∀ s : Fin 14, (∑ c : Row 4, if classify c = s then (1 : ℤ) else 0) = weights s) ∧
    (quotient ^ (4 + 3)).mulVec (1 : Fin 14 → ℤ) =
      ∑ j : Fin 3, (![6, -15, 9] : Fin 3 → ℤ) j •
        (quotient ^ (4 + j.val)).mulVec (1 : Fin 14 → ℤ) :=
  ⟨row_counts, initial_weights, vector_relation⟩

set_option maxHeartbeats 10000000 in
private theorem counting_bridge (n : ℕ) :
    (U4 (n + 2) : ℤ) = dotProduct weights
      ((quotient ^ (n + 1)).mulVec (1 : Fin 14 → ℤ)) :=
  count_transfer 4 14 classify quotient weights
    finite_certificate.1 finite_certificate.2.1 n

set_option maxHeartbeats 10000000 in
theorem result (n : ℕ) : (U4 (n + 8) : ℤ) =
    9 * (U4 (n + 7) : ℤ) - 15 * (U4 (n + 6) : ℤ) + 6 * (U4 (n + 5) : ℤ) := by
  have h := TransferMatrix.scalarRelationShift quotient weights 3 4
    (![6, -15, 9] : Fin 3 → ℤ) finite_certificate.2.2 n
  have hb (j : ℕ) : dotProduct weights
      ((quotient ^ (n + 4 + j)).mulVec (1 : Fin 14 → ℤ)) =
        (U4 (n + 4 + j + 1) : ℤ) := by
    rw [show n + 4 + j = (n + 3 + j) + 1 by omega]
    exact (counting_bridge (n + 3 + j)).symm
  simp_rw [hb] at h
  norm_num only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Finset.sum_empty,
    add_zero, Nat.add_assoc] at h
  linarith only [h]

end D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233157Row
