/- GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233156Row
   generality: I
   mirror-B: D5/B/S3/Combinatorics/TraceAvoidingArrays/HardinA233156Row
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233156Row.result; premises=D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233156Row.finite_certificate
   digest: The literal 3-row three-state strip satisfies Hardin's order-2 recurrence. -/

/-
admission_basis: open-problem-resolution (#29231; Proved)
escape_witness: none
The equality-pattern tables and power identities normalize finite arithmetic.
U3: proof_shape=bind-only; consumers=counting_bridge, result
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
namespace D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233156Row
open D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233155RowTransfer
open D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233155ColumnTransfer
open D5.S3.Combinatorics.TraceAvoidingArrays
open scoped BigOperators
set_option maxRecDepth 100000

def U3 (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun f : Fin 3 × Fin n → Fin 3 => Legal f)).card

def classes : Fin 3 → Fin 3 → Fin 3 → Fin 5 :=
  ![![![0, 1, 1], ![2, 3, 4], ![2, 4, 3]], ![![3, 2, 4], ![1, 0, 1], ![4, 2, 3]], ![![3, 4, 2], ![4,
    3, 2], ![1, 1, 0]]]
def classify (r : Row 3) : Fin 5 := classes (r 0) (r 1) (r 2)
def representatives : Fin 5 → Row 3 :=
  ![![0, 0, 0], ![0, 0, 1], ![0, 1, 0], ![0, 1, 1], ![0, 1, 2]]
def quotient : Matrix (Fin 5) (Fin 5) ℤ :=
  ![![2, 2, 2, 2, 0], ![1, 1, 0, 1, 1], ![1, 1, 0, 0, 0], ![1, 1, 1, 1, 0], ![0, 0, 0, 1, 1]]
def weights : Fin 5 → ℤ := ![3, 6, 6, 6, 6]
private def successors : Fin 5 → List (Fin 5) :=
  ![[0, 3, 2, 1, 1, 2, 3, 0], [0, 3, 1, 4], [0, 1], [0, 2, 1, 3], [4, 3]]

set_option maxHeartbeats 10000000 in
private theorem class_invariant : ∀ (e : Equiv.Perm (Fin 3)) (r : Row 3),
    classify (relabel e r) = classify r := by decide +kernel
set_option maxHeartbeats 10000000 in
private theorem class_representative : ∀ r : Row 3, ∃ e : Equiv.Perm (Fin 3),
    relabel e r = representatives (classify r) := by decide +kernel
set_option maxHeartbeats 10000000 in
private theorem successor_table : ∀ i : Fin 5,
    successorClasses classify (representatives i) = successors i := by decide +kernel
set_option maxHeartbeats 10000000 in
private theorem representative_rows : ∀ i s : Fin 5,
    ((successorClasses classify (representatives i)).map
      (fun j => if j = s then (1 : ℤ) else 0)).sum = quotient i s := by
  have ht : List.ofFn (fun i : Fin 5 => List.ofFn (fun s : Fin 5 =>
      ((successors i).map (fun j => if j = s then (1 : ℤ) else 0)).sum)) =
      List.ofFn (fun i : Fin 5 => List.ofFn (fun s : Fin 5 => quotient i s)) := rfl
  intro i s
  rw [successor_table]
  exact congrFun (List.ofFn_inj.mp (congrFun (List.ofFn_inj.mp ht) i)) s
set_option maxHeartbeats 10000000 in
private theorem row_counts : ∀ r : Row 3, ∀ s : Fin 5,
    (∑ c : Row 3, if columnCompatible r c ∧ classify c = s then (1 : ℤ) else 0) =
      quotient (classify r) s :=
  quotient_rows 3 5 classify representatives quotient class_invariant
    class_representative representative_rows
set_option maxHeartbeats 10000000 in
private theorem initial_weights : ∀ s : Fin 5,
    (∑ c : Row 3, if classify c = s then (1 : ℤ) else 0) = weights s := by
  intro s
  rw [← (finFunctionFinEquiv (m := 3) (n := 3)).symm.sum_comp]
  rw [← List.sum_ofFn, List.ofFn_eq_map]
  revert s
  decide +kernel
private def W : Fin 5 → Fin 5 → ℤ :=
  ![![1, 1, 1, 1, 1], ![8, 4, 2, 4, 2], ![36, 18, 12, 18, 6], ![168, 78, 54, 84, 24], ![768, 354,
    246, 384, 108]]
set_option maxHeartbeats 10000000 in
private theorem powers_table : ∀ j : Fin 5,
    (quotient ^ j.val).mulVec (1 : Fin 5 → ℤ) = W j := by
  apply TransferMatrix.tabulatedPowers
  · exact List.ofFn_inj.mp rfl
  · intro j
    fin_cases j <;> exact List.ofFn_inj.mp rfl
set_option maxHeartbeats 10000000 in
private theorem vector_relation :
    (quotient ^ (2 + 2)).mulVec (1 : Fin 5 → ℤ) =
      ∑ j : Fin 2, (![-2, 5] : Fin 2 → ℤ) j •
        (quotient ^ (2 + j.val)).mulVec (1 : Fin 5 → ℤ) := by
  rw [show 2 + 2 = (4 : Fin 5).val from rfl, powers_table]
  have hh (j : Fin 2) : (quotient ^ (2 + j.val)).mulVec (1 : Fin 5 → ℤ) =
      W ⟨2 + j.val, by omega⟩ := powers_table ⟨2 + j.val, by omega⟩
  simp_rw [hh]
  exact List.ofFn_inj.mp (by decide +kernel)

set_option maxHeartbeats 10000000 in
theorem finite_certificate :
    (∀ r : Row 3, ∀ s : Fin 5,
      (∑ c : Row 3, if columnCompatible r c ∧ classify c = s then (1 : ℤ) else 0) =
        quotient (classify r) s) ∧
    (∀ s : Fin 5, (∑ c : Row 3, if classify c = s then (1 : ℤ) else 0) = weights s) ∧
    (quotient ^ (2 + 2)).mulVec (1 : Fin 5 → ℤ) =
      ∑ j : Fin 2, (![-2, 5] : Fin 2 → ℤ) j •
        (quotient ^ (2 + j.val)).mulVec (1 : Fin 5 → ℤ) :=
  ⟨row_counts, initial_weights, vector_relation⟩

set_option maxHeartbeats 10000000 in
private theorem counting_bridge (n : ℕ) :
    (U3 (n + 2) : ℤ) = dotProduct weights
      ((quotient ^ (n + 1)).mulVec (1 : Fin 5 → ℤ)) :=
  count_transfer 3 5 classify quotient weights
    finite_certificate.1 finite_certificate.2.1 n

set_option maxHeartbeats 10000000 in
theorem result (n : ℕ) : (U3 (n + 5) : ℤ) =
    5 * (U3 (n + 4) : ℤ) - 2 * (U3 (n + 3) : ℤ) := by
  have h := TransferMatrix.scalarRelationShift quotient weights 2 2
    (![-2, 5] : Fin 2 → ℤ) finite_certificate.2.2 n
  have hb (j : ℕ) : dotProduct weights
      ((quotient ^ (n + 2 + j)).mulVec (1 : Fin 5 → ℤ)) =
        (U3 (n + 2 + j + 1) : ℤ) := by
    rw [show n + 2 + j = (n + 1 + j) + 1 by omega]
    exact (counting_bridge (n + 1 + j)).symm
  simp_rw [hb] at h
  norm_num only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Finset.sum_empty,
    add_zero, Nat.add_assoc] at h
  linarith only [h]

end D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233156Row
