/- GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233159RowCertificate
   generality: I
   mirror-B: D5/B/S3/Combinatorics/TraceAvoidingArrays/HardinA233159RowCertificate
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233159Row.result; premises=D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233159Row.finite_certificate
   digest: A finite column quotient supplies the order-nine recurrence for six-row strips. -/

/-
admission_basis: open-problem-resolution (#29231; Proved)
escape_witness: none
Finite tables and arithmetic identities instantiate existing finite structures.
successor_table: proof_shape=bind-only; consumers=quotient_certificate
representative_rows: proof_shape=bind-only; consumers=quotient_certificate
row_counts: proof_shape=bind-only; consumers=quotient_certificate
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
    successorClasses classify (representatives i) = successors i := by decide +kernel

set_option maxHeartbeats 10000000 in
private theorem representative_rows : ∀ i s : Fin 122,
    ((successorClasses classify (representatives i)).map
      (fun j => if j = s then (1 : ℤ) else 0)).sum = quotient i s := by
  have ht : List.ofFn (fun i : Fin 122 => List.ofFn (fun s : Fin 122 =>
      ((successors i).map (fun j => if j = s then (1 : ℤ) else 0)).sum)) =
      List.ofFn (fun i : Fin 122 => List.ofFn (fun s : Fin 122 => quotient i s)) := rfl
  intro i s
  rw [successor_table]
  exact congrFun (List.ofFn_inj.mp (congrFun (List.ofFn_inj.mp ht) i)) s

set_option maxHeartbeats 10000000 in
private theorem row_counts : ∀ r : Row 6, ∀ s : Fin 122,
    (∑ c : Row 6, if columnCompatible r c ∧ classify c = s then (1 : ℤ) else 0) =
      quotient (classify r) s :=
  quotient_rows 6 122 classify representatives quotient equality_classes.1
    equality_classes.2 representative_rows

set_option maxHeartbeats 10000000 in
private theorem initial_weights : ∀ s : Fin 122,
    (∑ c : Row 6, if classify c = s then (1 : ℤ) else 0) = weights s := by
  intro s
  rw [← (finFunctionFinEquiv (m := 3) (n := 6)).symm.sum_comp]
  rw [← List.sum_ofFn, List.ofFn_eq_map]
  revert s
  decide +kernel

set_option maxHeartbeats 10000000 in
private theorem mulVec_successors (v : Fin 122 → ℤ) (i : Fin 122) :
    quotient.mulVec v i = ((successors i).map v).sum := by
  have hq (s : Fin 122) : quotient i s =
      ((successors i).map (fun j => if j = s then (1 : ℤ) else 0)).sum := by
    rw [← representative_rows i s, successor_table]
  change (∑ s : Fin 122, quotient i s * v s) = _
  simp_rw [hq]
  generalize successors i = l
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, add_mul, Finset.sum_add_distrib]
    rw [ih]
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
