/- GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233152Column
   generality: I
   mirror-B: D5/B/S3/Combinatorics/TraceAvoidingArrays/HardinA233152Column
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233152Column.result; premises=D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233152Column.finite_certificate
   digest: The literal 5-column three-state strip satisfies Hardin's order-2 recurrence. -/

/-
admission_basis: open-problem-resolution (#29204; Proved)
escape_witness: none
Finite row tables normalize the row quotient; their helpers are bind-only.
T5: proof_shape=bind-only; consumers=counting_bridge, first_count, initial_relation, result
codes: proof_shape=bind-only; consumers=codes_table, classCount
classes: proof_shape=bind-only; consumers=classify
classify: proof_shape=bind-only; consumers=classCount, row_counts_code, row_counts, initial_weights, finite_certificate, counting_bridge
quotient: proof_shape=bind-only; consumers=row_counts_code, row_counts, powers_table, vector_relation, finite_certificate, counting_bridge, initial_relation, result
weights: proof_shape=bind-only; consumers=initial_weights, finite_certificate, counting_bridge, initial_relation, result
codes_table: proof_shape=bind-only; consumers=row_counts, initial_weights
classCount: proof_shape=bind-only; consumers=row_counts_code
row_counts_code: proof_shape=bind-only; consumers=row_counts
row_counts: proof_shape=bind-only; consumers=finite_certificate
initial_weights: proof_shape=bind-only; consumers=finite_certificate
W: proof_shape=bind-only; consumers=powers_table, vector_relation, initial_relation
powers_table: proof_shape=bind-only; consumers=vector_relation, initial_relation
vector_relation: proof_shape=bind-only; consumers=finite_certificate
finite_certificate: proof_shape=bind-only; consumers=counting_bridge, result
counting_bridge: proof_shape=bind-only; consumers=initial_relation, result
first_count: proof_shape=bind-only; consumers=initial_relation
initial_relation: proof_shape=bind-only; consumers=result
result: proof_shape=bind-only; consumers=Reg.Recurrence.family
-/
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233155RowTransfer
import D5.S3.Combinatorics.TraceAvoidingArrays.TransferMatrix
import Mathlib.Tactic

/-! A finite row quotient transports the recurrence to every strip height. -/
namespace D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233152Column
open D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233155RowTransfer
open D5.S3.Combinatorics.TraceAvoidingArrays
open scoped BigOperators
set_option maxRecDepth 100000

def T5 (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun f : Fin n × Fin 5 → Fin 3 => Legal f)).card

private def codes : List (Fin 243) := [0, 1, 3, 5, 9, 10, 16, 17, 27, 28, 30, 32, 48, 50, 52, 53,
    81, 82, 84, 86, 90, 91, 97, 98, 144, 145, 151, 152, 156, 158, 160, 161, 189, 190, 192, 194,
    210, 212, 214, 215, 225, 226, 232, 233, 237, 239, 241, 242]
def classes : Fin 3 → Fin 3 → Fin 3 → Fin 3 → Fin 3 → Fin 3 :=
  ![![![![![0, 1, 0], ![1, 0, 2], ![0, 0, 0]], ![![1, 0, 0], ![0, 0, 0], ![0, 1, 2]], ![![0, 0,
    0], ![0, 0, 0], ![0, 0, 0]]], ![![![1, 2, 0], ![0, 0, 1], ![0, 0, 0]], ![![0, 0, 0], ![0, 0,
    0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0], ![0, 2, 1]]], ![![![0, 0, 0], ![0, 0, 0], ![0, 0,
    0]], ![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]]]],
    ![![![![0, 1, 0], ![1, 0, 2], ![0, 0, 0]], ![![1, 0, 0], ![0, 0, 0], ![0, 1, 2]], ![![0, 0,
    0], ![0, 0, 0], ![0, 0, 0]]], ![![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0,
    0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]]], ![![![0, 0, 0], ![0, 0, 0], ![0, 0,
    0]], ![![2, 1, 0], ![0, 0, 0], ![0, 0, 1]], ![![0, 0, 0], ![2, 0, 1], ![0, 1, 0]]]],
    ![![![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 0,
    0], ![0, 0, 0], ![0, 0, 0]]], ![![![1, 2, 0], ![0, 0, 1], ![0, 0, 0]], ![![0, 0, 0], ![0, 0,
    0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0], ![0, 2, 1]]], ![![![0, 0, 0], ![0, 0, 0], ![0, 0,
    0]], ![![2, 1, 0], ![0, 0, 0], ![0, 0, 1]], ![![0, 0, 0], ![2, 0, 1], ![0, 1, 0]]]]]

def classify (r : Row 5) : Fin 3 := classes (r 0) (r 1) (r 2) (r 3) (r 4)
def quotient : Matrix (Fin 3) (Fin 3) ℤ :=
  ![![5, 8, 3], ![4, 7, 3], ![2, 5, 3]]
def weights : Fin 3 → ℤ := ![12, 24, 12]

set_option maxHeartbeats 10000000 in
private theorem codes_table : legalCodes 5 = codes := by decide +kernel

private def classCount (r : Row 5) (s : Fin 3) : ℤ :=
  (codes.map (fun c => if compatible r (decode 5 c) ∧ classify (decode 5 c) = s
    then (1 : ℤ) else 0)).sum

set_option maxHeartbeats 10000000 in
private theorem row_counts_code : ∀ a : Fin 243, rowLegal (decode 5 a) →
    ∀ s : Fin 3, classCount (decode 5 a) s = quotient (classify (decode 5 a)) s := by
  decide +kernel

private theorem row_counts : ∀ r : Row 5, rowLegal r → ∀ s : Fin 3,
    (∑ c : Row 5, if rowLegal c ∧ compatible r c ∧ classify c = s then (1 : ℤ) else 0) =
      quotient (classify r) s := by
  intro r hr s
  have hs := row_sum 5 (fun c => if compatible r c ∧ classify c = s then (1 : ℤ) else 0)
  simp only [← ite_and] at hs
  rw [hs, codes_table]
  have he : decode 5 (finFunctionFinEquiv r) = r :=
    Equiv.symm_apply_apply finFunctionFinEquiv r
  have hc := row_counts_code (finFunctionFinEquiv r) (by rw [he]; exact hr) s
  rw [he] at hc
  exact hc

set_option maxHeartbeats 10000000 in
private theorem initial_weights : ∀ s : Fin 3,
    (∑ c : Row 5, if rowLegal c ∧ classify c = s then (1 : ℤ) else 0) = weights s := by
  intro s
  have hs := row_sum 5 (fun c => if classify c = s then (1 : ℤ) else 0)
  simp only [← ite_and] at hs
  rw [hs, codes_table]
  revert s
  decide +kernel

private def W : Fin 4 → Fin 3 → ℤ :=
  ![![1, 1, 1], ![16, 14, 10], ![222, 192, 132], ![3042, 2628, 1800]]
private theorem powers_table : ∀ j : Fin 4,
    (quotient ^ j.val).mulVec (1 : Fin 3 → ℤ) = W j := by
  apply TransferMatrix.tabulatedPowers
  · exact List.ofFn_inj.mp rfl
  · intro j
    fin_cases j <;> exact List.ofFn_inj.mp rfl

private theorem vector_relation :
    (quotient ^ (1 + 2)).mulVec (1 : Fin 3 → ℤ) =
      ∑ j : Fin 2, (![-18, 15] : Fin 2 → ℤ) j •
        (quotient ^ (1 + j.val)).mulVec (1 : Fin 3 → ℤ) := by
  have hp : (quotient ^ (1 + 2)).mulVec (1 : Fin 3 → ℤ) = W 3 := powers_table 3
  rw [hp]
  have hc : (∑ j : Fin 2, (![-18, 15] : Fin 2 → ℤ) j •
      (quotient ^ (1 + j.val)).mulVec (1 : Fin 3 → ℤ)) =
      ∑ j : Fin 2, (![-18, 15] : Fin 2 → ℤ) j • W ⟨1 + j.val, by omega⟩ := by
    apply Finset.sum_congr rfl
    intro j _
    rw [powers_table ⟨1 + j.val, by omega⟩]
  rw [hc]
  exact List.ofFn_inj.mp (by decide +kernel)

theorem finite_certificate :
    (∀ r : Row 5, rowLegal r → ∀ s : Fin 3,
      (∑ c : Row 5, if rowLegal c ∧ compatible r c ∧ classify c = s then (1 : ℤ) else 0) =
        quotient (classify r) s) ∧
    (∀ s : Fin 3, (∑ c : Row 5, if rowLegal c ∧ classify c = s then (1 : ℤ) else 0) =
      weights s) ∧
    (quotient ^ (1 + 2)).mulVec (1 : Fin 3 → ℤ) =
      ∑ j : Fin 2, (![-18, 15] : Fin 2 → ℤ) j •
        (quotient ^ (1 + j.val)).mulVec (1 : Fin 3 → ℤ) :=
  ⟨row_counts, initial_weights, vector_relation⟩

private theorem counting_bridge (n : ℕ) :
    (T5 (n + 2) : ℤ) = dotProduct weights
      ((quotient ^ (n + 1)).mulVec (1 : Fin 3 → ℤ)) :=
  count_transfer 5 3 classify quotient weights
    finite_certificate.1 finite_certificate.2.1 n

set_option maxHeartbeats 10000000 in
private theorem first_count : T5 1 = 48 := by decide +kernel

private theorem initial_relation : (T5 3 : ℤ) =
    15 * (T5 (2) : ℤ) - 18 * (T5 (1) : ℤ) := by
  have h1 : (T5 1 : ℤ) = 48 := by exact_mod_cast first_count
  have h2 := counting_bridge 0
  change (T5 2 : ℤ) = dotProduct weights
    ((quotient ^ 1).mulVec (1 : Fin 3 → ℤ)) at h2
  have hp2 := powers_table (1 : Fin 4)
  change (quotient ^ 1).mulVec (1 : Fin 3 → ℤ) = W 1 at hp2
  rw [hp2] at h2
  have h3 := counting_bridge 1
  change (T5 3 : ℤ) = dotProduct weights
    ((quotient ^ 2).mulVec (1 : Fin 3 → ℤ)) at h3
  have hp3 := powers_table (2 : Fin 4)
  change (quotient ^ 2).mulVec (1 : Fin 3 → ℤ) = W 2 at hp3
  rw [hp3] at h3
  norm_num [W, weights, dotProduct, Fin.sum_univ_succ] at *
  omega

theorem result (n : ℕ) : (T5 (n + 3) : ℤ) =
    15 * (T5 (n + 2) : ℤ) - 18 * (T5 (n + 1) : ℤ) := by
  cases n with
  | zero => exact initial_relation
  | succ n =>
    have h := TransferMatrix.scalarRelationShift quotient weights 2 1
      (![-18, 15] : Fin 2 → ℤ) finite_certificate.2.2 n
    have hb (j : ℕ) : dotProduct weights
        ((quotient ^ (n + 1 + j)).mulVec (1 : Fin 3 → ℤ)) = (T5 (n + j + 2) : ℤ) := by
      rw [show n + 1 + j = n + j + 1 by omega]
      exact (counting_bridge (n + j)).symm
    simp_rw [hb] at h
    norm_num only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ,
      Matrix.cons_val_zero, Matrix.cons_val_succ, Finset.sum_empty,
      add_zero, Nat.add_assoc] at h
    simp only [Nat.add_assoc]
    linarith

end D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233152Column
