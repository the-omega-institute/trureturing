/- GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233153Column
   generality: I
   mirror-B: D5/B/S3/Combinatorics/TraceAvoidingArrays/HardinA233153Column
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233153Column.result; premises=D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233153Column.finite_certificate
   digest: The literal 6-column three-state strip satisfies Hardin's order-3 recurrence. -/

/-
admission_basis: open-problem-resolution (#29204; Proved)
escape_witness: none
Finite row tables normalize the row quotient; their helpers are bind-only.
T6: proof_shape=bind-only; consumers=counting_bridge, first_count, initial_relation, result
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
namespace D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233153Column
open D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233155RowTransfer
open D5.S3.Combinatorics.TraceAvoidingArrays
open scoped BigOperators
set_option maxRecDepth 100000

def T6 (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun f : Fin n × Fin 6 → Fin 3 => Legal f)).card

private def codes : List (Fin 729) := [0, 1, 3, 5, 9, 10, 16, 17, 27, 28, 30, 32, 48, 50, 52, 53,
    81, 82, 84, 86, 90, 91, 97, 98, 144, 145, 151, 152, 156, 158, 160, 161, 243, 244, 246, 248,
    252, 253, 259, 260, 270, 271, 273, 275, 291, 293, 295, 296, 432, 433, 435, 437, 453, 455,
    457, 458, 468, 469, 475, 476, 480, 482, 484, 485, 567, 568, 570, 572, 576, 577, 583, 584,
    630, 631, 637, 638, 642, 644, 646, 647, 675, 676, 678, 680, 696, 698, 700, 701, 711, 712,
    718, 719, 723, 725, 727, 728]
def classes : Fin 3 → Fin 3 → Fin 3 → Fin 3 → Fin 3 → Fin 3 → Fin 8 :=
  ![![![![![![0, 1, 0], ![2, 0, 3], ![0, 0, 0]], ![![4, 5, 0], ![0, 0, 0], ![0, 6, 7]], ![![0, 0,
    0], ![0, 0, 0], ![0, 0, 0]]], ![![![2, 3, 0], ![0, 0, 1], ![0, 0, 0]], ![![0, 0, 0], ![0, 0,
    0], ![0, 0, 0]], ![![0, 0, 0], ![4, 0, 5], ![0, 7, 6]]], ![![![0, 0, 0], ![0, 0, 0], ![0, 0,
    0]], ![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]]]],
    ![![![![5, 4, 0], ![6, 0, 7], ![0, 0, 0]], ![![1, 0, 0], ![0, 0, 0], ![0, 2, 3]], ![![0, 0,
    0], ![0, 0, 0], ![0, 0, 0]]], ![![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0,
    0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]]], ![![![0, 0, 0], ![0, 0, 0], ![0, 0,
    0]], ![![3, 2, 0], ![0, 0, 0], ![0, 0, 1]], ![![0, 0, 0], ![7, 0, 6], ![0, 4, 5]]]],
    ![![![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 0,
    0], ![0, 0, 0], ![0, 0, 0]]], ![![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0,
    0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]]], ![![![0, 0, 0], ![0, 0, 0], ![0, 0,
    0]], ![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]]]]],
    ![![![![![0, 1, 0], ![2, 0, 3], ![0, 0, 0]], ![![4, 5, 0], ![0, 0, 0], ![0, 6, 7]], ![![0, 0,
    0], ![0, 0, 0], ![0, 0, 0]]], ![![![2, 3, 0], ![0, 0, 1], ![0, 0, 0]], ![![0, 0, 0], ![0, 0,
    0], ![0, 0, 0]], ![![0, 0, 0], ![4, 0, 5], ![0, 7, 6]]], ![![![0, 0, 0], ![0, 0, 0], ![0, 0,
    0]], ![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]]]],
    ![![![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 0,
    0], ![0, 0, 0], ![0, 0, 0]]], ![![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0,
    0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]]], ![![![0, 0, 0], ![0, 0, 0], ![0, 0,
    0]], ![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]]]],
    ![![![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 0,
    0], ![0, 0, 0], ![0, 0, 0]]], ![![![6, 7, 0], ![5, 0, 4], ![0, 0, 0]], ![![0, 0, 0], ![0, 0,
    0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0], ![0, 3, 2]]], ![![![0, 0, 0], ![0, 0, 0], ![0, 0,
    0]], ![![7, 6, 0], ![0, 0, 0], ![0, 5, 4]], ![![0, 0, 0], ![3, 0, 2], ![0, 1, 0]]]]],
    ![![![![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 0,
    0], ![0, 0, 0], ![0, 0, 0]]], ![![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0,
    0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]]], ![![![0, 0, 0], ![0, 0, 0], ![0, 0,
    0]], ![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]]]],
    ![![![![5, 4, 0], ![6, 0, 7], ![0, 0, 0]], ![![1, 0, 0], ![0, 0, 0], ![0, 2, 3]], ![![0, 0,
    0], ![0, 0, 0], ![0, 0, 0]]], ![![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0,
    0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]]], ![![![0, 0, 0], ![0, 0, 0], ![0, 0,
    0]], ![![3, 2, 0], ![0, 0, 0], ![0, 0, 1]], ![![0, 0, 0], ![7, 0, 6], ![0, 4, 5]]]],
    ![![![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 0,
    0], ![0, 0, 0], ![0, 0, 0]]], ![![![6, 7, 0], ![5, 0, 4], ![0, 0, 0]], ![![0, 0, 0], ![0, 0,
    0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0], ![0, 3, 2]]], ![![![0, 0, 0], ![0, 0, 0], ![0, 0,
    0]], ![![7, 6, 0], ![0, 0, 0], ![0, 5, 4]], ![![0, 0, 0], ![3, 0, 2], ![0, 1, 0]]]]]]

def classify (r : Row 6) : Fin 8 := classes (r 0) (r 1) (r 2) (r 3) (r 4) (r 5)
def quotient : Matrix (Fin 8) (Fin 8) ℤ :=
  ![![5, 5, 4, 4, 3, 3, 1, 1], ![3, 3, 3, 3, 3, 3, 2, 2], ![4, 4, 4, 4, 3, 3, 1, 1], ![2, 2, 2,
    2, 2, 2, 3, 3], ![3, 3, 3, 3, 3, 3, 1, 1], ![4, 4, 2, 2, 3, 3, 2, 2], ![2, 2, 2, 2, 3, 3, 2,
    2], ![1, 1, 1, 1, 1, 1, 3, 3]]
def weights : Fin 8 → ℤ := ![12, 12, 12, 12, 12, 12, 12, 12]

set_option maxHeartbeats 10000000 in
private theorem codes_table : legalCodes 6 = codes := by decide +kernel

private def classCount (r : Row 6) (s : Fin 8) : ℤ :=
  (codes.map (fun c => if compatible r (decode 6 c) ∧ classify (decode 6 c) = s
    then (1 : ℤ) else 0)).sum

set_option maxHeartbeats 10000000 in
private theorem row_counts_code : ∀ a : Fin 729, rowLegal (decode 6 a) →
    ∀ s : Fin 8, classCount (decode 6 a) s = quotient (classify (decode 6 a)) s := by
  decide +kernel

private theorem row_counts : ∀ r : Row 6, rowLegal r → ∀ s : Fin 8,
    (∑ c : Row 6, if rowLegal c ∧ compatible r c ∧ classify c = s then (1 : ℤ) else 0) =
      quotient (classify r) s := by
  intro r hr s
  have hs := row_sum 6 (fun c => if compatible r c ∧ classify c = s then (1 : ℤ) else 0)
  simp only [← ite_and] at hs
  rw [hs, codes_table]
  have he : decode 6 (finFunctionFinEquiv r) = r :=
    Equiv.symm_apply_apply finFunctionFinEquiv r
  have hc := row_counts_code (finFunctionFinEquiv r) (by rw [he]; exact hr) s
  rw [he] at hc
  exact hc

set_option maxHeartbeats 10000000 in
private theorem initial_weights : ∀ s : Fin 8,
    (∑ c : Row 6, if rowLegal c ∧ classify c = s then (1 : ℤ) else 0) = weights s := by
  intro s
  have hs := row_sum 6 (fun c => if classify c = s then (1 : ℤ) else 0)
  simp only [← ite_and] at hs
  rw [hs, codes_table]
  revert s
  decide +kernel

private def W : Fin 5 → Fin 8 → ℤ :=
  ![![1, 1, 1, 1, 1, 1, 1, 1], ![26, 22, 24, 18, 20, 22, 18, 12], ![564, 456, 516, 354, 426, 462,
    366, 222], ![11832, 9510, 10812, 7320, 8922, 9660, 7620, 4542], ![247146, 198492, 225804,
    152598, 186330, 201702, 159018, 94542]]
private theorem powers_table : ∀ j : Fin 5,
    (quotient ^ j.val).mulVec (1 : Fin 8 → ℤ) = W j := by
  apply TransferMatrix.tabulatedPowers
  · exact List.ofFn_inj.mp rfl
  · intro j
    fin_cases j <;> exact List.ofFn_inj.mp rfl

private theorem vector_relation :
    (quotient ^ (1 + 3)).mulVec (1 : Fin 8 → ℤ) =
      ∑ j : Fin 3, (![81, -90, 25] : Fin 3 → ℤ) j •
        (quotient ^ (1 + j.val)).mulVec (1 : Fin 8 → ℤ) := by
  have hp : (quotient ^ (1 + 3)).mulVec (1 : Fin 8 → ℤ) = W 4 := powers_table 4
  rw [hp]
  have hc : (∑ j : Fin 3, (![81, -90, 25] : Fin 3 → ℤ) j •
      (quotient ^ (1 + j.val)).mulVec (1 : Fin 8 → ℤ)) =
      ∑ j : Fin 3, (![81, -90, 25] : Fin 3 → ℤ) j • W ⟨1 + j.val, by omega⟩ := by
    apply Finset.sum_congr rfl
    intro j _
    rw [powers_table ⟨1 + j.val, by omega⟩]
  rw [hc]
  exact List.ofFn_inj.mp (by decide +kernel)

theorem finite_certificate :
    (∀ r : Row 6, rowLegal r → ∀ s : Fin 8,
      (∑ c : Row 6, if rowLegal c ∧ compatible r c ∧ classify c = s then (1 : ℤ) else 0) =
        quotient (classify r) s) ∧
    (∀ s : Fin 8, (∑ c : Row 6, if rowLegal c ∧ classify c = s then (1 : ℤ) else 0) =
      weights s) ∧
    (quotient ^ (1 + 3)).mulVec (1 : Fin 8 → ℤ) =
      ∑ j : Fin 3, (![81, -90, 25] : Fin 3 → ℤ) j •
        (quotient ^ (1 + j.val)).mulVec (1 : Fin 8 → ℤ) :=
  ⟨row_counts, initial_weights, vector_relation⟩

private theorem counting_bridge (n : ℕ) :
    (T6 (n + 2) : ℤ) = dotProduct weights
      ((quotient ^ (n + 1)).mulVec (1 : Fin 8 → ℤ)) :=
  count_transfer 6 8 classify quotient weights
    finite_certificate.1 finite_certificate.2.1 n

set_option maxHeartbeats 10000000 in
private theorem first_count : T6 1 = 96 := by decide +kernel

private theorem initial_relation : (T6 4 : ℤ) =
    25 * (T6 (3) : ℤ) - 90 * (T6 (2) : ℤ) + 81 * (T6 (1) : ℤ) := by
  have h1 : (T6 1 : ℤ) = 96 := by exact_mod_cast first_count
  have h2 := counting_bridge 0
  change (T6 2 : ℤ) = dotProduct weights
    ((quotient ^ 1).mulVec (1 : Fin 8 → ℤ)) at h2
  have hp2 := powers_table (1 : Fin 5)
  change (quotient ^ 1).mulVec (1 : Fin 8 → ℤ) = W 1 at hp2
  rw [hp2] at h2
  have h3 := counting_bridge 1
  change (T6 3 : ℤ) = dotProduct weights
    ((quotient ^ 2).mulVec (1 : Fin 8 → ℤ)) at h3
  have hp3 := powers_table (2 : Fin 5)
  change (quotient ^ 2).mulVec (1 : Fin 8 → ℤ) = W 2 at hp3
  rw [hp3] at h3
  have h4 := counting_bridge 2
  change (T6 4 : ℤ) = dotProduct weights
    ((quotient ^ 3).mulVec (1 : Fin 8 → ℤ)) at h4
  have hp4 := powers_table (3 : Fin 5)
  change (quotient ^ 3).mulVec (1 : Fin 8 → ℤ) = W 3 at hp4
  rw [hp4] at h4
  norm_num [W, weights, dotProduct, Fin.sum_univ_succ] at *
  omega

theorem result (n : ℕ) : (T6 (n + 4) : ℤ) =
    25 * (T6 (n + 3) : ℤ) - 90 * (T6 (n + 2) : ℤ) + 81 * (T6 (n + 1) : ℤ) := by
  cases n with
  | zero => exact initial_relation
  | succ n =>
    have h := TransferMatrix.scalarRelationShift quotient weights 3 1
      (![81, -90, 25] : Fin 3 → ℤ) finite_certificate.2.2 n
    have hb (j : ℕ) : dotProduct weights
        ((quotient ^ (n + 1 + j)).mulVec (1 : Fin 8 → ℤ)) = (T6 (n + j + 2) : ℤ) := by
      rw [show n + 1 + j = n + j + 1 by omega]
      exact (counting_bridge (n + j)).symm
    simp_rw [hb] at h
    norm_num only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ,
      Matrix.cons_val_zero, Matrix.cons_val_succ, Finset.sum_empty,
      add_zero, Nat.add_assoc] at h
    simp only [Nat.add_assoc]
    linarith

end D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233153Column
