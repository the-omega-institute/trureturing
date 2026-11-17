/- GID: D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/HardinA229585Strip
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/StripDefectsWidth7/HardinA229585Strip
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/HardinA229585Strip.result; premises=D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/HardinA229585Strip.finite_certificate
   digest: The integer recurrence for canonical one-defect width-7 arrays. -/

/-
admission_basis: open-problem-resolution (#30580; Proved)
escape_witness: none
cellOrder: proof_shape=bind-only; consumers=Normal, scale_count
Normal: proof_shape=bind-only; consumers=a, scale_count
decidableNormal: proof_shape=bind-only; consumers=a
a: proof_shape=bind-only; consumers=result
edge: proof_shape=bind-only; consumers=cross_relabel, count_transfer
class_relabel: proof_shape=bind-only; consumers=transition_counts
horizontal_relabel: proof_shape=bind-only; consumers=cross_relabel, transition_counts
cross_relabel: proof_shape=bind-only; consumers=transition_counts
transition_counts: proof_shape=bind-only; consumers=finite_certificate
finite_certificate: proof_shape=bind-only; consumers=count_transfer, powers_table, polynomial_relation
count_transfer: proof_shape=bind-only; consumers=result
powers_table: proof_shape=bind-only; consumers=polynomial_relation, result
polynomial_relation: proof_shape=bind-only; consumers=result
scale_count: proof_shape=bind-only; consumers=result
result: proof_shape=bind-only; consumers=external sequence A229585
-/

import D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.HardinA229585StripData
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.HardinA229585StripCertificate
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.HardinA229585StripOrbitCertificate
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical
import Mathlib.Logic.Equiv.Fin.Basic

set_option profiler true

/-! Exact finite certificates for the width-seven one-defect strip. -/
open scoped BigOperators
namespace D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.HardinA229585Strip
open D5.S3.StatisticalMechanics.Potts.StripDefects
open D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer (bondDefects defects literalCount continuation lumped_count forward forward_shift)
open D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical (Canonical canonical_pattern_card)
open HardinA229585StripData

private abbrev cellOrder (n : ℕ) : LinearOrder (Fin n × Fin 7) :=
  LinearOrder.lift' finProdFinEquiv finProdFinEquiv.injective
private def Normal {n : ℕ} (A : Fin n × Fin 7 → Fin 3) : Prop :=
  @Canonical (Fin n × Fin 7) (cellOrder n).toLT 3 A
private instance decidableNormal {n : ℕ} (A : Fin n × Fin 7 → Fin 3) : Decidable (Normal A) := by
  unfold Normal Canonical
  change Decidable (∀ (i : Fin n × Fin 7) (b : Fin 3), b < A i →
    ∃ j : Fin n × Fin 7, finProdFinEquiv j < finProdFinEquiv i ∧ A j = b)
  infer_instance

/-- The finite filter ranges over every three-colour array of the indicated shape. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter fun A : Fin n × Fin 7 → Fin 3 =>
    defects horizontal antidiagonal (List.ofFn fun i j => A (i, j)) = 1 ∧ Normal A).card

private theorem edge (r t : Row) : bondDefects antidiagonal r t = cross (boundary r) t := by
  unfold cross bondDefects
  apply congrArg Finset.card
  ext e
  by_cases he : e ∈ antidiagonal
  · obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp he
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
    rfl
  · simp [he]

private theorem class_relabel (e : Equiv.Perm (Fin 3)) (p : Boundary) (d : ℕ) :
    cl (e ∘ p) d = cl p d := by
  have hn :
      D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255ShapeSymmetry.normalize (e ∘ p) =
      D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255ShapeSymmetry.normalize p := by
    funext j
    simp only [D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255ShapeSymmetry.normalize,
      Function.comp_apply, e.injective.eq_iff]
  simp only [cl,
    D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255ShapeSymmetry.proper,
    D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255ShapeSymmetry.classOf,
    hn,
    Function.comp_apply, e.injective.eq_iff, e.injective.ne_iff]
  rfl

private theorem horizontal_relabel (e : Equiv.Perm (Fin 3)) (r : Row) :
    bondDefects horizontal (e ∘ r) (e ∘ r) = bondDefects horizontal r r := by
  simpa only [List.map_cons, List.map_nil, defects, DefectTransfer.tailDefects,
    Nat.add_zero] using DefectTransfer.relabel_defects horizontal antidiagonal e [r]

private theorem cross_relabel (e : Equiv.Perm (Fin 3)) (p : Boundary) (r : Row) :
    cross (e ∘ p) (e ∘ r) = cross p r := by
  have h := DefectTransfer.relabel_defects horizontal antidiagonal e [Fin.cons 0 p, r]
  simp only [List.map_cons, List.map_nil, defects, DefectTransfer.tailDefects,
    Nat.add_zero, horizontal_relabel, edge] at h
  change bondDefects horizontal (Fin.cons 0 p) (Fin.cons 0 p) +
      (cross (e ∘ p) (e ∘ r) + bondDefects horizontal r r) =
    bondDefects horizontal (Fin.cons 0 p) (Fin.cons 0 p) +
      (cross p r + bondDefects horizontal r r) at h
  omega

private theorem transition_counts (p : Boundary) (d : Fin 2) (hp : Valid p d.val)
    (s : Fin 72) :
    (∑ r : Row, if cross p r + bondDefects horizontal r r ≤ d.val ∧
      cl (boundary r) (d.val - (cross p r + bondDefects horizontal r r)) = s
      then (1 : ℤ) else 0) = T (cl p d.val) s := by
  obtain ⟨p', ⟨hnormal, e, he⟩, _⟩ :=
    D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical.canonical_exists_unique p
  have hv : Valid p' d.val := by
    rw [he]
    simpa only [Valid, Function.comp_apply, e.injective.eq_iff] using hp
  have hT :
      (∑ r : Row, if cross p' r + bondDefects horizontal r r ≤ d.val ∧
        cl (boundary r) (d.val - (cross p' r + bondDefects horizontal r r)) = s
        then (1 : ℤ) else 0) = T (cl p' d.val) s := by
    exact HardinA229585StripOrbitCertificate.transition_counts p' d hv hnormal s
  rw [he] at hT
  let E : Row ≃ Row := Equiv.piCongrRight fun _ : Fin 7 => e
  rw [← E.sum_comp] at hT
  change (∑ r : Row, if cross (e ∘ p) (e ∘ r) +
    bondDefects horizontal (e ∘ r) (e ∘ r) ≤ d.val ∧
    cl (boundary (e ∘ r)) (d.val - (cross (e ∘ p) (e ∘ r) +
      bondDefects horizontal (e ∘ r) (e ∘ r))) = s then (1 : ℤ) else 0) =
    T (cl (e ∘ p) d.val) s at hT
  simpa only [cross_relabel, horizontal_relabel,
    show ∀ r : Row, boundary (e ∘ r) = e ∘ boundary r from fun _ => rfl,
    class_relabel] using hT

/-- Counts, budget preservation and the integer polynomial certificate. -/
theorem finite_certificate :
    (∀ p (d : Fin 2), Valid p d.val →
      terminal (cl p d.val) = (if d.val = 0 then 1 else 0)) ∧
    (∀ p (d : Fin 2), Valid p d.val → ∀ r : Row,
      cross p r + bondDefects horizontal r r ≤ d.val →
      Valid (boundary r) (d.val - (cross p r + bondDefects horizontal r r))) ∧
    (∀ p (d : Fin 2), Valid p d.val → ∀ s : Fin 72,
      (∑ r : Row, if cross p r + bondDefects horizontal r r ≤ d.val ∧
        cl (boundary r) (d.val - (cross p r + bondDefects horizontal r r)) = s
        then (1 : ℤ) else 0) = T (cl p d.val) s) ∧
    (∀ r : Row, bondDefects horizontal r r ≤ 1 →
      Valid (boundary r) (1 - bondDefects horizontal r r)) ∧
    (∀ s : Fin 72, (∑ r : Row, if bondDefects horizontal r r ≤ 1 ∧
      cl (boundary r) (1 - bondDefects horizontal r r) = s then (1 : ℤ) else 0) = initial s) ∧
    (W 0 = initial ∧ ∀ i : Fin 10, W i.succ = Matrix.vecMul (W i.castSucc) T) ∧
    W 10 = ∑ j : Fin 8, (![-656100, 1574640, -1513404, 750384, -206469, 31428, -2466, 84] j : ℤ) • W ⟨2 + j.val, by omega⟩ := by
  obtain ⟨hz, hn, hi, hv, hw, hp⟩ := HardinA229585StripCertificate.structural_certificate
  exact ⟨hz, hn, transition_counts, hi, hv, hw, hp⟩

private theorem count_transfer (n : ℕ) :
    (literalCount (q := 3) horizontal antidiagonal 1 (n + 1) : ℤ) =
      dotProduct initial ((T ^ n).mulVec terminal) := by
  apply lumped_count horizontal antidiagonal boundary cross Valid cl T initial terminal 1 edge
  · intro p d h
    exact finite_certificate.1 p ⟨d, by have := h.1; omega⟩ h
  · intro p d h r hr
    exact finite_certificate.2.1 p ⟨d, by have := h.1; omega⟩ h r hr
  · intro p d h s
    exact finite_certificate.2.2.1 p ⟨d, by have := h.1; omega⟩ h s
  · exact finite_certificate.2.2.2.1
  · exact finite_certificate.2.2.2.2.1

private theorem powers_table (i : Fin 11) : forward T initial i.val = W i := by
  induction i using Fin.induction with
  | zero => exact finite_certificate.2.2.2.2.2.1.1.symm
  | succ i ih =>
    rw [forward, Fin.val_succ, Function.iterate_succ_apply']
    change Matrix.vecMul (forward T initial i.val) T = W i.succ
    change forward T initial i.val = W i.castSucc at ih
    rw [ih]
    exact (finite_certificate.2.2.2.2.2.1.2 i).symm

private theorem polynomial_relation :
    forward T initial (2 + 8) =
      ∑ j : Fin 8, (![-656100, 1574640, -1513404, 750384, -206469, 31428, -2466, 84] j : ℤ) • forward T initial (2 + j.val) := by
  rw [powers_table ⟨10, by omega⟩]
  simp_rw [show ∀ j : Fin 8, forward T initial (2 + j.val) = W ⟨2 + j.val, by omega⟩
    from fun j => powers_table ⟨2 + j.val, by omega⟩]
  exact finite_certificate.2.2.2.2.2.2

private theorem scale_count (n : ℕ) (hn : 1 ≤ n) :
    literalCount (q := 3) horizontal antidiagonal 1 n = 6 * a n := by
  classical
  let S : (Fin n × Fin 7 → Fin 3) → Prop := fun A =>
    defects horizontal antidiagonal (List.ofFn fun i j => A (i, j)) = 1
  have hinv : ∀ e : Equiv.Perm (Fin 3), ∀ A, S (e ∘ A) ↔ S A := by
    intro e A
    have hm : (List.ofFn fun i j => (e ∘ A) (i, j)) =
        (List.ofFn fun i j => A (i, j)).map (fun r => e ∘ r) := by
      rw [List.map_ofFn]
      rfl
    change defects horizontal antidiagonal _ = 1 ↔ _
    rw [hm, DefectTransfer.relabel_defects]
  have huse : ∀ A, S A → ∃ i j, A i ≠ A j := by
    intro A ha
    by_contra hh
    push_neg at hh
    let z : Fin n × Fin 7 := (⟨0, by omega⟩, 0)
    have he : A = fun _ => A z := funext fun i => hh i z
    change defects horizontal antidiagonal _ = 1 at ha
    rw [he] at ha
    simp only [List.ofFn_const] at ha
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    rw [DefectTransfer.constant_defects] at ha
    have hc : horizontal.card = 6 ∧ antidiagonal.card = 6 := by decide +kernel
    rw [hc.1, hc.2] at ha
    omega
  have h := @canonical_pattern_card (Fin n × Fin 7) inferInstance (cellOrder n) S hinv huse
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype, S] at h
  unfold literalCount a Normal
  convert h using 1
  apply congrArg (fun x : ℕ => 6 * x)
  apply congrArg Finset.card
  ext A
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

attribute [local irreducible] a

/-- Hardin's width-seven recurrence, valid from row count nine. -/
theorem result (n : ℕ) :
    (a (n + 9) : ℤ) = 84 * a (n + 8) - 2466 * a (n + 7) +
      31428 * a (n + 6) - 206469 * a (n + 5) + 750384 * a (n + 4) -
      1513404 * a (n + 3) + 1574640 * a (n + 2) - 656100 * a (n + 1) := by
  have bridge (m : ℕ) :
      dotProduct initial ((T ^ m).mulVec terminal) = 6 * (a (m + 1) : ℤ) := by
    rw [← count_transfer, scale_count (m + 1) (by omega)]
    push_cast
    rfl
  have table (i : Fin 11) :
      dotProduct (W i) terminal = 6 * (a (i.val + 1) : ℤ) := by
    rw [← powers_table i, DefectTransfer.forward_eq, ← Matrix.dotProduct_mulVec, bridge]
  have first (i : Fin 2) :
      dotProduct (W ⟨8 + i.val, by omega⟩) terminal =
        ∑ j : Fin 8, (![-656100, 1574640, -1513404, 750384, -206469, 31428, -2466, 84] j : ℤ) *
          dotProduct (W ⟨0 + i.val + j.val, by omega⟩) terminal := by
    revert i
    decide +kernel
  rcases n with _ | _ | n
  · have h := first 0
    simp_rw [table] at h
    norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_one, Fin.val_succ,
      Matrix.cons_val_zero, Matrix.cons_val_succ, Nat.add_assoc, Nat.add_zero] at h
    linarith
  · have h := first 1
    simp_rw [table] at h
    norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_one, Fin.val_succ,
      Matrix.cons_val_zero, Matrix.cons_val_succ, Nat.add_assoc, Nat.add_zero] at h
    linarith
  · have h := forward_shift T initial terminal 8 2 ![-656100, 1574640, -1513404, 750384, -206469, 31428, -2466, 84] polynomial_relation n
    simp_rw [bridge] at h
    norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_one, Fin.val_succ,
      Matrix.cons_val_zero, Matrix.cons_val_succ, Nat.add_assoc, Nat.add_zero] at h
    linarith

end D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.HardinA229585Strip
