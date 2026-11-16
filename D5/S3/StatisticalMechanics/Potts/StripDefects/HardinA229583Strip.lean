/- GID: D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229583Strip
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/StripDefects/HardinA229583Strip
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229583Strip.result; premises=D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229583Strip.finite_certificate
   digest: The integer recurrence for one-defect normalized three-colour width-5 strips. -/

/-
admission_basis: open-problem-resolution (#30580; Proved)
escape_witness: none
cellOrder: proof_shape=bind-only; consumers=Normal, scale_count
Normal: proof_shape=bind-only; consumers=a, scale_count
decidableNormal: proof_shape=bind-only; consumers=a
a: proof_shape=bind-only; consumers=result
edge: proof_shape=bind-only; consumers=count_transfer
finite_certificate: proof_shape=bind-only; consumers=count_transfer, powers_table, polynomial_relation
count_transfer: proof_shape=content; consumers=result
powers_table: proof_shape=bind-only; consumers=polynomial_relation
polynomial_relation: proof_shape=bind-only; consumers=result
scale_count: proof_shape=bind-only; consumers=result
result: proof_shape=content; consumers=external sequence A229583
-/

import D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229583StripData
import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229583StripCertificate
import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229583StripClasses0
import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229583StripClasses1
import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229583StripClasses2
import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229583StripClasses3
import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229583StripClasses4
import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229583StripClasses5
import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229583StripClasses6
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical
import Mathlib.Logic.Equiv.Fin.Basic

/-! Literal defective colourings and their finite boundary transfer. -/
open scoped BigOperators
namespace D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229583Strip
open DefectTransfer (bondDefects defects literalCount continuation lumped_count forward forward_shift)
open D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical (Canonical canonical_pattern_card)
open HardinA229583StripData

private abbrev cellOrder (n : ℕ) : LinearOrder (Fin n × Fin 5) :=
  LinearOrder.lift' finProdFinEquiv finProdFinEquiv.injective
private def Normal {n : ℕ} (A : Fin n × Fin 5 → Fin 3) : Prop :=
  @Canonical (Fin n × Fin 5) (cellOrder n).toLT 3 A
private instance decidableNormal {n : ℕ} (A : Fin n × Fin 5 → Fin 3) : Decidable (Normal A) := by
  unfold Normal Canonical
  change Decidable (∀ (i : Fin n × Fin 5) (b : Fin 3), b < A i →
    ∃ j : Fin n × Fin 5, finProdFinEquiv j < finProdFinEquiv i ∧ A j = b)
  infer_instance

/-- The finite filter ranges over every three-colour array of the indicated shape. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter fun A : Fin n × Fin 5 → Fin 3 =>
    defects horizontal antidiagonal (List.ofFn fun i j => A (i, j)) = 1 ∧ Normal A).card

theorem edge (r t : Row) : bondDefects antidiagonal r t = cross (boundary r) t := by
  unfold cross bondDefects
  apply congrArg Finset.card
  ext e
  by_cases he : e ∈ antidiagonal
  · obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp he
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
    rfl
  · simp [he]

/-- Counts, budget preservation and the integer polynomial certificate. -/
theorem finite_certificate :
    (∀ p (d : Fin 2), Valid p d.val →
      terminal (cl p d.val) = (if d.val = 0 then 1 else 0)) ∧
    (∀ p (d : Fin 2), Valid p d.val → ∀ r : Row,
      cross p r + bondDefects horizontal r r ≤ d.val →
      Valid (boundary r) (d.val - (cross p r + bondDefects horizontal r r))) ∧
    (∀ p (d : Fin 2), Valid p d.val → ∀ s : Fin 14,
      (∑ r : Row, if cross p r + bondDefects horizontal r r ≤ d.val ∧
        cl (boundary r) (d.val - (cross p r + bondDefects horizontal r r)) = s
        then (1 : ℤ) else 0) = T (cl p d.val) s) ∧
    (∀ r : Row, bondDefects horizontal r r ≤ 1 →
      Valid (boundary r) (1 - bondDefects horizontal r r)) ∧
    (∀ s : Fin 14, (∑ r : Row, if bondDefects horizontal r r ≤ 1 ∧
      cl (boundary r) (1 - bondDefects horizontal r r) = s then (1 : ℤ) else 0) = initial s) ∧
    (W 0 = initial ∧ ∀ i : Fin 5, W i.succ = Matrix.vecMul (W i.castSucc) T) ∧
    W 5 = ∑ j : Fin 4, (![-324, 540, -261, 30] j : ℤ) • W ⟨1 + j.val, by omega⟩ := by
  obtain ⟨hz, hn, hi, hv, hw, hp⟩ := HardinA229583StripCertificate.structural_certificate
  refine ⟨hz, hn, ?_, hi, hv, hw, hp⟩
  intro p d h s
  by_cases h0 : s.val < 2
  · exact HardinA229583StripClasses0.transition_counts s ⟨by omega, h0⟩ p d h
  by_cases h1 : s.val < 4
  · exact HardinA229583StripClasses1.transition_counts s ⟨by omega, h1⟩ p d h
  by_cases h2 : s.val < 6
  · exact HardinA229583StripClasses2.transition_counts s ⟨by omega, h2⟩ p d h
  by_cases h3 : s.val < 8
  · exact HardinA229583StripClasses3.transition_counts s ⟨by omega, h3⟩ p d h
  by_cases h4 : s.val < 10
  · exact HardinA229583StripClasses4.transition_counts s ⟨by omega, h4⟩ p d h
  by_cases h5 : s.val < 12
  · exact HardinA229583StripClasses5.transition_counts s ⟨by omega, h5⟩ p d h
  exact HardinA229583StripClasses6.transition_counts s ⟨by omega, s.isLt⟩ p d h

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

private theorem powers_table (i : Fin 6) : forward T initial i.val = W i := by
  induction i using Fin.induction with
  | zero => exact finite_certificate.2.2.2.2.2.1.1.symm
  | succ i ih =>
    rw [forward, Fin.val_succ, Function.iterate_succ_apply']
    change Matrix.vecMul (forward T initial i.val) T = W i.succ
    change forward T initial i.val = W i.castSucc at ih
    rw [ih]
    exact (finite_certificate.2.2.2.2.2.1.2 i).symm

private theorem polynomial_relation :
    forward T initial (1 + 4) =
      ∑ j : Fin 4, (![-324, 540, -261, 30] j : ℤ) • forward T initial (1 + j.val) := by
  rw [powers_table ⟨5, by omega⟩]
  simp_rw [show ∀ j : Fin 4, forward T initial (1 + j.val) = W ⟨1 + j.val, by omega⟩
    from fun j => powers_table ⟨1 + j.val, by omega⟩]
  exact finite_certificate.2.2.2.2.2.2

private theorem scale_count (n : ℕ) (hn : 1 ≤ n) :
    literalCount (q := 3) horizontal antidiagonal 1 n = 6 * a n := by
  classical
  let S : (Fin n × Fin 5 → Fin 3) → Prop := fun A =>
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
    let z : Fin n × Fin 5 := (⟨0, by omega⟩, 0)
    have he : A = fun _ => A z := funext fun i => hh i z
    change defects horizontal antidiagonal _ = 1 at ha
    rw [he] at ha
    simp only [List.ofFn_const] at ha
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    rw [DefectTransfer.constant_defects] at ha
    have hc : horizontal.card = 4 ∧ antidiagonal.card = 4 := by decide +kernel
    rw [hc.1, hc.2] at ha
    omega
  have h := @canonical_pattern_card (Fin n × Fin 5) inferInstance (cellOrder n) S hinv huse
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype, S] at h
  unfold literalCount a Normal
  convert h using 1
  apply congrArg (fun x : ℕ => 6 * x)
  apply congrArg Finset.card
  ext A
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

attribute [local irreducible] a

/-- Hardin's registered recurrence, with its explicit starting shift. -/
theorem result (n : ℕ) :
    (a (n + 5) : ℤ) =  30 * a (n + 4) - 261 * a (n + 3) + 540 * a (n + 2) - 324 * a (n + 1) := by
  have bridge (m : ℕ) :
      dotProduct initial ((T ^ m).mulVec terminal) = 6 * (a (m + 1) : ℤ) := by
    rw [← count_transfer, scale_count (m + 1) (by omega)]
    push_cast
    rfl
  have table (i : Fin 6) :
      dotProduct (W i) terminal = 6 * (a (i.val + 1) : ℤ) := by
    rw [← powers_table i, DefectTransfer.forward_eq, ← Matrix.dotProduct_mulVec, bridge]
  have first (i : Fin 1) :
      dotProduct (W ⟨4 + i.val, by omega⟩) terminal =
        ∑ j : Fin 4, (![-324, 540, -261, 30] j : ℤ) *
          dotProduct (W ⟨0 + i.val + j.val, by omega⟩) terminal := by
    revert i
    decide +kernel
  cases n with
  | zero =>
    have h := first 0
    simp_rw [table] at h
    norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ,
      Matrix.cons_val_zero, Matrix.cons_val_succ, Nat.add_assoc, Nat.add_zero] at h
    linarith
  | succ n =>
    have h := forward_shift T initial terminal 4 1 ![-324, 540, -261, 30] polynomial_relation n
    simp_rw [bridge] at h
    norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ,
      Matrix.cons_val_zero, Matrix.cons_val_succ, Nat.add_assoc, Nat.add_zero] at h
    linarith

end D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229583Strip
