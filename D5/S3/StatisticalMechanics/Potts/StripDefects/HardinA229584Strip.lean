/- GID: D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229584Strip
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/StripDefects/HardinA229584Strip
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229584Strip.result; premises=D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229584Strip.finite_certificate
   digest: The integer recurrence for one-defect normalized three-colour width-6 strips. -/

/-
admission_basis: open-problem-resolution (#30580; Proved)
escape_witness: none
class_relabel: proof_shape=bind-only; consumers=transition_counts
horizontal_relabel: proof_shape=bind-only; consumers=transition_counts
cross_relabel: proof_shape=bind-only; consumers=transition_counts
transition_counts: proof_shape=bind-only; consumers=finite_certificate
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
result: proof_shape=content; consumers=external sequence A229584
-/

import D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229584StripData
import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229584StripCertificate
import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229584StripClasses0
import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229584StripClasses1
import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229584StripClasses2
import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229584StripClasses3
import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229584StripClasses4
import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229584StripClasses5
import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229584StripClasses6
import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229584StripClasses7
import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229584StripClasses8
import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229584StripClasses9
import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229584StripClasses10
import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229584StripClasses11
import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229584StripClasses12
import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229584StripClasses13
import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229584StripClasses14
import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229584StripClasses15
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical
import Mathlib.Logic.Equiv.Fin.Basic

/-! Literal defective colourings and their finite boundary transfer. -/
open scoped BigOperators
namespace D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229584Strip
open DefectTransfer (bondDefects defects literalCount continuation lumped_count forward forward_shift)
open D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical (Canonical canonical_pattern_card)
open HardinA229584StripData

private abbrev cellOrder (n : ℕ) : LinearOrder (Fin n × Fin 6) :=
  LinearOrder.lift' finProdFinEquiv finProdFinEquiv.injective
private def Normal {n : ℕ} (A : Fin n × Fin 6 → Fin 3) : Prop :=
  @Canonical (Fin n × Fin 6) (cellOrder n).toLT 3 A
private instance decidableNormal {n : ℕ} (A : Fin n × Fin 6 → Fin 3) : Decidable (Normal A) := by
  unfold Normal Canonical
  change Decidable (∀ (i : Fin n × Fin 6) (b : Fin 3), b < A i →
    ∃ j : Fin n × Fin 6, finProdFinEquiv j < finProdFinEquiv i ∧ A j = b)
  infer_instance

/-- The finite filter ranges over every three-colour array of the indicated shape. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter fun A : Fin n × Fin 6 → Fin 3 =>
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
  simp only [cl, Function.comp_apply, e.injective.eq_iff]

private theorem horizontal_relabel (e : Equiv.Perm (Fin 3)) (r : Row) :
    bondDefects horizontal (e ∘ r) (e ∘ r) = bondDefects horizontal r r := by
  simp only [bondDefects, Function.comp_apply, e.injective.eq_iff]

private theorem cross_relabel (e : Equiv.Perm (Fin 3)) (p : Boundary) (r : Row) :
    cross (e ∘ p) (e ∘ r) = cross p r := by
  unfold cross bondDefects
  apply congrArg Finset.card
  ext a
  by_cases ha : a ∈ antidiagonal
  · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
    simp only [Finset.mem_filter, Fin.cons_succ, Function.comp_apply, e.injective.eq_iff]
  · simp [ha]

private theorem transition_counts (p : Boundary) (d : Fin 2) (hp : Valid p d.val)
    (s : Fin 32) :
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
    by_cases h0 : s.val < 2
    · exact HardinA229584StripClasses0.transition_counts s ⟨by omega, h0⟩ p' d hv hnormal
    by_cases h1 : s.val < 4
    · exact HardinA229584StripClasses1.transition_counts s ⟨by omega, h1⟩ p' d hv hnormal
    by_cases h2 : s.val < 6
    · exact HardinA229584StripClasses2.transition_counts s ⟨by omega, h2⟩ p' d hv hnormal
    by_cases h3 : s.val < 8
    · exact HardinA229584StripClasses3.transition_counts s ⟨by omega, h3⟩ p' d hv hnormal
    by_cases h4 : s.val < 10
    · exact HardinA229584StripClasses4.transition_counts s ⟨by omega, h4⟩ p' d hv hnormal
    by_cases h5 : s.val < 12
    · exact HardinA229584StripClasses5.transition_counts s ⟨by omega, h5⟩ p' d hv hnormal
    by_cases h6 : s.val < 14
    · exact HardinA229584StripClasses6.transition_counts s ⟨by omega, h6⟩ p' d hv hnormal
    by_cases h7 : s.val < 16
    · exact HardinA229584StripClasses7.transition_counts s ⟨by omega, h7⟩ p' d hv hnormal
    by_cases h8 : s.val < 18
    · exact HardinA229584StripClasses8.transition_counts s ⟨by omega, h8⟩ p' d hv hnormal
    by_cases h9 : s.val < 20
    · exact HardinA229584StripClasses9.transition_counts s ⟨by omega, h9⟩ p' d hv hnormal
    by_cases h10 : s.val < 22
    · exact HardinA229584StripClasses10.transition_counts s ⟨by omega, h10⟩ p' d hv hnormal
    by_cases h11 : s.val < 24
    · exact HardinA229584StripClasses11.transition_counts s ⟨by omega, h11⟩ p' d hv hnormal
    by_cases h12 : s.val < 26
    · exact HardinA229584StripClasses12.transition_counts s ⟨by omega, h12⟩ p' d hv hnormal
    by_cases h13 : s.val < 28
    · exact HardinA229584StripClasses13.transition_counts s ⟨by omega, h13⟩ p' d hv hnormal
    by_cases h14 : s.val < 30
    · exact HardinA229584StripClasses14.transition_counts s ⟨by omega, h14⟩ p' d hv hnormal
    exact HardinA229584StripClasses15.transition_counts s ⟨by omega, s.isLt⟩ p' d hv hnormal
  rw [he] at hT
  let E : Row ≃ Row := Equiv.piCongrRight fun _ : Fin 6 => e
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
    (∀ p (d : Fin 2), Valid p d.val → ∀ s : Fin 32,
      (∑ r : Row, if cross p r + bondDefects horizontal r r ≤ d.val ∧
        cl (boundary r) (d.val - (cross p r + bondDefects horizontal r r)) = s
        then (1 : ℤ) else 0) = T (cl p d.val) s) ∧
    (∀ r : Row, bondDefects horizontal r r ≤ 1 →
      Valid (boundary r) (1 - bondDefects horizontal r r)) ∧
    (∀ s : Fin 32, (∑ r : Row, if bondDefects horizontal r r ≤ 1 ∧
      cl (boundary r) (1 - bondDefects horizontal r r) = s then (1 : ℤ) else 0) = initial s) ∧
    (W 0 = initial ∧ ∀ i : Fin 7, W i.succ = Matrix.vecMul (W i.castSucc) T) ∧
    W 7 = ∑ j : Fin 6, (![-6561, 14580, -12150, 4662, -805, 50] j : ℤ) • W ⟨1 + j.val, by omega⟩ := by
  obtain ⟨hz, hn, hi, hv, hw, hp⟩ := HardinA229584StripCertificate.structural_certificate
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

private theorem powers_table (i : Fin 8) : forward T initial i.val = W i := by
  induction i using Fin.induction with
  | zero => exact finite_certificate.2.2.2.2.2.1.1.symm
  | succ i ih =>
    rw [forward, Fin.val_succ, Function.iterate_succ_apply']
    change Matrix.vecMul (forward T initial i.val) T = W i.succ
    change forward T initial i.val = W i.castSucc at ih
    rw [ih]
    exact (finite_certificate.2.2.2.2.2.1.2 i).symm

private theorem polynomial_relation :
    forward T initial (1 + 6) =
      ∑ j : Fin 6, (![-6561, 14580, -12150, 4662, -805, 50] j : ℤ) • forward T initial (1 + j.val) := by
  rw [powers_table ⟨7, by omega⟩]
  simp_rw [show ∀ j : Fin 6, forward T initial (1 + j.val) = W ⟨1 + j.val, by omega⟩
    from fun j => powers_table ⟨1 + j.val, by omega⟩]
  exact finite_certificate.2.2.2.2.2.2

private theorem scale_count (n : ℕ) (hn : 1 ≤ n) :
    literalCount (q := 3) horizontal antidiagonal 1 n = 6 * a n := by
  classical
  let S : (Fin n × Fin 6 → Fin 3) → Prop := fun A =>
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
    let z : Fin n × Fin 6 := (⟨0, by omega⟩, 0)
    have he : A = fun _ => A z := funext fun i => hh i z
    change defects horizontal antidiagonal _ = 1 at ha
    rw [he] at ha
    simp only [List.ofFn_const] at ha
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    rw [DefectTransfer.constant_defects] at ha
    have hc : horizontal.card = 5 ∧ antidiagonal.card = 5 := by decide +kernel
    rw [hc.1, hc.2] at ha
    omega
  have h := @canonical_pattern_card (Fin n × Fin 6) inferInstance (cellOrder n) S hinv huse
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
    (a (n + 7) : ℤ) =  50 * a (n + 6) - 805 * a (n + 5) + 4662 * a (n + 4) - 12150 * a (n + 3) + 14580 * a (n + 2) - 6561 * a (n + 1) := by
  have bridge (m : ℕ) :
      dotProduct initial ((T ^ m).mulVec terminal) = 6 * (a (m + 1) : ℤ) := by
    rw [← count_transfer, scale_count (m + 1) (by omega)]
    push_cast
    rfl
  have table (i : Fin 8) :
      dotProduct (W i) terminal = 6 * (a (i.val + 1) : ℤ) := by
    rw [← powers_table i, DefectTransfer.forward_eq, ← Matrix.dotProduct_mulVec, bridge]
  have first (i : Fin 1) :
      dotProduct (W ⟨6 + i.val, by omega⟩) terminal =
        ∑ j : Fin 6, (![-6561, 14580, -12150, 4662, -805, 50] j : ℤ) *
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
    have h := forward_shift T initial terminal 6 1 ![-6561, 14580, -12150, 4662, -805, 50] polynomial_relation n
    simp_rw [bridge] at h
    norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ,
      Matrix.cons_val_zero, Matrix.cons_val_succ, Nat.add_assoc, Nat.add_zero] at h
    linarith

end D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229584Strip
