/- GID: D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229691Strip
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/StripDefects/HardinA229691Strip
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229691Strip.result; premises=D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229691Strip.finite_certificate
   digest: Exact-budget transfer for Hardin's registered defective colourings. -/

/-
admission_basis: open-problem-resolution (#30838; Proved)
escape_witness: none (consumed bind-only helpers of the settlement on the live path of HardinA229691Strip.result)
a: proof_shape=bind-only; consumers=result
finite_certificate: proof_shape=bind-only; consumers=result
result: proof_shape=bind-only; consumers=none (external open-problem-resolution #30838)
-/

import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229691StripData
import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229691StripCertificate
import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229691StripClasses0
import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229691StripClasses1
import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229691StripClasses2
import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229691StripClasses3
import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229691StripClasses4
import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229691StripClasses5
import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229691StripClasses6
import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229691StripClasses7
import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229691StripClasses8
import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229691StripClasses9
import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229691StripClasses10
import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229691StripClasses11
import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229691StripClasses12
import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229691StripClasses13
import D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229583Strip
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical
import Mathlib.Logic.Equiv.Fin.Basic

/-! Literal row-major canonical counts and row transfer. -/
open scoped BigOperators
namespace D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229691Strip
open HardinA229583StripData (Row Boundary horizontal antidiagonal boundary cross)
open HardinA229691StripData
open DefectTransfer (bondDefects defects literalCount lumped_count forward forward_shift)
open D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical (Canonical canonical_pattern_card)

/-- Literal row-major canonical arrays at the exact defect budget. -/
def a (n : ℕ) : ℕ :=
  letI : DecidablePred (fun A : Fin n × Fin 5 → Fin 3 =>
    @Canonical (Fin n × Fin 5)
      (LinearOrder.lift' finProdFinEquiv finProdFinEquiv.injective).toLT 3 A) :=
    fun _ => by unfold Canonical; infer_instance
  (Finset.univ.filter fun A : Fin n × Fin 5 → Fin 3 =>
    defects horizontal antidiagonal (List.ofFn fun i j => A (i, j)) = 2 ∧
    (@Canonical (Fin n × Fin 5)
      (LinearOrder.lift' finProdFinEquiv finProdFinEquiv.injective).toLT 3 A)).card

theorem finite_certificate :
    (∀ p (d : Fin 3), Valid p d.val →
      terminal (cl p d.val) = (if d.val = 0 then 1 else 0)) ∧
    (∀ p (d : Fin 3), Valid p d.val → ∀ r : Row,
      cross p r + bondDefects horizontal r r ≤ d.val →
      Valid (boundary r) (d.val - (cross p r + bondDefects horizontal r r))) ∧
    (∀ p (d : Fin 3), Valid p d.val → ∀ s : Fin 27,
      (∑ r : Row, if cross p r + bondDefects horizontal r r ≤ d.val ∧
        cl (boundary r) (d.val - (cross p r + bondDefects horizontal r r)) = s
        then (1 : ℤ) else 0) = T (cl p d.val) s) ∧
    (∀ r : Row, bondDefects horizontal r r ≤ 2 →
      Valid (boundary r) (2 - bondDefects horizontal r r)) ∧
    (∀ s : Fin 27, (∑ r : Row, if bondDefects horizontal r r ≤ 2 ∧
      cl (boundary r) (2 - bondDefects horizontal r r) = s then (1 : ℤ) else 0) = initial s) ∧
    (W 0 = initial ∧ ∀ i : Fin 7, W i.succ = Matrix.vecMul (W i.castSucc) T) ∧
    W 7 = ∑ j : Fin 6, (![-5832, 14580, -13122, 4995, -729, 45] j : ℤ) • W ⟨1 + j.val, by omega⟩ := by
  refine ⟨HardinA229691StripCertificate.structural_certificate.1, HardinA229691StripCertificate.structural_certificate.2.1, ?_,
    HardinA229691StripCertificate.structural_certificate.2.2.1, HardinA229691StripCertificate.structural_certificate.2.2.2.1,
    HardinA229691StripCertificate.structural_certificate.2.2.2.2.1, HardinA229691StripCertificate.structural_certificate.2.2.2.2.2⟩
  intro p d h s
  by_cases h0 : s.val < 2
  · exact HardinA229691StripClasses0.transition_counts s ⟨by omega, h0⟩ p d h
  by_cases h1 : s.val < 4
  · exact HardinA229691StripClasses1.transition_counts s ⟨by omega, h1⟩ p d h
  by_cases h2 : s.val < 6
  · exact HardinA229691StripClasses2.transition_counts s ⟨by omega, h2⟩ p d h
  by_cases h3 : s.val < 8
  · exact HardinA229691StripClasses3.transition_counts s ⟨by omega, h3⟩ p d h
  by_cases h4 : s.val < 10
  · exact HardinA229691StripClasses4.transition_counts s ⟨by omega, h4⟩ p d h
  by_cases h5 : s.val < 12
  · exact HardinA229691StripClasses5.transition_counts s ⟨by omega, h5⟩ p d h
  by_cases h6 : s.val < 14
  · exact HardinA229691StripClasses6.transition_counts s ⟨by omega, h6⟩ p d h
  by_cases h7 : s.val < 16
  · exact HardinA229691StripClasses7.transition_counts s ⟨by omega, h7⟩ p d h
  by_cases h8 : s.val < 18
  · exact HardinA229691StripClasses8.transition_counts s ⟨by omega, h8⟩ p d h
  by_cases h9 : s.val < 20
  · exact HardinA229691StripClasses9.transition_counts s ⟨by omega, h9⟩ p d h
  by_cases h10 : s.val < 22
  · exact HardinA229691StripClasses10.transition_counts s ⟨by omega, h10⟩ p d h
  by_cases h11 : s.val < 24
  · exact HardinA229691StripClasses11.transition_counts s ⟨by omega, h11⟩ p d h
  by_cases h12 : s.val < 26
  · exact HardinA229691StripClasses12.transition_counts s ⟨by omega, h12⟩ p d h
  exact HardinA229691StripClasses13.transition_counts s ⟨by omega, s.isLt⟩ p d h

attribute [local irreducible] a T initial terminal W cl

/-- The registered recurrence at every index at least 8. -/
theorem result (n : ℕ) :
    (a (n + 8) : ℤ) = 45 * a (n + 7) - 729 * a (n + 6) + 4995 * a (n + 5) - 13122 * a (n + 4) + 14580 * a (n + 3) - 5832 * a (n + 2) := by
  have labelled (m : ℕ) :
      (literalCount (q := 3) horizontal antidiagonal 2 (m + 1) : ℤ) =
        dotProduct initial ((T ^ m).mulVec terminal) := by
    apply lumped_count horizontal antidiagonal boundary cross Valid cl T initial terminal 2
      HardinA229583Strip.edge
    · intro p d h
      exact finite_certificate.1 p ⟨d, by have hd : d ≤ 2 := h.1; omega⟩ h
    · intro p d h r hr
      exact finite_certificate.2.1 p ⟨d, by have hd : d ≤ 2 := h.1; omega⟩ h r hr
    · intro p d h s
      exact finite_certificate.2.2.1 p ⟨d, by have hd : d ≤ 2 := h.1; omega⟩ h s
    · exact finite_certificate.2.2.2.1
    · exact finite_certificate.2.2.2.2.1
  have tab (i : Fin 8) : forward T initial i.val = W i := by
    induction i using Fin.induction with
    | zero => exact finite_certificate.2.2.2.2.2.1.1.symm
    | succ i ih =>
      rw [forward, Fin.val_succ, Function.iterate_succ_apply']
      change Matrix.vecMul (forward T initial i.val) T = W i.succ
      change forward T initial i.val = W i.castSucc at ih
      rw [ih]
      exact (finite_certificate.2.2.2.2.2.1.2 i).symm
  have poly : forward T initial (1 + 6) =
      ∑ j : Fin 6, (![-5832, 14580, -13122, 4995, -729, 45] j : ℤ) • forward T initial (1 + j.val) := by
    rw [tab ⟨7, by omega⟩]
    simp_rw [show ∀ j : Fin 6, forward T initial (1 + j.val) = W ⟨1 + j.val, by omega⟩
      from fun j => tab ⟨1 + j.val, by omega⟩]
    exact finite_certificate.2.2.2.2.2.2
  have scale (m : ℕ) : literalCount (q := 3) horizontal antidiagonal 2 (m + 1) = 6 * a (m + 1) := by
    classical
    let S : (Fin (m + 1) × Fin 5 → Fin 3) → Prop := fun A =>
      defects horizontal antidiagonal (List.ofFn fun i j => A (i, j)) = 2
    have invariant : ∀ e : Equiv.Perm (Fin 3), ∀ A, S (e ∘ A) ↔ S A := by
      intro e A
      change defects horizontal antidiagonal _ = 2 ↔ _
      rw [show (List.ofFn fun i j => (e ∘ A) (i, j)) =
        (List.ofFn fun i j => A (i, j)).map (fun r => e ∘ r) by rw [List.map_ofFn]; rfl,
        DefectTransfer.relabel_defects]
    have nonconstant : ∀ A, S A → ∃ x y, A x ≠ A y := by
      intro A h
      by_contra he
      push_neg at he
      have const : A = fun _ => A (0, 0) := funext fun x => he x (0, 0)
      change defects horizontal antidiagonal _ = 2 at h
      rw [const] at h
      simp only [List.ofFn_const] at h
      rw [DefectTransfer.constant_defects] at h
      have cards : horizontal.card = 4 ∧ antidiagonal.card = 4 := by decide +kernel
      rw [cards.1, cards.2] at h
      omega
    have orbit := @canonical_pattern_card (Fin (m + 1) × Fin 5) inferInstance
      (LinearOrder.lift' finProdFinEquiv finProdFinEquiv.injective) S invariant nonconstant
    simp only [Nat.card_eq_fintype_card, Fintype.card_subtype] at orbit
    unfold literalCount a
    convert orbit using 1
    apply congrArg (fun x : ℕ => 6 * x)
    apply congrArg Finset.card
    ext A
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, S]
  have bridge (m : ℕ) :
      dotProduct initial ((T ^ m).mulVec terminal) = 6 * (a (m + 1) : ℤ) := by
    rw [← labelled, scale]
    push_cast
    rfl
  have h := forward_shift T initial terminal 6 1 ![-5832, 14580, -13122, 4995, -729, 45] poly n
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.val_one] at h
  have h1 := bridge (n + 1)
  have h2 := bridge (n + 2)
  have h3 := bridge (n + 3)
  have h4 := bridge (n + 4)
  have h5 := bridge (n + 5)
  have h6 := bridge (n + 6)
  have h7 := bridge (n + 7)
  simp only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] at h h1 h2 h3 h4 h5 h6 h7
  rw [h1, h2, h3, h4, h5, h6, h7] at h
  norm_num only [Nat.reduceAdd, zero_add] at h
  linarith

end D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229691Strip
