/- GID: D5/S3/StatisticalMechanics/Potts/StripDefectsTwo/HardinA229696Strip
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/StripDefectsTwo/HardinA229696Strip
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/StripDefectsTwo/HardinA229696Strip.result; premises=D5/S3/StatisticalMechanics/Potts/StripDefectsTwo/HardinA229696Strip.finite_certificate
   digest: Block extension for exact two-defect HA strip counts. -/

/-
admission_basis: open-problem-resolution (#31299; Proved)
escape_witness: none (consumed bind-only helpers of the settlement on the live path of HardinA229696Strip.result)
a: proof_shape=bind-only; consumers=result
finite_certificate: proof_shape=bind-only; consumers=result
result: proof_shape=bind-only; consumers=none (external open-problem-resolution #31299)
-/

import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229588Strip
import D5.S3.StatisticalMechanics.Potts.StripDefectsTwo.HardinA229696StripData
import D5.S3.StatisticalMechanics.Potts.StripDefectsTwo.HardinA229696StripCut
import D5.S3.StatisticalMechanics.Potts.StripDefectsTwo.HardinA229696StripCertificate
import D5.S3.StatisticalMechanics.Potts.StripDefectsTwo.HardinA229696StripForward
import D5.S3.StatisticalMechanics.Potts.StripDefectsTwo.HardinA229696StripClasses0
import D5.S3.StatisticalMechanics.Potts.StripDefectsTwo.HardinA229696StripClasses1
import D5.S3.StatisticalMechanics.Potts.StripDefectsTwo.HardinA229696StripClasses2
import D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical

open scoped BigOperators
open D5.S3.Combinatorics.TraceAvoidingArrays
open D5.S3.StatisticalMechanics.Potts.StripDefects
namespace D5.S3.StatisticalMechanics.Potts.StripDefectsTwo.HardinA229696Strip
open HardinA229588Strip (Row horizontal between)
open HardinA229696StripData
open DefectTransfer (bondDefects defects literalCount lumped_count forward forward_shift)
open HardinA233177Canonical (Canonical canonical_pattern_card)
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Literal row-major canonical arrays, with columns swept only to count bonds. -/
def a (n : ℕ) : ℕ :=
  letI : DecidablePred (fun A : Fin 3 × Fin n → Fin 3 =>
    @Canonical (Fin 3 × Fin n)
      (LinearOrder.lift' finProdFinEquiv finProdFinEquiv.injective).toLT 3 A) :=
    fun _ => by unfold Canonical; infer_instance
  (Finset.univ.filter fun A : Fin 3 × Fin n → Fin 3 =>
    defects horizontal between (List.ofFn fun j i => A (i, j)) = 2 ∧
    (@Canonical (Fin 3 × Fin n)
      (LinearOrder.lift' finProdFinEquiv finProdFinEquiv.injective).toLT 3 A)).card

theorem finite_certificate :
    (∀ p (d : Fin 3), Valid p d.val →
      terminal (cl p d.val) = (if d.val = 0 then 1 else 0)) ∧
    (∀ p (d : Fin 3), Valid p d.val → ∀ r : Row,
      bondDefects between p r + bondDefects horizontal r r ≤ d.val →
      Valid r (d.val - (bondDefects between p r + bondDefects horizontal r r))) ∧
    (∀ p (d : Fin 3), Valid p d.val → ∀ s : Fin 15,
      (∑ r : Row, if bondDefects between p r + bondDefects horizontal r r ≤ d.val ∧
        cl r (d.val - (bondDefects between p r + bondDefects horizontal r r)) = s
        then (1 : ℤ) else 0) = T (cl p d.val) s) ∧
    (∀ r : Row, bondDefects horizontal r r ≤ 2 → Valid r (2 - bondDefects horizontal r r)) ∧
    (∀ s : Fin 15, (∑ r : Row, if bondDefects horizontal r r ≤ 2 ∧
      cl r (2 - bondDefects horizontal r r) = s then (1 : ℤ) else 0) = initial s) ∧
    (W 0 = initial ∧ ∀ i : Fin 10, W i.succ = Matrix.vecMul (W i.castSucc) T) ∧
    W 10 = ∑ j : Fin 6, (![-8, 60, -162, 185, -81, 15] j : ℤ) • W ⟨4 + j.val, by omega⟩ := by
  refine ⟨HardinA229696StripCertificate.structural_certificate.1,
    HardinA229696StripCertificate.structural_certificate.2.1, ?_,
    HardinA229696StripCertificate.structural_certificate.2.2.1,
    HardinA229696StripCertificate.structural_certificate.2.2.2,
    HardinA229696StripForward.forward_certificate.1, HardinA229696StripForward.forward_certificate.2⟩
  intro p d hd s
  by_cases hs : s.val < 10
  · let j : Fin 10 := ⟨s.val, hs⟩
    have he : s = j.castAdd 5 := rfl
    rw [he]
    exact HardinA229696StripCut.leading_counts p d j
  · let j : Fin 5 := ⟨s.val - 10, by omega⟩
    have he : s = j.natAdd 10 := Fin.ext (by simp [j]; omega)
    rw [he]
    by_cases h2 : d.val = 2
    · have hd2 : d.val = 2 := h2
      simp only [hd2]
      by_cases hj0 : j.val < 2
      · exact HardinA229696StripClasses0.transition_counts j ⟨by omega, hj0⟩ p
      by_cases hj1 : j.val < 4
      · exact HardinA229696StripClasses1.transition_counts j ⟨by omega, hj1⟩ p
      exact HardinA229696StripClasses2.transition_counts j ⟨by omega, j.isLt⟩ p
    · exact HardinA229696StripCut.tail_counts p ⟨d.val, by omega⟩ j

attribute [local irreducible] a T initial terminal W cl

/-- The registered recurrence for every length at least 11. -/
theorem result (n : ℕ) :
    (a (n + 11) : ℤ) = 15 * a (n + 10) - 81 * a (n + 9) + 185 * a (n + 8) - 162 * a (n + 7) + 60 * a (n + 6) - 8 * a (n + 5) := by
  have labelled (m : ℕ) :
      (literalCount (q := 3) horizontal between 2 (m + 1) : ℤ) =
        dotProduct initial ((T ^ m).mulVec terminal) := by
    apply lumped_count horizontal between id (bondDefects between) Valid cl T initial terminal 2
      (fun _ _ => rfl)
    · intro p d h
      exact finite_certificate.1 p ⟨d, by change d ≤ 2 at h; omega⟩ h
    · intro p d h r hr
      exact finite_certificate.2.1 p ⟨d, by change d ≤ 2 at h; omega⟩ h r hr
    · intro p d h s
      exact finite_certificate.2.2.1 p ⟨d, by change d ≤ 2 at h; omega⟩ h s
    · exact finite_certificate.2.2.2.1
    · exact finite_certificate.2.2.2.2.1
  have tab (i : Fin 11) : forward T initial i.val = W i := by
    induction i using Fin.induction with
    | zero => exact finite_certificate.2.2.2.2.2.1.1.symm
    | succ i ih =>
      rw [forward, Fin.val_succ, Function.iterate_succ_apply']
      change Matrix.vecMul (forward T initial i.val) T = W i.succ
      change forward T initial i.val = W i.castSucc at ih
      rw [ih]
      exact (finite_certificate.2.2.2.2.2.1.2 i).symm
  have poly : forward T initial (4 + 6) =
      ∑ j : Fin 6, (![-8, 60, -162, 185, -81, 15] j : ℤ) • forward T initial (4 + j.val) := by
    rw [tab ⟨10, by omega⟩]
    simp_rw [show ∀ j : Fin 6, forward T initial (4 + j.val) = W ⟨4 + j.val, by omega⟩
      from fun j => tab ⟨4 + j.val, by omega⟩]
    exact finite_certificate.2.2.2.2.2.2
  have scale (m : ℕ) : literalCount (q := 3) horizontal between 2 (m + 1) = 6 * a (m + 1) := by
    classical
    let S : (Fin 3 × Fin (m + 1) → Fin 3) → Prop := fun A =>
      defects horizontal between (List.ofFn fun j i => A (i, j)) = 2
    have invariant : ∀ e : Equiv.Perm (Fin 3), ∀ A, S (e ∘ A) ↔ S A := by
      intro e A
      change defects horizontal between _ = 2 ↔ _
      rw [show (List.ofFn fun j i => (e ∘ A) (i, j)) =
        (List.ofFn fun j i => A (i, j)).map (fun r => e ∘ r) by rw [List.map_ofFn]; rfl,
        DefectTransfer.relabel_defects]
    have nonconstant : ∀ A, S A → ∃ x y, A x ≠ A y := by
      intro A h
      by_contra he
      push_neg at he
      have const : A = fun _ => A (0, 0) := funext fun x => he x (0, 0)
      change defects horizontal between _ = 2 at h
      rw [const] at h
      simp only [List.ofFn_const] at h
      rw [DefectTransfer.constant_defects] at h
      have cards : horizontal.card = 0 ∧ between.card = 5 := by decide +kernel
      rw [cards.1, cards.2] at h
      omega
    have orbit := @canonical_pattern_card (Fin 3 × Fin (m + 1)) inferInstance
      (LinearOrder.lift' finProdFinEquiv finProdFinEquiv.injective) S invariant nonconstant
    let e := Equiv.arrowCongr (Equiv.prodComm (Fin (m + 1)) (Fin 3)) (Equiv.refl (Fin 3))
    have card := Fintype.card_congr (e.subtypeEquiv (p := fun A =>
      defects horizontal between (List.ofFn fun i j => A (i, j)) = 2) (q := S) (fun _ => Iff.rfl))
    simp only [Nat.card_eq_fintype_card, Fintype.card_subtype] at orbit card
    unfold literalCount a
    convert card.trans orbit using 1
    apply congrArg (fun x : ℕ => 6 * x)
    apply congrArg Finset.card
    ext A
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, S]
  have bridge (m : ℕ) :
      dotProduct initial ((T ^ m).mulVec terminal) = 6 * (a (m + 1) : ℤ) := by
    rw [← labelled, scale]
    push_cast
    rfl
  have h := forward_shift T initial terminal 6 4 ![-8, 60, -162, 185, -81, 15] poly n
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.val_one] at h
  have h4 := bridge (n + 4)
  have h5 := bridge (n + 5)
  have h6 := bridge (n + 6)
  have h7 := bridge (n + 7)
  have h8 := bridge (n + 8)
  have h9 := bridge (n + 9)
  have h10 := bridge (n + 10)
  simp only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] at h h4 h5 h6 h7 h8 h9 h10
  rw [h4, h5, h6, h7, h8, h9, h10] at h
  norm_num only [Nat.reduceAdd, zero_add] at h
  linarith

end D5.S3.StatisticalMechanics.Potts.StripDefectsTwo.HardinA229696Strip
