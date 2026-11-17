/- GID: D5/S3/StatisticalMechanics/Potts/StripDefectsTwo/HardinA229697Strip
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/StripDefectsTwo/HardinA229697Strip
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/StripDefectsTwo/HardinA229697Strip.result; premises=D5/S3/StatisticalMechanics/Potts/StripDefectsTwo/HardinA229697Strip.finite_certificate
   digest: Block extension for exact two-defect HA strip counts. -/

/-
admission_basis: open-problem-resolution (#31299; Proved)
escape_witness: none (consumed bind-only helpers of the settlement on the live path of HardinA229697Strip.result)
a: proof_shape=bind-only; consumers=result
finite_certificate: proof_shape=bind-only; consumers=result
result: proof_shape=bind-only; consumers=none (external open-problem-resolution #31299)
-/

import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229589StripData
import D5.S3.StatisticalMechanics.Potts.StripDefectsTwo.HardinA229697StripData
import D5.S3.StatisticalMechanics.Potts.StripDefectsTwo.HardinA229697StripCut
import D5.S3.StatisticalMechanics.Potts.StripDefectsTwo.HardinA229697StripCertificate
import D5.S3.StatisticalMechanics.Potts.StripDefectsTwo.HardinA229697StripForward
import D5.S3.StatisticalMechanics.Potts.StripDefectsTwo.HardinA229697StripClasses0
import D5.S3.StatisticalMechanics.Potts.StripDefectsTwo.HardinA229697StripClasses1
import D5.S3.StatisticalMechanics.Potts.StripDefectsTwo.HardinA229697StripClasses2
import D5.S3.StatisticalMechanics.Potts.StripDefectsTwo.HardinA229697StripClasses3
import D5.S3.StatisticalMechanics.Potts.StripDefectsTwo.HardinA229697StripClasses4
import D5.S3.StatisticalMechanics.Potts.StripDefectsTwo.HardinA229697StripClasses5
import D5.S3.StatisticalMechanics.Potts.StripDefectsTwo.HardinA229697StripClasses6
import D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical

open scoped BigOperators
open D5.S3.Combinatorics.TraceAvoidingArrays
open D5.S3.StatisticalMechanics.Potts.StripDefects
namespace D5.S3.StatisticalMechanics.Potts.StripDefectsTwo.HardinA229697Strip
open HardinA229589StripData (Row horizontal between)
open HardinA229697StripData
open DefectTransfer (bondDefects defects literalCount lumped_count forward forward_shift)
open HardinA233177Canonical (Canonical canonical_pattern_card)
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Literal row-major canonical arrays, with columns swept only to count bonds. -/
def a (n : ℕ) : ℕ :=
  letI : DecidablePred (fun A : Fin 4 × Fin n → Fin 3 =>
    @Canonical (Fin 4 × Fin n)
      (LinearOrder.lift' finProdFinEquiv finProdFinEquiv.injective).toLT 3 A) :=
    fun _ => by unfold Canonical; infer_instance
  (Finset.univ.filter fun A : Fin 4 × Fin n → Fin 3 =>
    defects horizontal between (List.ofFn fun j i => A (i, j)) = 2 ∧
    (@Canonical (Fin 4 × Fin n)
      (LinearOrder.lift' finProdFinEquiv finProdFinEquiv.injective).toLT 3 A)).card

theorem finite_certificate :
    (∀ p (d : Fin 3), Valid p d.val →
      terminal (cl p d.val) = (if d.val = 0 then 1 else 0)) ∧
    (∀ p (d : Fin 3), Valid p d.val → ∀ r : Row,
      bondDefects between p r + bondDefects horizontal r r ≤ d.val →
      Valid r (d.val - (bondDefects between p r + bondDefects horizontal r r))) ∧
    (∀ p (d : Fin 3), Valid p d.val → ∀ s : Fin 42,
      (∑ r : Row, if bondDefects between p r + bondDefects horizontal r r ≤ d.val ∧
        cl r (d.val - (bondDefects between p r + bondDefects horizontal r r)) = s
        then (1 : ℤ) else 0) = T (cl p d.val) s) ∧
    (∀ r : Row, bondDefects horizontal r r ≤ 2 → Valid r (2 - bondDefects horizontal r r)) ∧
    (∀ s : Fin 42, (∑ r : Row, if bondDefects horizontal r r ≤ 2 ∧
      cl r (2 - bondDefects horizontal r r) = s then (1 : ℤ) else 0) = initial s) ∧
    (W 0 = initial ∧ ∀ i : Fin 17, W i.succ = Matrix.vecMul (W i.castSucc) T) ∧
    W 17 = ∑ j : Fin 9, (![216, -1620, 5022, -8343, 8073, -4644, 1557, -288, 27] j : ℤ) • W ⟨8 + j.val, by omega⟩ := by
  refine ⟨HardinA229697StripCertificate.structural_certificate.1,
    HardinA229697StripCertificate.structural_certificate.2.1, ?_,
    HardinA229697StripCertificate.structural_certificate.2.2.1,
    HardinA229697StripCertificate.structural_certificate.2.2.2,
    HardinA229697StripForward.forward_certificate.1, HardinA229697StripForward.forward_certificate.2⟩
  intro p d hd s
  by_cases hs : s.val < 28
  · let j : Fin 28 := ⟨s.val, hs⟩
    have he : s = j.castAdd 14 := rfl
    rw [he]
    exact HardinA229697StripCut.leading_counts p d j
  · let j : Fin 14 := ⟨s.val - 28, by omega⟩
    have he : s = j.natAdd 28 := Fin.ext (by simp [j]; omega)
    rw [he]
    by_cases h2 : d.val = 2
    · have hd2 : d.val = 2 := h2
      simp only [hd2]
      by_cases hj0 : j.val < 2
      · exact HardinA229697StripClasses0.transition_counts j ⟨by omega, hj0⟩ p
      by_cases hj1 : j.val < 4
      · exact HardinA229697StripClasses1.transition_counts j ⟨by omega, hj1⟩ p
      by_cases hj2 : j.val < 6
      · exact HardinA229697StripClasses2.transition_counts j ⟨by omega, hj2⟩ p
      by_cases hj3 : j.val < 8
      · exact HardinA229697StripClasses3.transition_counts j ⟨by omega, hj3⟩ p
      by_cases hj4 : j.val < 10
      · exact HardinA229697StripClasses4.transition_counts j ⟨by omega, hj4⟩ p
      by_cases hj5 : j.val < 12
      · exact HardinA229697StripClasses5.transition_counts j ⟨by omega, hj5⟩ p
      exact HardinA229697StripClasses6.transition_counts j ⟨by omega, j.isLt⟩ p
    · exact HardinA229697StripCut.tail_counts p ⟨d.val, by omega⟩ j

attribute [local irreducible] a T initial terminal W cl

/-- The registered recurrence for every length at least 18. -/
theorem result (n : ℕ) :
    (a (n + 18) : ℤ) = 27 * a (n + 17) - 288 * a (n + 16) + 1557 * a (n + 15) - 4644 * a (n + 14) + 8073 * a (n + 13) - 8343 * a (n + 12) + 5022 * a (n + 11) - 1620 * a (n + 10) + 216 * a (n + 9) := by
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
  have tab (i : Fin 18) : forward T initial i.val = W i := by
    induction i using Fin.induction with
    | zero => exact finite_certificate.2.2.2.2.2.1.1.symm
    | succ i ih =>
      rw [forward, Fin.val_succ, Function.iterate_succ_apply']
      change Matrix.vecMul (forward T initial i.val) T = W i.succ
      change forward T initial i.val = W i.castSucc at ih
      rw [ih]
      exact (finite_certificate.2.2.2.2.2.1.2 i).symm
  have poly : forward T initial (8 + 9) =
      ∑ j : Fin 9, (![216, -1620, 5022, -8343, 8073, -4644, 1557, -288, 27] j : ℤ) • forward T initial (8 + j.val) := by
    rw [tab ⟨17, by omega⟩]
    simp_rw [show ∀ j : Fin 9, forward T initial (8 + j.val) = W ⟨8 + j.val, by omega⟩
      from fun j => tab ⟨8 + j.val, by omega⟩]
    exact finite_certificate.2.2.2.2.2.2
  have scale (m : ℕ) : literalCount (q := 3) horizontal between 2 (m + 1) = 6 * a (m + 1) := by
    classical
    let S : (Fin 4 × Fin (m + 1) → Fin 3) → Prop := fun A =>
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
      have cards : horizontal.card = 0 ∧ between.card = 7 := by decide +kernel
      rw [cards.1, cards.2] at h
      omega
    have orbit := @canonical_pattern_card (Fin 4 × Fin (m + 1)) inferInstance
      (LinearOrder.lift' finProdFinEquiv finProdFinEquiv.injective) S invariant nonconstant
    let e := Equiv.arrowCongr (Equiv.prodComm (Fin (m + 1)) (Fin 4)) (Equiv.refl (Fin 3))
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
  have h := forward_shift T initial terminal 9 8 ![216, -1620, 5022, -8343, 8073, -4644, 1557, -288, 27] poly n
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.val_one] at h
  have h8 := bridge (n + 8)
  have h9 := bridge (n + 9)
  have h10 := bridge (n + 10)
  have h11 := bridge (n + 11)
  have h12 := bridge (n + 12)
  have h13 := bridge (n + 13)
  have h14 := bridge (n + 14)
  have h15 := bridge (n + 15)
  have h16 := bridge (n + 16)
  have h17 := bridge (n + 17)
  simp only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] at h h8 h9 h10 h11 h12 h13 h14 h15 h16 h17
  rw [h8, h9, h10, h11, h12, h13, h14, h15, h16, h17] at h
  norm_num only [Nat.reduceAdd, zero_add] at h
  linarith

end D5.S3.StatisticalMechanics.Potts.StripDefectsTwo.HardinA229697Strip
