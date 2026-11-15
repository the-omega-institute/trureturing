/- GID: D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229589Strip
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/StripDefects/HardinA229589Strip
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229589Strip.result; premises=D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229589Strip.finite_certificate
   digest: Exact-budget transfer for Hardin's registered defective colourings. -/

/-
admission_basis: open-problem-resolution (#30838; Proved)
escape_witness: none (consumed bind-only helpers of the settlement on the live path of HardinA229589Strip.result)
a: proof_shape=bind-only; consumers=result
finite_certificate: proof_shape=bind-only; consumers=result
result: proof_shape=bind-only; consumers=none (external open-problem-resolution #30838)
-/

import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229589StripData
import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229589StripCertificate
import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229589StripClasses0
import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229589StripClasses1
import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229589StripClasses2
import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229589StripClasses3
import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229589StripClasses4
import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229589StripClasses5
import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229589StripClasses6
import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229589StripClasses7
import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229589StripClasses8
import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229589StripClasses9
import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229589StripClasses10
import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229589StripClasses11
import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229589StripClasses12
import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229589StripClasses13
import D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical
import Mathlib.Logic.Equiv.Fin.Basic

/-! Literal row-major canonical counts and column transfer. -/
open scoped BigOperators
namespace D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229589Strip
open HardinA229589StripData
open DefectTransfer (bondDefects defects literalCount lumped_count forward forward_shift)
open D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical (Canonical canonical_pattern_card)

/-- Literal row-major canonical arrays, with columns swept only to count bonds. -/
def a (n : ℕ) : ℕ :=
  letI : DecidablePred (fun A : Fin 4 × Fin n → Fin 3 =>
    @Canonical (Fin 4 × Fin n)
      (LinearOrder.lift' finProdFinEquiv finProdFinEquiv.injective).toLT 3 A) :=
    fun _ => by unfold Canonical; infer_instance
  (Finset.univ.filter fun A : Fin 4 × Fin n → Fin 3 =>
    defects horizontal between (List.ofFn fun j i => A (i, j)) = 1 ∧
    (@Canonical (Fin 4 × Fin n)
      (LinearOrder.lift' finProdFinEquiv finProdFinEquiv.injective).toLT 3 A)).card

theorem finite_certificate :
    (∀ p (d : Fin 2), Valid p d.val →
      terminal (cl p d.val) = (if d.val = 0 then 1 else 0)) ∧
    (∀ p (d : Fin 2), Valid p d.val → ∀ r : Row,
      bondDefects between p r + bondDefects horizontal r r ≤ d.val →
      Valid r (d.val - (bondDefects between p r + bondDefects horizontal r r))) ∧
    (∀ p (d : Fin 2), Valid p d.val → ∀ s : Fin 28,
      (∑ r : Row, if bondDefects between p r + bondDefects horizontal r r ≤ d.val ∧
        cl r (d.val - (bondDefects between p r + bondDefects horizontal r r)) = s
        then (1 : ℤ) else 0) = T (cl p d.val) s) ∧
    (∀ r : Row, bondDefects horizontal r r ≤ 1 →
      Valid r (1 - bondDefects horizontal r r)) ∧
    (∀ s : Fin 28, (∑ r : Row, if bondDefects horizontal r r ≤ 1 ∧
      cl r (1 - bondDefects horizontal r r) = s then (1 : ℤ) else 0) = initial s) ∧
    (W 0 = initial ∧ ∀ i : Fin 12, W i.succ = Matrix.vecMul (W i.castSucc) T) ∧
    W 12 = ∑ j : Fin 6, (![-36, 180, -333, 282, -111, 18] j : ℤ) • W ⟨6 + j.val, by omega⟩ := by
  refine ⟨HardinA229589StripCertificate.structural_certificate.1, HardinA229589StripCertificate.structural_certificate.2.1, ?_,
    HardinA229589StripCertificate.structural_certificate.2.2.1, HardinA229589StripCertificate.structural_certificate.2.2.2.1,
    HardinA229589StripCertificate.structural_certificate.2.2.2.2.1, HardinA229589StripCertificate.structural_certificate.2.2.2.2.2⟩
  intro p d h s
  by_cases h0 : s.val < 2
  · exact HardinA229589StripClasses0.transition_counts s ⟨by omega, h0⟩ p d h
  by_cases h1 : s.val < 4
  · exact HardinA229589StripClasses1.transition_counts s ⟨by omega, h1⟩ p d h
  by_cases h2 : s.val < 6
  · exact HardinA229589StripClasses2.transition_counts s ⟨by omega, h2⟩ p d h
  by_cases h3 : s.val < 8
  · exact HardinA229589StripClasses3.transition_counts s ⟨by omega, h3⟩ p d h
  by_cases h4 : s.val < 10
  · exact HardinA229589StripClasses4.transition_counts s ⟨by omega, h4⟩ p d h
  by_cases h5 : s.val < 12
  · exact HardinA229589StripClasses5.transition_counts s ⟨by omega, h5⟩ p d h
  by_cases h6 : s.val < 14
  · exact HardinA229589StripClasses6.transition_counts s ⟨by omega, h6⟩ p d h
  by_cases h7 : s.val < 16
  · exact HardinA229589StripClasses7.transition_counts s ⟨by omega, h7⟩ p d h
  by_cases h8 : s.val < 18
  · exact HardinA229589StripClasses8.transition_counts s ⟨by omega, h8⟩ p d h
  by_cases h9 : s.val < 20
  · exact HardinA229589StripClasses9.transition_counts s ⟨by omega, h9⟩ p d h
  by_cases h10 : s.val < 22
  · exact HardinA229589StripClasses10.transition_counts s ⟨by omega, h10⟩ p d h
  by_cases h11 : s.val < 24
  · exact HardinA229589StripClasses11.transition_counts s ⟨by omega, h11⟩ p d h
  by_cases h12 : s.val < 26
  · exact HardinA229589StripClasses12.transition_counts s ⟨by omega, h12⟩ p d h
  exact HardinA229589StripClasses13.transition_counts s ⟨by omega, s.isLt⟩ p d h

attribute [local irreducible] a T initial terminal W cl

/-- The registered recurrence at every index at least 13. -/
theorem result (n : ℕ) :
    (a (n + 13) : ℤ) = 18 * a (n + 12) - 111 * a (n + 11) + 282 * a (n + 10) - 333 * a (n + 9) + 180 * a (n + 8) - 36 * a (n + 7) := by
  have labelled (m : ℕ) :
      (literalCount (q := 3) horizontal between 1 (m + 1) : ℤ) =
        dotProduct initial ((T ^ m).mulVec terminal) := by
    apply lumped_count horizontal between id (bondDefects between) Valid cl T initial terminal 1
      (fun _ _ => rfl)
    · intro p d h
      exact finite_certificate.1 p ⟨d, by change d ≤ 1 at h; omega⟩ h
    · intro p d h r hr
      exact finite_certificate.2.1 p ⟨d, by change d ≤ 1 at h; omega⟩ h r hr
    · intro p d h s
      exact finite_certificate.2.2.1 p ⟨d, by change d ≤ 1 at h; omega⟩ h s
    · exact finite_certificate.2.2.2.1
    · exact finite_certificate.2.2.2.2.1
  have tab (i : Fin 13) : forward T initial i.val = W i := by
    induction i using Fin.induction with
    | zero => exact finite_certificate.2.2.2.2.2.1.1.symm
    | succ i ih =>
      rw [forward, Fin.val_succ, Function.iterate_succ_apply']
      change Matrix.vecMul (forward T initial i.val) T = W i.succ
      change forward T initial i.val = W i.castSucc at ih
      rw [ih]
      exact (finite_certificate.2.2.2.2.2.1.2 i).symm
  have poly : forward T initial (6 + 6) =
      ∑ j : Fin 6, (![-36, 180, -333, 282, -111, 18] j : ℤ) • forward T initial (6 + j.val) := by
    rw [tab ⟨12, by omega⟩]
    simp_rw [show ∀ j : Fin 6, forward T initial (6 + j.val) = W ⟨6 + j.val, by omega⟩
      from fun j => tab ⟨6 + j.val, by omega⟩]
    exact finite_certificate.2.2.2.2.2.2
  have scale (m : ℕ) : literalCount (q := 3) horizontal between 1 (m + 1) = 6 * a (m + 1) := by
    classical
    let S : (Fin 4 × Fin (m + 1) → Fin 3) → Prop := fun A =>
      defects horizontal between (List.ofFn fun j i => A (i, j)) = 1
    have invariant : ∀ e : Equiv.Perm (Fin 3), ∀ A, S (e ∘ A) ↔ S A := by
      intro e A
      change defects horizontal between _ = 1 ↔ _
      rw [show (List.ofFn fun j i => (e ∘ A) (i, j)) =
        (List.ofFn fun j i => A (i, j)).map (fun r => e ∘ r) by rw [List.map_ofFn]; rfl,
        DefectTransfer.relabel_defects]
    have nonconstant : ∀ A, S A → ∃ x y, A x ≠ A y := by
      intro A h
      by_contra he
      push_neg at he
      have const : A = fun _ => A (0, 0) := funext fun x => he x (0, 0)
      change defects horizontal between _ = 1 at h
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
      defects horizontal between (List.ofFn fun i j => A (i, j)) = 1) (q := S) (fun _ => Iff.rfl))
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
  have h := forward_shift T initial terminal 6 6 ![-36, 180, -333, 282, -111, 18] poly n
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.val_one] at h
  have h6 := bridge (n + 6)
  have h7 := bridge (n + 7)
  have h8 := bridge (n + 8)
  have h9 := bridge (n + 9)
  have h10 := bridge (n + 10)
  have h11 := bridge (n + 11)
  have h12 := bridge (n + 12)
  simp only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] at h h6 h7 h8 h9 h10 h11 h12
  rw [h6, h7, h8, h9, h10, h11, h12] at h
  norm_num only [Nat.reduceAdd, zero_add] at h
  linarith

end D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229589Strip
