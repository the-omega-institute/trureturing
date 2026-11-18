/- GID: D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P4a/HardinA229537Strip
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P4a/HardinA229537Strip
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P4a/HardinA229537Strip.result; premises=D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P4a/HardinA229537StripCertificate.finite_certificate
   digest: Hardin's order-twelve recurrence for literal one-defect four-row HDA arrays. -/

/-
admission_basis: open-problem-resolution (#31548; Proved)
escape_witness: none (consumed bind-only helpers of the settlement on the live path of result)
a: proof_shape=bind-only; consumers=result
result: proof_shape=bind-only; consumers=none (external open-problem-resolution #31548)
-/

import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177PairTransfer
import D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P4a.HardinA229537StripData
import D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P4a.HardinA229537StripCertificate
import D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical
import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229589StripCertificate
import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229589StripData
import Mathlib.Logic.Equiv.Fin.Basic

open scoped BigOperators
namespace D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P4a.HardinA229537Strip
open D5.S3.StatisticalMechanics.Potts.StripDefects
open D5.S3.Combinatorics.TraceAvoidingArrays
open HardinA229537StripData
open DefectTransfer (bondDefects defects literalCount lumped_count)
open HardinA233177Canonical (Canonical canonical_pattern_card)
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

/-- The literal row-major canonical filtered array count. -/
def a (n : ℕ) : ℕ :=
  letI : DecidablePred (fun A : Fin 4 × Fin n → Fin 3 =>
    @Canonical (Fin 4 × Fin n)
      (LinearOrder.lift' finProdFinEquiv finProdFinEquiv.injective).toLT 3 A) :=
    fun _ => by unfold Canonical; infer_instance
  (Finset.univ.filter fun A : Fin 4 × Fin n → Fin 3 =>
    defects horizontal between (List.ofFn fun j i => A (i, j)) = 1 ∧
    (@Canonical (Fin 4 × Fin n)
      (LinearOrder.lift' finProdFinEquiv finProdFinEquiv.injective).toLT 3 A)).card

attribute [local irreducible] a

/-- The registered recurrence at every index at least fifteen. -/
theorem result (n : ℕ) :
    (a (n + 15) : ℤ) =
      6 * a (n + 14) + 23 * a (n + 13) - 102 * a (n + 12) - 288 * a (n + 11) +
      250 * a (n + 10) + 787 * a (n + 9) - 238 * a (n + 8) - 741 * a (n + 7) +
      124 * a (n + 6) + 196 * a (n + 5) - 16 * a (n + 4) - 16 * a (n + 3) := by
  have labelled (m : ℕ) :
      (literalCount (q := 3) horizontal between 1 (m + 1) : ℤ) =
        dotProduct initial ((T ^ m).mulVec terminal) := by
    apply lumped_count horizontal between id (bondDefects between)
      (fun _ d => d ≤ 1) cl T initial terminal 1 (fun _ _ => rfl)
    · intro p d hd
      have h := HardinA229589StripCertificate.structural_certificate.1 p ⟨d, by omega⟩ hd
      rcases (show d = 0 ∨ d = 1 by omega) with rfl | rfl <;>
        simpa only [cl, terminal, Nat.reduceEqDiff, ite_true, ite_false] using h
    · intro p d hd r hr
      omega
    · intro p d hd s
      simpa only [horizontal, HardinA229589StripData.horizontal, bondDefects, Finset.filter_empty, Finset.card_empty,
        Nat.add_zero, id_eq] using
        HardinA229537StripCertificate.finite_certificate.1 p ⟨d, by omega⟩ s
    · exact HardinA229589StripCertificate.structural_certificate.2.2.1
    · intro s
      have h := HardinA229589StripCertificate.structural_certificate.2.2.2.1 s
      simpa only [horizontal, HardinA229589StripData.horizontal, bondDefects,
        Finset.filter_empty, Finset.card_empty, Nat.zero_le, Nat.sub_zero, true_and, id_eq,
        initial, cl, Nat.reduceEqDiff, ite_true, ite_false] using h
  have scale (m : ℕ) (hm : 1 ≤ m) :
      literalCount (q := 3) horizontal between 1 (m + 1) = 6 * a (m + 1) := by
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
      have cards : horizontal.card = 0 ∧ between.card = 10 := by decide +kernel
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
  have bridge (m : ℕ) (hm : 1 ≤ m) :
      dotProduct initial ((T ^ m).mulVec terminal) = 6 * (a (m + 1) : ℤ) := by
    rw [← labelled, scale m hm]
    push_cast
    rfl
  have h := congrArg (fun w => dotProduct initial ((T ^ n).mulVec w))
    HardinA229537StripCertificate.finite_certificate.2
  simp only [Matrix.mulVec_sum, Matrix.mulVec_smul, Matrix.mulVec_mulVec,
    ← pow_add, dotProduct_sum, dotProduct_smul, smul_eq_mul] at h
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.val_one] at h
  have h0 := bridge (n + 2) (by omega)
  have h1 := bridge (n + 3) (by omega)
  have h2 := bridge (n + 4) (by omega)
  have h3 := bridge (n + 5) (by omega)
  have h4 := bridge (n + 6) (by omega)
  have h5 := bridge (n + 7) (by omega)
  have h6 := bridge (n + 8) (by omega)
  have h7 := bridge (n + 9) (by omega)
  have h8 := bridge (n + 10) (by omega)
  have h9 := bridge (n + 11) (by omega)
  have h10 := bridge (n + 12) (by omega)
  have h11 := bridge (n + 13) (by omega)
  have h12 := bridge (n + 14) (by omega)
  simp only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] at h h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  rw [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12] at h
  norm_num only [Nat.reduceAdd, zero_add] at h
  linarith

end D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P4a.HardinA229537Strip
