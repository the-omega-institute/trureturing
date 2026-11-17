/- GID: D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/HardinA229532Strip
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/HardinA229532Strip
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/HardinA229532Strip.result; premises=D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/HardinA229532Strip.finite_certificate,D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/HardinA229532Strip.base_certificate
   digest: Exact width-six one-defect HDA transfer. -/

/-
admission_basis: open-problem-resolution (#31328; Proved)
escape_witness: none (consumed bind-only helpers of the settlement on the live path of HardinA229532Strip.result)
finite_certificate: proof_shape=bind-only; consumers=result
base_certificate: proof_shape=bind-only; consumers=result
a: proof_shape=bind-only; consumers=result
result: proof_shape=bind-only; consumers=none (external open-problem-resolution #31328)
-/

import D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.WidthSix.HardinA229532StripClasses
import D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical
import Mathlib.Logic.Equiv.Fin.Basic

open scoped BigOperators
open D5.S3.StatisticalMechanics.Potts.StripDefects
namespace D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.HardinA229532Strip
open DefectTransfer (bondDefects)
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option synthInstance.maxSize 100000
open D5.S3.Combinatorics.TraceAvoidingArrays
open D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229584StripData (Row horizontal)
open WidthSix
open DefectTransfer (defects literalCount lumped_count forward forward_shift)
open HardinA233177Canonical (Canonical canonical_pattern_card)
open HardinA229532StripData

/-- The literal row-major canonical filtered array count. -/
def a (n : ℕ) : ℕ :=
  letI : DecidablePred (fun A : Fin n × Fin 6 → Fin 3 =>
    @Canonical (Fin n × Fin 6)
      (LinearOrder.lift' finProdFinEquiv finProdFinEquiv.injective).toLT 3 A) :=
    fun _ => by unfold Canonical; infer_instance
  (Finset.univ.filter fun A : Fin n × Fin 6 → Fin 3 =>
    defects horizontal between (List.ofFn fun i j => A (i, j)) = 1 ∧
    (@Canonical (Fin n × Fin 6)
      (LinearOrder.lift' finProdFinEquiv finProdFinEquiv.injective).toLT 3 A)).card

private theorem finite_certificate :
    (∀ p (d : Fin 2), Valid p d.val →
      terminal (cl p d.val) = (if d.val = 0 then 1 else 0)) ∧
    (∀ p (d : Fin 2), Valid p d.val → ∀ r : Row,
      bondDefects between p r + bondDefects horizontal r r ≤ d.val →
      Valid r (d.val - (bondDefects between p r + bondDefects horizontal r r))) ∧
    (∀ p (d : Fin 2), Valid p d.val → ∀ s : Fin 31,
      (∑ r : Row, if bondDefects between p r + bondDefects horizontal r r ≤ d.val ∧
        cl r (d.val - (bondDefects between p r + bondDefects horizontal r r)) = s
        then (1 : ℤ) else 0) = T (cl p d.val) s) ∧
    (∀ r : Row, bondDefects horizontal r r ≤ 1 →
      Valid r (1 - bondDefects horizontal r r)) ∧
    (∀ s : Fin 31, (∑ r : Row, if bondDefects horizontal r r ≤ 1 ∧
      cl r (1 - bondDefects horizontal r r) = s then (1 : ℤ) else 0) = initial s) ∧
    (W 0 = initial ∧ ∀ i : Fin 20, W i.succ = Matrix.vecMul (W i.castSucc) T) ∧
    W 20 = ∑ j : Fin 18, (![-25, 240, 204, -6334, 6468, 42628, -83203, -34136, 160400, -40816, -108224, 56184, 23849, -19128, 340, 1854, -436, 36] j : ℤ) • W ⟨2 + j.val, by omega⟩ := by
  refine ⟨by decide +kernel, (by
    intro p d hp r hr
    dsimp only [Valid] at hp ⊢
    omega), HardinA229532StripClasses.transition_counts,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

private theorem base_certificate :
    dotProduct (W 19) terminal = ∑ j : Fin 18, (![-25, 240, 204, -6334, 6468, 42628, -83203, -34136, 160400, -40816, -108224, 56184, 23849, -19128, 340, 1854, -436, 36] j : ℤ) *
      dotProduct (W ⟨1 + j.val, by omega⟩) terminal := by decide +kernel

attribute [local irreducible] a

theorem result (n : ℕ) :
    (a (n + 20) : ℤ) = 36 * a (n + 19) - 436 * a (n + 18) + 1854 * a (n + 17) + 340 * a (n + 16) - 19128 * a (n + 15) + 23849 * a (n + 14) + 56184 * a (n + 13) - 108224 * a (n + 12) - 40816 * a (n + 11) + 160400 * a (n + 10) - 34136 * a (n + 9) - 83203 * a (n + 8) + 42628 * a (n + 7) + 6468 * a (n + 6) - 6334 * a (n + 5) + 204 * a (n + 4) + 240 * a (n + 3) - 25 * a (n + 2) := by
  have labelled (m : ℕ) :
      (literalCount (q := 3) horizontal between 1 (m + 1) : ℤ) =
        dotProduct initial ((T ^ m).mulVec terminal) := by
    apply lumped_count horizontal between id (bondDefects between) Valid cl T initial terminal 1
      (fun _ _ => rfl)
    · intro p d h
      exact finite_certificate.1 p ⟨d, by have := h.1; omega⟩ h
    · intro p d h r hr
      exact finite_certificate.2.1 p ⟨d, by have := h.1; omega⟩ h r hr
    · intro p d h s
      exact finite_certificate.2.2.1 p ⟨d, by have := h.1; omega⟩ h s
    · exact finite_certificate.2.2.2.1
    · exact finite_certificate.2.2.2.2.1
  have tab (i : Fin 21) : forward T initial i.val = W i := by
    induction i using Fin.induction with
    | zero => exact finite_certificate.2.2.2.2.2.1.1.symm
    | succ i ih =>
      rw [forward, Fin.val_succ, Function.iterate_succ_apply']
      change Matrix.vecMul (forward T initial i.val) T = W i.succ
      change forward T initial i.val = W i.castSucc at ih
      rw [ih]
      exact (finite_certificate.2.2.2.2.2.1.2 i).symm
  have poly : forward T initial (2 + 18) =
      ∑ j : Fin 18, (![-25, 240, 204, -6334, 6468, 42628, -83203, -34136, 160400, -40816, -108224, 56184, 23849, -19128, 340, 1854, -436, 36] j : ℤ) • forward T initial (2 + j.val) := by
    rw [tab ⟨20, by omega⟩]
    simp_rw [show ∀ j : Fin 18, forward T initial (2 + j.val) = W ⟨2 + j.val, by omega⟩
      from fun j => tab ⟨2 + j.val, by omega⟩]
    exact finite_certificate.2.2.2.2.2.2
  have scale (m : ℕ) (hm : 1 ≤ m) :
      literalCount (q := 3) horizontal between 1 (m + 1) = 6 * a (m + 1) := by
    classical
    let S : (Fin (m + 1) × Fin 6 → Fin 3) → Prop := fun A =>
      defects horizontal between (List.ofFn fun i j => A (i, j)) = 1
    have invariant : ∀ e : Equiv.Perm (Fin 3), ∀ A, S (e ∘ A) ↔ S A := by
      intro e A
      change defects horizontal between _ = 1 ↔ _
      rw [show (List.ofFn fun i j => (e ∘ A) (i, j)) =
        (List.ofFn fun i j => A (i, j)).map (fun r => e ∘ r) by rw [List.map_ofFn]; rfl,
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
      have cards : horizontal.card = 5 ∧ between.card = 10 := by decide +kernel
      rw [cards.1, cards.2] at h
      omega
    have orbit := @canonical_pattern_card (Fin (m + 1) × Fin 6) inferInstance
      (LinearOrder.lift' finProdFinEquiv finProdFinEquiv.injective) S invariant nonconstant
    simp only [Nat.card_eq_fintype_card, Fintype.card_subtype] at orbit
    unfold literalCount a
    convert orbit using 1
    apply congrArg (fun x : ℕ => 6 * x)
    apply congrArg Finset.card
    ext A
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, S]
  have bridge (m : ℕ) (hm : 1 ≤ m) :
      dotProduct initial ((T ^ m).mulVec terminal) = 6 * (a (m + 1) : ℤ) := by
    rw [← labelled, scale m hm]
    push_cast
    rfl
  have h : dotProduct initial ((T ^ (n + 1 + 18)).mulVec terminal) =
      ∑ j : Fin 18, (![-25, 240, 204, -6334, 6468, 42628, -83203, -34136, 160400, -40816, -108224, 56184, 23849, -19128, 340, 1854, -436, 36] j : ℤ) *
        dotProduct initial ((T ^ (n + 1 + j.val)).mulVec terminal) := by
    cases n with
    | zero =>
      simp only [Nat.zero_add]
      simp_rw [Matrix.dotProduct_mulVec, ← DefectTransfer.forward_eq]
      rw [tab ⟨19, by omega⟩]
      simp_rw [show ∀ j : Fin 18, forward T initial (1 + j.val) = W ⟨1 + j.val, by omega⟩
        from fun j => tab ⟨1 + j.val, by omega⟩]
      exact base_certificate
    | succ m =>
      simpa only [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        (forward_shift T initial terminal 18 2 ![-25, 240, 204, -6334, 6468, 42628, -83203, -34136, 160400, -40816, -108224, 56184, 23849, -19128, 340, 1854, -436, 36] poly m)
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.val_one] at h
  have h0 := bridge (n + 1) (by omega)
  have h1 := bridge (n + 2) (by omega)
  have h2 := bridge (n + 3) (by omega)
  have h3 := bridge (n + 4) (by omega)
  have h4 := bridge (n + 5) (by omega)
  have h5 := bridge (n + 6) (by omega)
  have h6 := bridge (n + 7) (by omega)
  have h7 := bridge (n + 8) (by omega)
  have h8 := bridge (n + 9) (by omega)
  have h9 := bridge (n + 10) (by omega)
  have h10 := bridge (n + 11) (by omega)
  have h11 := bridge (n + 12) (by omega)
  have h12 := bridge (n + 13) (by omega)
  have h13 := bridge (n + 14) (by omega)
  have h14 := bridge (n + 15) (by omega)
  have h15 := bridge (n + 16) (by omega)
  have h16 := bridge (n + 17) (by omega)
  have h17 := bridge (n + 18) (by omega)
  have h18 := bridge (n + 19) (by omega)
  simp only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] at h h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18
  rw [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18] at h
  norm_num only [Nat.reduceAdd, zero_add] at h
  linarith

end D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.HardinA229532Strip
