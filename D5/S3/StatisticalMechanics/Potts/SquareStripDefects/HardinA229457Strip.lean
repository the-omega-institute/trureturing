/- GID: D5/S3/StatisticalMechanics/Potts/SquareStripDefects/HardinA229457Strip
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/SquareStripDefects/HardinA229457Strip
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/SquareStripDefects/HardinA229457Strip.result; premises=D5/S3/StatisticalMechanics/Potts/SquareStripDefects/HardinA229457Strip.finite_certificate
   digest: Exact residual-budget square-lattice strip transfer. -/

/-
admission_basis: open-problem-resolution (#31660; Proved)
escape_witness: none (consumed bind-only helpers of the settlement on the live path of HardinA229457Strip.result)
a: proof_shape=bind-only; consumers=result
finite_certificate: proof_shape=bind-only; consumers=result, HardinA229604Strip.finite_certificate
result: proof_shape=bind-only; consumers=none (external open-problem-resolution #31660)
-/

import D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.WidthSix.HardinA229532StripData
import D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229457StripData
import D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229457StripClasses
import D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229457StripPowers
import D5.S3.StatisticalMechanics.Potts.SquareStripDefects.ProperTransfer
import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229584StripData
import D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical

/-! Exact residual-budget square-lattice strip transfer. -/

open scoped BigOperators
open D5.S3.Combinatorics.TraceAvoidingArrays
open D5.S3.StatisticalMechanics.Potts.StripDefects
open HardinA229584StripData (Row horizontal)
namespace D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229457Strip
open DefectTransfer (bondDefects)
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
open HardinA229457StripData
open DefectTransfer (defects literalCount lumped_count forward forward_shift)
open HardinA233177Canonical (Canonical canonical_pattern_card)
/-- Literal row-major canonical arrays, with columns swept only to count bonds. -/
def a (n : ℕ) : ℕ :=
  letI : DecidablePred (fun f : Fin n × Fin 6 → Fin 3 =>
    @Canonical (Fin n × Fin 6)
      (LinearOrder.lift' finProdFinEquiv finProdFinEquiv.injective).toLT 3 f) :=
    fun _ => by unfold Canonical; infer_instance
  (Finset.univ.filter fun f : Fin n × Fin 6 → Fin 3 =>
    defects horizontal ProperTransfer.between (List.ofFn fun i j => f (i, j)) = 1 ∧
    (@Canonical (Fin n × Fin 6)
      (LinearOrder.lift' finProdFinEquiv finProdFinEquiv.injective).toLT 3 f)).card

theorem finite_certificate :
    (∀ p (d : Fin 2), Valid p d.val →
      terminal (cl p d.val) = (if d.val = 0 then 1 else 0)) ∧
    (∀ p (d : Fin 2), Valid p d.val → ∀ r : Row,
      bondDefects ProperTransfer.between p r + bondDefects horizontal r r ≤ d.val →
      Valid r (d.val - (bondDefects ProperTransfer.between p r + bondDefects horizontal r r))) ∧
    (∀ p (d : Fin 2), Valid p d.val → ∀ s : Fin 42,
      (∑ r : Row, if bondDefects ProperTransfer.between p r + bondDefects horizontal r r ≤ d.val ∧
        cl r (d.val - (bondDefects ProperTransfer.between p r + bondDefects horizontal r r)) = s
        then (1 : ℤ) else 0) = T (cl p d.val) s) ∧
    (∀ r : Row, bondDefects horizontal r r ≤ 1 →
      Valid r (1 - bondDefects horizontal r r)) ∧
    (∀ s : Fin 42, (∑ r : Row, if bondDefects horizontal r r ≤ 1 ∧
      cl r (1 - bondDefects horizontal r r) = s then (1 : ℤ) else 0) = initial s) := by
  refine ⟨by decide +kernel, ?_, HardinA229457StripClasses.transition_counts,
    ?_, by decide +kernel⟩
  · intro p d hp r hr
    dsimp only [Valid,
      D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.WidthSix.HardinA229532StripData.Valid] at hp ⊢
    omega
  · intro r hr
    dsimp only [Valid,
      D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.WidthSix.HardinA229532StripData.Valid]
    omega

attribute [local irreducible] a

theorem result (n : ℕ) :
    (a (n + 16) : ℤ) = 60 * a (n + 15) - 1482 * a (n + 14) + 20016 * a (n + 13) - 167163 * a (n + 12) + 924894 * a (n + 11) - 3537110 * a (n + 10) + 9593166 * a (n + 9) - 18693789 * a (n + 8) + 26218062 * a (n + 7) - 26188161 * a (n + 6) + 18139608 * a (n + 5) - 8262712 * a (n + 4) + 2220864 * a (n + 3) - 266256 * a (n + 2) := by
  have labelled (m : ℕ) :
      (literalCount (q := 3) horizontal ProperTransfer.between 1 (m + 1) : ℤ) =
        dotProduct initial ((T ^ m).mulVec terminal) := by
    apply lumped_count horizontal ProperTransfer.between id (bondDefects ProperTransfer.between) Valid cl T initial terminal 1
      (fun _ _ => rfl)
    · intro p d h
      exact finite_certificate.1 p ⟨d, by have := h.1; omega⟩ h
    · intro p d h r hr
      exact finite_certificate.2.1 p ⟨d, by have := h.1; omega⟩ h r hr
    · intro p d h s
      exact finite_certificate.2.2.1 p ⟨d, by have := h.1; omega⟩ h s
    · exact finite_certificate.2.2.2.1
    · exact finite_certificate.2.2.2.2
  have tab (i : Fin 26) : forward T initial i.val = W i := by
    induction i using Fin.induction with
    | zero => exact HardinA229457StripPowers.steps.1.symm
    | succ i ih =>
      rw [forward, Fin.val_succ, Function.iterate_succ_apply']
      change Matrix.vecMul (forward T initial i.val) T = W i.succ
      change forward T initial i.val = W i.castSucc at ih
      rw [ih]
      exact (funext (HardinA229457StripPowers.steps.2 i)).symm
  have poly : forward T initial (1 + 14) =
      ∑ j : Fin 14, (![-266256, 2220864, -8262712, 18139608, -26188161, 26218062, -18693789, 9593166, -3537110, 924894, -167163, 20016, -1482, 60] j : ℤ) • forward T initial (1 + j.val) := by
    rw [tab ⟨15, by omega⟩]
    simp_rw [show ∀ j : Fin 14, forward T initial (1 + j.val) = W ⟨1 + j.val, by omega⟩
      from fun j => tab ⟨1 + j.val, by omega⟩]
    rw [show (⟨15, by omega⟩ : Fin 26) = (15 : Fin 26) by decide]
    funext s
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using
      HardinA229457StripPowers.relation s
  have scale (m : ℕ)  :
      literalCount (q := 3) horizontal ProperTransfer.between 1 (m + 1) = 6 * a (m + 1) := by
    classical
    let predicate : (Fin (m + 1) × Fin 6 → Fin 3) → Prop := fun f =>
      defects horizontal ProperTransfer.between (List.ofFn fun i j => f (i, j)) = 1
    have invariant : ∀ e : Equiv.Perm (Fin 3), ∀ f, predicate (e ∘ f) ↔ predicate f := by
      intro e f
      change defects horizontal ProperTransfer.between _ = 1 ↔ _
      rw [show (List.ofFn fun i j => (e ∘ f) (i, j)) =
        (List.ofFn fun i j => f (i, j)).map (fun r => e ∘ r) by rw [List.map_ofFn]; rfl,
        DefectTransfer.relabel_defects]
    have nonconstant : ∀ f, predicate f → ∃ x y, f x ≠ f y := by
      intro f h
      by_contra he
      push_neg at he
      have const : f = fun _ => f (0, 0) := funext fun x => he x (0, 0)
      change defects horizontal ProperTransfer.between _ = 1 at h
      rw [const] at h
      simp only [List.ofFn_const] at h
      rw [DefectTransfer.constant_defects] at h
      have cards : horizontal.card = 5 ∧ ProperTransfer.between.card = 6 := by decide +kernel
      rw [cards.1, cards.2] at h
      omega
    have orbit := @canonical_pattern_card (Fin (m + 1) × Fin 6) inferInstance
      (LinearOrder.lift' finProdFinEquiv finProdFinEquiv.injective) predicate invariant nonconstant
    simp only [Nat.card_eq_fintype_card, Fintype.card_subtype] at orbit
    unfold literalCount a
    convert orbit using 1
    apply congrArg (fun x : ℕ => 6 * x)
    apply congrArg Finset.card
    ext f
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, predicate]
  have bridge (m : ℕ)  :
      dotProduct initial ((T ^ m).mulVec terminal) = 6 * (a (m + 1) : ℤ) := by
    rw [← labelled, scale m]
    push_cast
    rfl
  have h := forward_shift T initial terminal 14 1 ![-266256, 2220864, -8262712, 18139608, -26188161, 26218062, -18693789, 9593166, -3537110, 924894, -167163, 20016, -1482, 60] poly n
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.val_one] at h
  have h0 := bridge (n + 1)
  have h1 := bridge (n + 2)
  have h2 := bridge (n + 3)
  have h3 := bridge (n + 4)
  have h4 := bridge (n + 5)
  have h5 := bridge (n + 6)
  have h6 := bridge (n + 7)
  have h7 := bridge (n + 8)
  have h8 := bridge (n + 9)
  have h9 := bridge (n + 10)
  have h10 := bridge (n + 11)
  have h11 := bridge (n + 12)
  have h12 := bridge (n + 13)
  have h13 := bridge (n + 14)
  have h14 := bridge (n + 15)
  simp only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] at h h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14
  rw [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14] at h
  norm_num only [Nat.reduceAdd, zero_add] at h
  linarith

end D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229457Strip
