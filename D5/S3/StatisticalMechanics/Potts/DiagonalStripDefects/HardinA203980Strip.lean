/- GID: D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203980Strip
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203980Strip
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203980Strip.result; premises=D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203980StripCertificate.finite_certificate
   digest: Eight boundary classes for five-column diagonal and antidiagonal strips. -/

/-
admission_basis: open-problem-resolution (#31593; Proved)
escape_witness: none (consumed bind-only helpers of the settlement on the live path of HardinA203980Strip.result)
a: proof_shape=bind-only; consumers=result
counting_bridge: proof_shape=bind-only; consumers=result
result: proof_shape=bind-only; consumers=none (external open-problem-resolution #31593)
-/

import D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA203980StripData
import D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA203980StripCertificate
import D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical
import D5.S3.Combinatorics.TraceAvoidingArrays.TransferMatrix
import Mathlib.Logic.Equiv.Fin.Basic

/-! Literal canonical counts and the diagonal-strip recurrence. -/

namespace D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA203980Strip
open HardinA203980StripData
open D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
open D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical (Canonical canonical_pattern_card)
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

/-- The literal row-major canonical count of zero-defect arrays with n+1 rows. -/
def a (n : ℕ) : ℕ :=
  letI : DecidablePred (fun f : Fin (n + 1) × Fin 5 → Fin 3 =>
    @Canonical (Fin (n + 1) × Fin 5)
      (LinearOrder.lift' finProdFinEquiv finProdFinEquiv.injective).toLT 3 f) :=
    fun _ => by unfold Canonical; infer_instance
  (Finset.univ.filter fun f : Fin (n + 1) × Fin 5 → Fin 3 =>
    defects horizontal between (List.ofFn fun i j => f (i, j)) = 0 ∧
    (@Canonical (Fin (n + 1) × Fin 5)
      (LinearOrder.lift' finProdFinEquiv finProdFinEquiv.injective).toLT 3 f)).card

attribute [local irreducible] a

/-- The labelled transfer is six times the literal canonical count once a bond is present. -/
theorem counting_bridge (m : ℕ) (hm : 1 ≤ m) :
    dotProduct initial ((T ^ m).mulVec terminal) = 6 * (a m : ℤ) := by
  have labelled : (literalCount (q := 3) horizontal between 0 (m + 1) : ℤ) =
      dotProduct initial ((T ^ m).mulVec terminal) := by
    apply lumped_count horizontal between id (bondDefects between)
      (fun _ d => d = 0) (fun p _ => boundary p) T initial terminal 0 (fun _ _ => rfl)
    · intro p d hd
      subst d
      rfl
    · intro p d hd r hr
      omega
    · intro p d hd s
      subst d
      simpa only [horizontal, bondDefects, Finset.filter_empty, Finset.card_empty,
        Nat.add_zero, Nat.le_zero, id_eq] using HardinA203980StripCertificate.counts p s
    · intro r hr
      simp only [horizontal, bondDefects, Finset.filter_empty, Finset.card_empty, Nat.sub_zero]
    · intro s
      simpa only [horizontal, bondDefects, Finset.filter_empty, Finset.card_empty,
        Nat.le_refl, Nat.sub_zero, true_and, id_eq] using
        HardinA203980StripCertificate.initial_counts s
  have scale : literalCount (q := 3) horizontal between 0 (m + 1) = 6 * a m := by
    classical
    let s : (Fin (m + 1) × Fin 5 → Fin 3) → Prop := fun f =>
      defects horizontal between (List.ofFn fun i j => f (i, j)) = 0
    have invariant : ∀ e : Equiv.Perm (Fin 3), ∀ f, s (e ∘ f) ↔ s f := by
      intro e f
      change defects horizontal between _ = 0 ↔ _
      rw [show (List.ofFn fun i j => (e ∘ f) (i, j)) =
        (List.ofFn fun i j => f (i, j)).map (fun r => e ∘ r) by rw [List.map_ofFn]; rfl,
        relabel_defects]
    have nonconstant : ∀ f, s f → ∃ x y, f x ≠ f y := by
      intro f ha
      by_contra he
      push_neg at he
      have hc : f = fun _ => f (0, 0) := funext fun x => he x (0, 0)
      change defects horizontal between _ = 0 at ha
      rw [hc] at ha
      simp only [List.ofFn_const] at ha
      rw [constant_defects] at ha
      have cards : horizontal.card = 0 ∧ between.card = 8 := by decide +kernel
      rw [cards.1, cards.2] at ha
      omega
    have orbit := @canonical_pattern_card (Fin (m + 1) × Fin 5) inferInstance
      (LinearOrder.lift' finProdFinEquiv finProdFinEquiv.injective) s invariant nonconstant
    simp only [Nat.card_eq_fintype_card, Fintype.card_subtype] at orbit
    unfold literalCount a
    convert orbit using 1
    apply congrArg (fun x : ℕ => 6 * x)
    apply congrArg Finset.card
    ext f
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, s]
  rw [← labelled, scale]
  push_cast
  rfl

/-- The order-four recurrence for every index at least five. -/
theorem result (n : ℕ) :
    (a (n + 5) : ℤ) = 15 * a (n + 4) - 270 * a (n + 2) + 324 * a (n + 1) := by
  have h := D5.S3.Combinatorics.TraceAvoidingArrays.TransferMatrix.scalarRelationShift
    T initial 4 1 ![324, -270, 0, 15] HardinA203980StripCertificate.finite_certificate n
  change dotProduct initial ((T ^ (n + 1 + 4)).mulVec terminal) = _ at h
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.val_one] at h
  have h1 := counting_bridge (n + 1) (by omega)
  have h2 := counting_bridge (n + 2) (by omega)
  have h3 := counting_bridge (n + 3) (by omega)
  have h4 := counting_bridge (n + 4) (by omega)
  have h5 := counting_bridge (n + 5) (by omega)
  simp only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] at h h1 h2 h3 h4 h5
  norm_num only [Nat.reduceAdd, zero_add] at h
  simp only [terminal] at h h1 h2 h3 h4 h5
  rw [h1, h2, h3, h4, h5] at h
  linarith

end D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA203980Strip
