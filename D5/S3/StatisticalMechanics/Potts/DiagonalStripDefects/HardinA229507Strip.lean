/- GID: D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229507Strip
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229507Strip
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229507Strip.result; premises=D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229507StripCertificate.finite_certificate
   digest: Eight boundary classes for five-column diagonal and antidiagonal strips. -/

/-
admission_basis: open-problem-resolution (#31593; Proved)
escape_witness: none (consumed bind-only helpers of the settlement on the live path of HardinA229507Strip.result)
a: proof_shape=bind-only; consumers=result
counting_bridge: proof_shape=bind-only; consumers=result
result: proof_shape=bind-only; consumers=none (external open-problem-resolution #31593)
-/

import D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA229507StripData
import D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA203980StripData
import D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA203980StripCertificate
import D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA229507StripCertificate
import D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical
import Mathlib.Logic.Equiv.Fin.Basic

/-! Literal canonical counts and the diagonal-strip recurrence. -/

namespace D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA229507Strip
open HardinA229507StripData
open HardinA203980StripData (Row horizontal between)
open D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
open D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical (Canonical canonical_pattern_card)
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

/-- The literal row-major canonical count of one-defect arrays with n rows. -/
def a (n : ℕ) : ℕ :=
  letI : DecidablePred (fun f : Fin n × Fin 5 → Fin 3 =>
    @Canonical (Fin n × Fin 5)
      (LinearOrder.lift' finProdFinEquiv finProdFinEquiv.injective).toLT 3 f) :=
    fun _ => by unfold Canonical; infer_instance
  (Finset.univ.filter fun f : Fin n × Fin 5 → Fin 3 =>
    defects horizontal between (List.ofFn fun i j => f (i, j)) = 1 ∧
    (@Canonical (Fin n × Fin 5)
      (LinearOrder.lift' finProdFinEquiv finProdFinEquiv.injective).toLT 3 f)).card

attribute [local irreducible] a

/-- The labelled transfer is six times the literal canonical count once a bond is present. -/
theorem counting_bridge (m : ℕ) :
    dotProduct initial ((T ^ m).mulVec terminal) = 6 * (a (m + 1) : ℤ) := by
  have labelled : (literalCount (q := 3) horizontal between 1 (m + 1) : ℤ) =
      dotProduct initial ((T ^ m).mulVec terminal) := by
    apply lumped_count horizontal between id (bondDefects between)
      (fun _ d => d ≤ 1) cl T initial terminal 1 (fun _ _ => rfl)
    · intro p d hd
      interval_cases d <;> simp only [cl, terminal, Nat.reduceEqDiff, Nat.lt_irrefl, Nat.zero_lt_one,
        ite_false, ite_true, Fin.append_left, Fin.append_right,
        HardinA203980StripData.terminal, Pi.zero_apply, Pi.one_apply]
    · intro p d hd r hr
      omega
    · intro p d hd s
      simpa only [horizontal, bondDefects, Finset.filter_empty, Finset.card_empty,
        Nat.add_zero, id_eq] using HardinA229507StripCertificate.transition_counts p ⟨d, by omega⟩ s
    · intro r hr
      simp only [horizontal, bondDefects, Finset.filter_empty, Finset.card_empty, Nat.sub_zero]
      omega
    · intro s
      simp only [horizontal, bondDefects, Finset.filter_empty, Finset.card_empty,
        Nat.zero_le, Nat.sub_zero, true_and, id_eq]
      induction s using Fin.addCases (m := 8) (n := 8) with
      | left j =>
        have cut (r : Row) : cl r 1 = j.castAdd 8 ↔ HardinA203980StripData.boundary r = j := by
          simp only [cl, Nat.zero_lt_one, ite_true, Fin.ext_iff, Fin.val_castAdd]
        simpa only [cut, initial,
          Fin.append_left] using HardinA203980StripCertificate.initial_counts j
      | right j =>
        have cut (r : Row) : cl r 1 ≠ j.natAdd 8 := by
          intro h
          have hb := (HardinA203980StripData.boundary r).isLt
          simp only [cl, Nat.zero_lt_one, ite_true, Fin.ext_iff,
            Fin.val_castAdd, Fin.val_natAdd] at h
          omega
        simp only [cut, ite_false, Finset.sum_const_zero, initial, Fin.append_right, Pi.zero_apply]
  have scale : literalCount (q := 3) horizontal between 1 (m + 1) = 6 * a (m + 1) := by
    classical
    let s : (Fin (m + 1) × Fin 5 → Fin 3) → Prop := fun f =>
      defects horizontal between (List.ofFn fun i j => f (i, j)) = 1
    have invariant : ∀ e : Equiv.Perm (Fin 3), ∀ f, s (e ∘ f) ↔ s f := by
      intro e f
      change defects horizontal between _ = 1 ↔ _
      rw [show (List.ofFn fun i j => (e ∘ f) (i, j)) =
        (List.ofFn fun i j => f (i, j)).map (fun r => e ∘ r) by rw [List.map_ofFn]; rfl,
        relabel_defects]
    have nonconstant : ∀ f, s f → ∃ x y, f x ≠ f y := by
      intro f ha
      by_contra he
      push_neg at he
      have hc : f = fun _ => f (0, 0) := funext fun x => he x (0, 0)
      change defects horizontal between _ = 1 at ha
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

/-- The order-eight recurrence for every index at least ten. -/
theorem result (n : ℕ) :
    (a (n + 10) : ℤ) = 30 * a (n + 9) - 225 * a (n + 8) - 540 * a (n + 7) +
      8748 * a (n + 6) - 9720 * a (n + 5) - 72900 * a (n + 4) +
      174960 * a (n + 3) - 104976 * a (n + 2) := by
  have h := congrArg (fun w => dotProduct initial ((T ^ n).mulVec w))
    HardinA229507StripCertificate.finite_certificate
  simp only [Matrix.mulVec_sum, Matrix.mulVec_add, Matrix.mulVec_zero, Matrix.mulVec_smul, Matrix.mulVec_mulVec,
    ← pow_add, dotProduct_sum, dotProduct_smul, smul_eq_mul,
    Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.val_one, dotProduct_add, dotProduct_zero] at h
  have h1 := counting_bridge (n + 1)
  have h2 := counting_bridge (n + 2)
  have h3 := counting_bridge (n + 3)
  have h4 := counting_bridge (n + 4)
  have h5 := counting_bridge (n + 5)
  have h6 := counting_bridge (n + 6)
  have h7 := counting_bridge (n + 7)
  have h8 := counting_bridge (n + 8)
  have h9 := counting_bridge (n + 9)
  simp only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] at h h1 h2 h3 h4 h5 h6 h7 h8 h9
  norm_num only [Nat.reduceAdd, zero_add] at h
  rw [h1, h2, h3, h4, h5, h6, h7, h8, h9] at h
  norm_num only [Nat.reduceAdd, zero_add] at h
  linarith

end D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA229507Strip
