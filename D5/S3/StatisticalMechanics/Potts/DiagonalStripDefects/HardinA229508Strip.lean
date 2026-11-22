/- GID: D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229508Strip
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229508Strip
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229508Strip.result; premises=D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229508StripCertificate.finite_certificate
   digest: Hardin's recurrence for canonical six-column one-defect arrays. -/

/-
admission_basis: open-problem-resolution (#32721; Proved)
escape_witness: none (consumed bind-only helpers of the settlement on the live path of HardinA229508Strip.result)
a: proof_shape=bind-only; consumers=counting_bridge, result
counting_bridge: proof_shape=bind-only; consumers=result
result: proof_shape=content; consumers=none (external open-problem-resolution #32721)
-/

import D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA229508StripData
import D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA229508StripCertificate
import D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA203981Strip
import D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA203981StripCertificate
import D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229637RowColumn
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical
import Init.Core
import Init.Data.Fin.Lemmas
import Init.Data.Nat.Basic
import Init.Data.Sum.Basic
import Init.Data.Sum.Lemmas
import Init.Prelude
import Init.SimpLemmas
import Lean.Meta.Tactic.Simp.BuiltinSimprocs.Nat
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Notation.Pi.Defs
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Order.Basic

namespace D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA229508Strip

open HardinA229508StripData
open HardinA229508StripCertificate (coeff finite_certificate)
open D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
open D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229637RowColumn (betw)
open D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical (Canonical)
set_option backward.isDefEq.respectTransparency false

/-- Literal row-major canonical arrays with n rows and exactly one defect. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter fun f : Fin n × Fin 6 → Fin 3 =>
    defects ∅ (betw 6) (List.ofFn fun i j => f (i, j)) = 1 ∧
    (@Canonical (Fin n × Fin 6)
      (LinearOrder.lift' finProdFinEquiv finProdFinEquiv.injective).toLT 3 f)).card

attribute [local irreducible] a

theorem counting_bridge (m : ℕ) (hm : 1 ≤ m) :
    dotProduct initial ((T ^ m).mulVec terminal) = 6 * (a (m + 1) : ℤ) := by
  have labelled : (literalCount (q := 3) ∅ (betw 6) 1 (m + 1) : ℤ) =
      dotProduct initial ((T ^ m).mulVec terminal) := by
    apply lumped_count ∅ (betw 6) id (bondDefects (betw 6)) (fun _ d => d ≤ 1)
      cl T initial terminal 1 (fun _ _ => rfl)
    · intro p d hd
      simp only [cl, terminal]
      split <;> rfl
    · intro p d hd r hr
      exact (Nat.sub_le _ _).trans hd
    · intro p d hd s
      simpa only [bondDefects, Finset.filter_empty, Finset.card_empty, Nat.add_zero, id_eq] using
        HardinA229508StripCertificate.transition_counts p ⟨d, Nat.lt_succ_of_le hd⟩ s
    · intro r hr
      exact Nat.sub_le _ _
    · intro s
      cases s with
      | inl j =>
        simpa only [bondDefects, Finset.filter_empty, Finset.card_empty, Nat.zero_le,
          Nat.sub_zero, true_and, id_eq, cl, Nat.one_ne_zero, ite_false, Sum.inl.injEq,
          initial, Sum.elim_inl] using HardinA203981StripCertificate.initial_counts j
      | inr j =>
        simp only [bondDefects, Finset.filter_empty, Finset.card_empty, Nat.sub_zero, id_eq,
          cl, Nat.one_ne_zero, ite_false, Sum.inl_ne_inr, and_false, initial,
          Sum.elim_inr, Pi.zero_apply, Finset.sum_const_zero]
  have h : literalCount (q := 3) ∅ (betw 6) 1 (m + 1) = 6 * a (m + 1) := by
    unfold a
    exact HardinA203981Strip.scale_count m 1 hm (by decide)
  rw [← labelled, h]
  simp only [Nat.cast_mul, Nat.cast_ofNat]

/-- The order-twelve recurrence at every index at least fourteen. -/
theorem result (n : ℕ) :
    (a (n + 14) : ℤ) = 50 * a (n + 13) - 715 * a (n + 12) + 324 * a (n + 11) + 50175 * a (n + 10) - 180630 * a (n + 9) - 940491 * a (n + 8) + 4556250 * a (n + 7) + 2329155 * a (n + 6) - 27398736 * a (n + 5) + 13286025 * a (n + 4) + 47829690 * a (n + 3) - 43046721 * a (n + 2) := by
  have h := forward_shift T initial terminal 12 1 coeff finite_certificate n
  simp only [Nat.add_assoc, Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ, Fin.val_one,
    coeff, Matrix.cons_val_zero, Matrix.cons_val_succ, Nat.reduceAdd, Nat.add_zero] at h
  rw [counting_bridge _ (Nat.succ_pos _),
    counting_bridge _ (Nat.succ_pos _),
    counting_bridge _ (Nat.succ_pos _),
    counting_bridge _ (Nat.succ_pos _),
    counting_bridge _ (Nat.succ_pos _),
    counting_bridge _ (Nat.succ_pos _),
    counting_bridge _ (Nat.succ_pos _),
    counting_bridge _ (Nat.succ_pos _),
    counting_bridge _ (Nat.succ_pos _),
    counting_bridge _ (Nat.succ_pos _),
    counting_bridge _ (Nat.succ_pos _),
    counting_bridge _ (Nat.succ_pos _),
    counting_bridge _ (Nat.succ_pos _)] at h
  linarith

end D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA229508Strip
