/- GID: D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229683Strip
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229683Strip
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229683Strip.result; premises=D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229683StripCertificate.finite_certificate
   digest: Hardin's recurrence for canonical six-column two-defect arrays. -/

/-
admission_basis: open-problem-resolution (#32721; Proved)
escape_witness: none (consumed bind-only helpers of the settlement on the live path of HardinA229683Strip.result)
a: proof_shape=bind-only; consumers=counting_bridge, result
counting_bridge: proof_shape=bind-only; consumers=result
result: proof_shape=content; consumers=none (external open-problem-resolution #32721)
-/

import D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA229683StripData
import D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA229683StripCertificate
import D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA229508StripData
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
import Init.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Notation.Pi.Defs
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Order.Basic

namespace D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA229683Strip

open HardinA229683StripData
open HardinA229683StripCertificate (coeff coeff_values finite_certificate)
open D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
open D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229637RowColumn (betw)
open D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical (Canonical)
set_option backward.isDefEq.respectTransparency false

/-- The literal row-major canonical count with n rows and two defects. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter fun f : Fin n × Fin 6 → Fin 3 =>
    defects ∅ (betw 6) (List.ofFn fun i j => f (i, j)) = 2 ∧
    (@Canonical (Fin n × Fin 6)
      (LinearOrder.lift' finProdFinEquiv finProdFinEquiv.injective).toLT 3 f)).card

attribute [local irreducible] a

theorem counting_bridge (m : ℕ) :
    dotProduct initial ((T ^ m).mulVec terminal) = 6 * (a (m + 1) : ℤ) := by
  have labelled : (literalCount (q := 3) ∅ (betw 6) 2 (m + 1) : ℤ) =
      dotProduct initial ((T ^ m).mulVec terminal) := by
    apply lumped_count ∅ (betw 6) id (bondDefects (betw 6)) (fun _ d => d ≤ 2)
      cl T initial terminal 2 (fun _ _ => rfl)
    · intro p d hd
      simp only [cl, terminal]
      split <;> rfl
    · intro p d hd r hr
      exact (Nat.sub_le _ _).trans hd
    · intro p d hd s
      simpa only [bondDefects, Finset.filter_empty, Finset.card_empty, Nat.add_zero, id_eq] using
        HardinA229683StripCertificate.transition_counts p ⟨d, Nat.lt_succ_of_le hd⟩ s
    · intro r hr
      exact Nat.sub_le _ _
    · intro s
      cases s with
      | inl s =>
        cases s with
        | inl j =>
          simpa only [bondDefects, Finset.filter_empty, Finset.card_empty, Nat.zero_le,
            Nat.sub_zero, true_and, id_eq, cl, show (2 : ℕ) ≠ 0 by decide, Nat.one_ne_zero,
            Nat.reduceSub, ite_false, Sum.inl.injEq, initial, HardinA229508StripData.initial,
            HardinA229508StripData.cl, Sum.elim_inl] using HardinA203981StripCertificate.initial_counts j
        | inr j =>
          simp only [bondDefects, Finset.filter_empty, Finset.card_empty, Nat.sub_zero, id_eq,
            cl, show (2 : ℕ) ≠ 0 by decide, Nat.one_ne_zero, Nat.reduceSub, ite_false,
            HardinA229508StripData.cl, Sum.inl.injEq, Sum.inl_ne_inr, and_false, initial,
            HardinA229508StripData.initial, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, Finset.sum_const_zero]
      | inr j =>
        simp only [bondDefects, Finset.filter_empty, Finset.card_empty, Nat.sub_zero, id_eq,
          cl, show (2 : ℕ) ≠ 0 by decide, ite_false, Sum.inl_ne_inr, and_false, initial,
          Sum.elim_inr, Pi.zero_apply, Finset.sum_const_zero]
  have h : literalCount (q := 3) ∅ (betw 6) 2 (m + 1) = 6 * a (m + 1) := by
    unfold a
    exact HardinA203981Strip.scale_count m 2 (by omega)
  rw [← labelled, h]
  simp only [Nat.cast_mul, Nat.cast_ofNat]

/-- The order-eighteen recurrence at every index at least twenty-one. -/
theorem result (n : ℕ) :
    (a (n + 21) : ℤ) = 75 * a (n + 20) - 2010 * a (n + 19) + 19486 * a (n + 18) + 60075 * a (n + 17) - 2206575 * a (n + 16) + 7404210 * a (n + 15) + 70536825 * a (n + 14) - 435322350 * a (n + 13) - 601275555 * a (n + 12) + 8082823950 * a (n + 11) - 6257717775 * a (n + 10) - 54520532190 * a (n + 9) + 92909172825 * a (n + 8) + 132368667075 * a (n + 7) - 366499782594 * a (n + 6) + 470715894135 * a (n + 4) - 282429536481 * a (n + 3) := by
  have h := forward_shift T initial terminal 18 2 coeff finite_certificate n
  simp only [Nat.add_assoc, Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ, Fin.val_one,
    coeff_values, Matrix.cons_val_zero, Matrix.cons_val_succ, Nat.reduceAdd, Nat.add_zero] at h
  simp only [counting_bridge] at h
  linarith

end D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA229683Strip
