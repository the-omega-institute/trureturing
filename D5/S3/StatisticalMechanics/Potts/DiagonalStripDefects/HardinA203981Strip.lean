/- GID: D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203981Strip
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203981Strip
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203981Strip.result; premises=D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203981StripCertificate.finite_certificate
   digest: Hardin's recurrence for canonical six-column zero-defect arrays. -/

/-
admission_basis: open-problem-resolution (#32721; Proved)
escape_witness: none (consumed bind-only helpers of the settlement on the live path of HardinA203981Strip.result)
a: proof_shape=bind-only; consumers=counting_bridge, result
scale_count: proof_shape=bind-only; consumers=HardinA229508Strip.counting_bridge, HardinA229683Strip.counting_bridge, counting_bridge
counting_bridge: proof_shape=bind-only; consumers=result
result: proof_shape=content; consumers=none (external open-problem-resolution #32721)
-/

import D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA203981StripData
import D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA203981StripCertificate
import D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229637RowColumn
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical
import Init.Core
import Init.Data.Fin.Lemmas
import Init.Data.List.OfFn
import Init.Data.Nat.Basic
import Init.Data.Nat.Lemmas
import Init.Prelude
import Init.Tactics
import Lean.Meta.Tactic.Simp.BuiltinSimprocs.Nat
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Group.Monoid
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.OfFn
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.SetTheory.Cardinal.Finite

/-! Literal canonical counts and the six-column diagonal-strip recurrence. -/

namespace D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA203981Strip

open HardinA203981StripData
open HardinA203981StripCertificate (coeff finite_certificate)
open D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
open D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229637RowColumn (betw)
open D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical (Canonical canonical_pattern_card)
set_option backward.isDefEq.respectTransparency false

/-- The literal row-major canonical count with n+1 rows and zero defects. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter fun f : Fin (n + 1) × Fin 6 → Fin 3 =>
    defects ∅ (betw 6) (List.ofFn fun i j => f (i, j)) = 0 ∧
    (@Canonical (Fin (n + 1) × Fin 6)
      (LinearOrder.lift' finProdFinEquiv finProdFinEquiv.injective).toLT 3 f)).card

/-- For budgets below the number of bonds in one step, global colour permutations
give six labelled arrays per canonical array when there are at least two rows. -/
theorem scale_count (m d : ℕ) (hm : 1 ≤ m) (hd : d < 10) :
    literalCount (q := 3) ∅ (betw 6) d (m + 1) =
      6 * (Finset.univ.filter fun f : Fin (m + 1) × Fin 6 → Fin 3 =>
        defects ∅ (betw 6) (List.ofFn fun i j => f (i, j)) = d ∧
        (@Canonical (Fin (m + 1) × Fin 6)
          (LinearOrder.lift' finProdFinEquiv finProdFinEquiv.injective).toLT 3 f)).card := by
  classical
  let s : (Fin (m + 1) × Fin 6 → Fin 3) → Prop := fun f =>
    defects ∅ (betw 6) (List.ofFn fun i j => f (i, j)) = d
  have invariant : ∀ e : Equiv.Perm (Fin 3), ∀ f, s (e ∘ f) ↔ s f := by
    intro e f
    change defects ∅ (betw 6) _ = d ↔ _
    rw [show (List.ofFn fun i j => (e ∘ f) (i, j)) =
      (List.ofFn fun i j => f (i, j)).map (fun r => e ∘ r) by rw [List.map_ofFn]; rfl,
      relabel_defects]
  have nonconstant : ∀ f, s f → ∃ x y, f x ≠ f y := by
    intro f h
    by_contra he
    push Not at he
    have hc : f = fun _ => f (0, 0) := funext fun x => he x (0, 0)
    change defects ∅ (betw 6) _ = d at h
    rw [hc] at h
    simp only [List.ofFn_const] at h
    rw [constant_defects, Finset.card_empty, zero_add,
      show (betw 6).card = 10 by rw [between_six]; decide +kernel] at h
    exact (Nat.not_lt_of_ge (h ▸ Nat.le_mul_of_pos_left 10 hm)) hd
  have h := @canonical_pattern_card (Fin (m + 1) × Fin 6) inferInstance
    (LinearOrder.lift' finProdFinEquiv finProdFinEquiv.injective) s invariant nonconstant
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype] at h
  unfold literalCount
  exact h

attribute [local irreducible] a

/-- The labelled zero-budget transfer counts six times the canonical arrays. -/
theorem counting_bridge (m : ℕ) (hm : 1 ≤ m) :
    dotProduct initial ((T ^ m).mulVec (1 : Fin 15 → ℤ)) = 6 * (a m : ℤ) := by
  have labelled : (literalCount (q := 3) ∅ (betw 6) 0 (m + 1) : ℤ) =
      dotProduct initial ((T ^ m).mulVec (1 : Fin 15 → ℤ)) := by
    apply lumped_count ∅ (betw 6) id (bondDefects (betw 6))
      (fun _ d => d = 0) (fun p _ => boundary p) T initial 1 0 (fun _ _ => rfl)
    · intro p d hd
      subst d
      rfl
    · intro p d hd r hr
      subst d
      exact Nat.zero_sub _
    · intro p d hd j
      subst d
      simpa only [bondDefects, Finset.filter_empty, Finset.card_empty, Nat.add_zero,
        Nat.le_zero, id_eq] using HardinA203981StripCertificate.counts p j
    · intro r hr
      rfl
    · intro j
      simpa only [bondDefects, Finset.filter_empty, Finset.card_empty, Nat.le_refl,
        true_and, id_eq] using HardinA203981StripCertificate.initial_counts j
  have h : literalCount (q := 3) ∅ (betw 6) 0 (m + 1) = 6 * a m := by
    unfold a
    exact scale_count m 0 hm (by decide)
  rw [← labelled, h]
  simp only [Nat.cast_mul, Nat.cast_ofNat]

/-- The order-six recurrence at every index at least seven. -/
theorem result (n : ℕ) :
    (a (n + 7) : ℤ) = 25 * a (n + 6) - 45 * a (n + 5) - 963 * a (n + 4) + 2025 * a (n + 3) + 3645 * a (n + 2) - 6561 * a (n + 1) := by
  have h := forward_shift T initial (1 : Fin 15 → ℤ) 6 1 coeff finite_certificate n
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ,
    coeff, Matrix.cons_val_zero, Matrix.cons_val_succ, Nat.reduceAdd, Nat.add_zero,
    Nat.add_assoc] at h
  rw [counting_bridge _ (Nat.succ_pos _), counting_bridge _ (Nat.succ_pos _),
    counting_bridge _ (Nat.succ_pos _), counting_bridge _ (Nat.succ_pos _),
    counting_bridge _ (Nat.succ_pos _), counting_bridge _ (Nat.succ_pos _),
    counting_bridge _ (Nat.succ_pos _)] at h
  linarith

end D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA203981Strip
