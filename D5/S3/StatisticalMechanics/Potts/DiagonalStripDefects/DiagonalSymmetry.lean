/- GID: D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/DiagonalSymmetry
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/DiagonalStripDefects/DiagonalSymmetry
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203980Strip.result; premises=D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203980StripCertificate.finite_certificate
   digest: Eight boundary classes for five-column diagonal and antidiagonal strips. -/

/-
admission_basis: open-problem-resolution (#31593; Proved)
escape_witness: none (consumed bind-only helpers of the settlement on the live path of HardinA203980Strip.result)
recolor: proof_shape=bind-only; consumers=transform, cost_recolor, boundary_recolor; reuses=Equiv.piCongrRight
reverse: proof_shape=bind-only; consumers=transform, cost_reverse, boundary_reverse; reuses=Equiv.arrowCongr, Fin.revPerm
transform: proof_shape=bind-only; consumers=class_rep, lift_counts
cost_formula: proof_shape=bind-only; consumers=cost_recolor, cost_reverse
cost_recolor: proof_shape=bind-only; consumers=lift_counts
cost_reverse: proof_shape=bind-only; consumers=lift_counts
boundary_recolor: proof_shape=bind-only; consumers=lift_counts
boundary_reverse: proof_shape=bind-only; consumers=lift_counts
class_rep: proof_shape=bind-only; consumers=lift_counts
lift_counts: proof_shape=bind-only; consumers=HardinA203980StripCertificate.counts
-/

import D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA203980StripData
import D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer

/-! Parity-wise row transformations preserve every diagonal defect count. -/

open scoped BigOperators
namespace D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.DiagonalSymmetry
open HardinA203980StripData
open D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer (bondDefects)
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

private def recolor (e f : Equiv.Perm (Fin 3)) : Row ≃ Row :=
  Equiv.piCongrRight (fun i : Fin 5 => if i.val % 2 = 0 then e else f)

private def reverse : Row ≃ Row :=
  Equiv.arrowCongr (Fin.revPerm : Equiv.Perm (Fin 5)) (Equiv.refl (Fin 3))

private def transform (b : Bool) (e f : Equiv.Perm (Fin 3)) : Row ≃ Row :=
  (if b then reverse else Equiv.refl Row).trans (recolor e f)

private theorem cost_formula (p r : Row) :
    bondDefects between p r =
      (if p 0 = r 1 then 1 else 0) + (if p 1 = r 0 then 1 else 0) +
      (if p 1 = r 2 then 1 else 0) + (if p 2 = r 1 then 1 else 0) +
      (if p 2 = r 3 then 1 else 0) + (if p 3 = r 2 then 1 else 0) +
      (if p 3 = r 4 then 1 else 0) + (if p 4 = r 3 then 1 else 0) := by
  simp only [bondDefects, Finset.card_eq_sum_ones, Finset.sum_filter, between]
  norm_num only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton,
    Prod.mk.injEq, Fin.reduceEq, and_false, false_and, or_false, false_or, not_false_eq_true,
    Finset.sum_singleton, Prod.fst, Prod.snd]
  omega

private theorem cost_recolor (e f : Equiv.Perm (Fin 3)) (p r : Row) :
    bondDefects between (recolor e f p) (recolor f e r) = bondDefects between p r := by
  norm_num [cost_formula, recolor, Equiv.piCongrRight_apply, Fin.val_natCast,
    e.injective.eq_iff, f.injective.eq_iff]

private theorem cost_reverse (p r : Row) :
    bondDefects between (reverse p) (reverse r) = bondDefects between p r := by
  norm_num [cost_formula, reverse, Equiv.arrowCongr_apply, Fin.revPerm, Fin.rev,
    Fin.val_natCast]
  omega

private theorem boundary_recolor (e f : Equiv.Perm (Fin 3)) (p : Row) :
    boundary (recolor e f p) = boundary p := by
  norm_num [boundary, recolor, Equiv.piCongrRight_apply, Fin.val_natCast,
    e.injective.eq_iff, f.injective.eq_iff]

private theorem boundary_reverse : ∀ p : Row, boundary (reverse p) = boundary p := by
  decide +kernel

private theorem class_rep : ∀ p : Row, ∃ b : Bool, ∃ e f : Equiv.Perm (Fin 3),
    transform b e f p = representatives (boundary p) := by
  intro p
  generalize h : p 0 = c
  fin_cases c <;> decide +kernel +revert

/-- Counts at representatives determine counts at every row by parity-wise colour permutations. -/
theorem lift_counts (d : ℕ) (t : Matrix (Fin 8) (Fin 8) ℤ)
    (h : ∀ i j : Fin 8, (∑ r : Row,
      if bondDefects between (representatives i) r = d ∧ boundary r = j
      then (1 : ℤ) else 0) = t i j) (p : Row) (j : Fin 8) :
    (∑ r : Row, if bondDefects between p r = d ∧ boundary r = j
      then (1 : ℤ) else 0) = t (boundary p) j := by
  obtain ⟨b, e, f, hp⟩ := class_rep p
  have cost (r : Row) : bondDefects between (transform b e f p) (transform b f e r) =
      bondDefects between p r := by
    cases b <;> simp only [transform, Bool.false_eq_true, ↓reduceIte,
      Equiv.trans_apply, Equiv.refl_apply, cost_recolor, cost_reverse]
  have cls (r : Row) : boundary (transform b f e r) = boundary r := by
    cases b <;> simp only [transform, Bool.false_eq_true, ↓reduceIte,
      Equiv.trans_apply, Equiv.refl_apply, boundary_recolor, boundary_reverse]
  calc
    _ = ∑ r : Row, if bondDefects between (transform b e f p) (transform b f e r) = d ∧
        boundary (transform b f e r) = j then (1 : ℤ) else 0 := by simp_rw [cost, cls]
    _ = _ := by
      rw [hp]
      exact ((transform b f e).sum_comp (fun r =>
        if bondDefects between (representatives (boundary p)) r = d ∧ boundary r = j
        then (1 : ℤ) else 0)).trans (h _ _)

end D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.DiagonalSymmetry
