/- GID: D5/S3/Geometry/AlgebraicBoundary/TauCeti/FieldTheory/IsRealClosed/Real
   generality: G
   mirror-B: D5/B/S3/Geometry/AlgebraicBoundary/TauCeti/FieldTheory/IsRealClosed/Real
   mirror-E: none(waiver:external-source-adaptation)
   anchors: []
   utility: none
   digest: Pinned TauCeti real algebraic dependency for entire boundary recovery. -/

/- Source: TauCetiProject/TauCeti revision 1f9b4414105d86e487a4ac4c3d3397076a44d0d2,
TauCeti/FieldTheory/IsRealClosed/Real.lean.
Adaptation: ordinary D5 import routes; the original declarations and proofs are retained.
License: docs/reports/licenses/TauCeti-LICENSE.txt. Original copyright notices follow.
Retire each transplanted declaration when the actual pinned mathlib supplies an equivalent
statement, and replace its consumers by direct imports and applications of that pinned owner.
This adaptation contributes no independent mathematical novelty or escape credit. -/

/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

import Mathlib.Analysis.Polynomial.Order
import Mathlib.Analysis.Real.Sqrt
public import Mathlib.FieldTheory.IsRealClosed.Basic
public import Mathlib.Basic.Real.Basic

/-! # The real numbers form a real closed field

This file provides `IsRealClosed ℝ`, so results for abstract real closed fields
specialize to the real numbers by typeclass inference. Nonnegative reals are
squares, and every odd-degree real polynomial has a real root.
-/

public section

/-- Odd-degree real polynomials have real roots. -/
private theorem Real.exists_isRoot_of_odd_natDegree {p : Polynomial ℝ}
    (hp : Odd p.natDegree) : ∃ x, p.IsRoot x := by
  by_contra h
  have hleft : ∀ y, p.IsRoot y → y < 0 := fun y hy => (h ⟨y, hy⟩).elim
  have hright : ∀ y, p.IsRoot y → 0 < y := fun y hy => (h ⟨y, hy⟩).elim
  have hsign : Int.negOnePow (p.natDegree : ℤ) = -1 :=
    Int.negOnePow_odd _ (by exact_mod_cast hp)
  rcases le_total 0 p.leadingCoeff with hlc | hlc
  · have hpos := Polynomial.zero_lt_eval_of_roots_lt_of_leadingCoeff_nonneg hleft hlc
    have hneg := Polynomial.zero_lt_negOnePow_mul_eval_of_lt_roots_of_leadingCoeff_nonneg
      hright hlc
    rw [hsign] at hneg
    norm_num at hneg
    linarith
  · have hneg := Polynomial.eval_lt_zero_of_roots_lt_of_leadingCoeff_nonpos hleft hlc
    have hpos := Polynomial.negOnePow_mul_eval_lt_zero_of_lt_roots_of_leadingCoeff_nonpos
      hright hlc
    rw [hsign] at hpos
    norm_num at hpos
    linarith

/-- The real numbers form a real closed field. -/
instance Real.instIsRealClosed : IsRealClosed ℝ :=
  IsRealClosed.of_linearOrderedField (fun hx => Real.isSquare_iff.mpr hx)
    Real.exists_isRoot_of_odd_natDegree
