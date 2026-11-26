/- GID: D5/S3/Geometry/AlgebraicBoundary/TauCeti/FieldTheory/RealClosure/Complexification
   generality: G
   mirror-B: D5/B/S3/Geometry/AlgebraicBoundary/TauCeti/FieldTheory/RealClosure/Complexification
   mirror-E: none(waiver:external-source-adaptation)
   anchors: []
   utility: none
   digest: Pinned TauCeti real algebraic dependency for entire boundary recovery. -/

/- Source: TauCetiProject/TauCeti revision 1f9b4414105d86e487a4ac4c3d3397076a44d0d2,
TauCeti/FieldTheory/RealClosure/Complexification.lean.
Adaptation: ordinary D5 import routes; selected declarations retain their original proofs.
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

public import D5.S3.Geometry.AlgebraicBoundary.TauCeti.Algebra.QuadraticAlgebra.Square
public import D5.S3.Geometry.AlgebraicBoundary.TauCeti.Algebra.Ring.Semireal
public import Mathlib.Analysis.RCLike.Sqrt
public import D5.S3.Geometry.AlgebraicBoundary.TauCeti.FieldTheory.IsRealClosed.Real
import D5.S3.Geometry.AlgebraicBoundary.TauCeti.FieldTheory.RealClosure.Sqrt
import D5.S3.Geometry.AlgebraicBoundary.TauCeti.Algebra.Order.Ring.Ordering.Semireal

/-! # Square roots in the complexification of a real closed field

`QuadraticAlgebra.isSquare` specializes the algebraic square-root construction to a real
closed field, without requiring an order on that field as a hypothesis. This square-closure
property is used to prove algebraic closedness of the complexification.

The retained source supplies the useful proof dependencies. Further exact applications,
including their assumptions and boundary cases, are developed in the owning Blueprint.

-/

public section

namespace QuadraticAlgebra

open TauCeti.RealClosure

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
variable [IsRealClosed R]

private noncomputable def complex_sqrt_magnitude
    (a b : R) : R :=
  nonnegSqrt (add_nonneg (sq_nonneg a) (sq_nonneg b))

private theorem complex_sqrt_magnitude_ge_abs
    (a b : R) :
    |a| ≤ complex_sqrt_magnitude a b := by
  have hm0 : 0 ≤ complex_sqrt_magnitude a b :=
    nonnegSqrt_nonneg (add_nonneg (sq_nonneg a) (sq_nonneg b))
  have hm : (complex_sqrt_magnitude a b) ^ 2 = a ^ 2 + b ^ 2 :=
    sq_nonnegSqrt (add_nonneg (sq_nonneg a) (sq_nonneg b))
  apply (sq_le_sq₀ (abs_nonneg a) hm0).mp
  rw [sq_abs, hm]
  nlinarith [sq_nonneg b]

private theorem complex_sqrt_radicands_nonneg
    (a b : R) :
    0 ≤ (complex_sqrt_magnitude a b + a) / 2 ∧
      0 ≤ (complex_sqrt_magnitude a b - a) / 2 := by
  have h' := complex_sqrt_magnitude_ge_abs a b
  constructor <;> apply div_nonneg (by linarith [neg_abs_le a, le_abs_self a]) (by norm_num)

private noncomputable def complex_sqrt_real_part
    (a b : R) : R :=
  nonnegSqrt (complex_sqrt_radicands_nonneg a b).1

private noncomputable def complex_sqrt_imag_part
    (a b : R) : R :=
  nonnegSqrt (complex_sqrt_radicands_nonneg a b).2

/-- The square root in `R[i]` whose real part is nonnegative and whose imaginary part is
nonnegative when the input's imaginary part is nonnegative, and nonpositive otherwise. -/
noncomputable def _root_.QuadraticAlgebra.sqrt
    (z : QuadraticAlgebra R (-1) 0) : QuadraticAlgebra R (-1) 0 := by
  exact ⟨complex_sqrt_real_part z.re z.im,
    if 0 ≤ z.im then complex_sqrt_imag_part z.re z.im
    else -complex_sqrt_imag_part z.re z.im⟩

/-- The coordinates of the chosen square root satisfy the equations obtained by squaring. -/
theorem _root_.QuadraticAlgebra.sqrt_coordinates
    (z : QuadraticAlgebra R (-1) 0) :
    z.sqrt.re ^ 2 - z.sqrt.im ^ 2 = z.re ∧ 2 * z.sqrt.re * z.sqrt.im = z.im := by
  let a := z.re
  let b := z.im
  let m := complex_sqrt_magnitude a b
  let s := complex_sqrt_real_part a b
  let q := complex_sqrt_imag_part a b
  have hm : m ^ 2 = a ^ 2 + b ^ 2 :=
    sq_nonnegSqrt (add_nonneg (sq_nonneg a) (sq_nonneg b))
  have hs0 : 0 ≤ s := nonnegSqrt_nonneg (complex_sqrt_radicands_nonneg a b).1
  have hs : s ^ 2 = (m + a) / 2 :=
    sq_nonnegSqrt (complex_sqrt_radicands_nonneg a b).1
  have hq0 : 0 ≤ q := nonnegSqrt_nonneg (complex_sqrt_radicands_nonneg a b).2
  have hq : q ^ 2 = (m - a) / 2 :=
    sq_nonnegSqrt (complex_sqrt_radicands_nonneg a b).2
  have hreal : s ^ 2 - q ^ 2 = a := by
    rw [hs, hq]
    ring
  have hprod_sq : (2 * s * q) ^ 2 = |b| ^ 2 := by
    calc
      (2 * s * q) ^ 2 = 4 * s ^ 2 * q ^ 2 := by ring
      _ = 4 * ((m + a) / 2) * ((m - a) / 2) := by rw [hs, hq]
      _ = b ^ 2 := by nlinarith [hm]
      _ = |b| ^ 2 := by rw [sq_abs]
  have hprod_nonneg : 0 ≤ 2 * s * q := mul_nonneg (mul_nonneg (by norm_num) hs0) hq0
  have hprod : 2 * s * q = |b| :=
    (sq_eq_sq₀ hprod_nonneg (abs_nonneg b)).mp hprod_sq
  have himag : 2 * s * (if 0 ≤ b then q else -q) = b := by
    by_cases hb : 0 ≤ b
    · simpa [hb, abs_of_nonneg hb] using hprod
    · have hbneg : b < 0 := lt_of_not_ge hb
      rw [ite_eq_right hb]
      calc
        2 * s * -q = -(2 * s * q) := by ring
        _ = -|b| := by rw [hprod]
        _ = b := by simp [abs_of_neg hbneg]
  have ha_def : a = z.re := rfl
  have hb_def : b = z.im := rfl
  have hs_def : s = complex_sqrt_real_part a b := rfl
  have hq_def : q = complex_sqrt_imag_part a b := rfl
  simp only [QuadraticAlgebra.sqrt, ← ha_def, ← hb_def, ← hs_def, ← hq_def]
  constructor
  · by_cases hb : 0 ≤ b <;> simp [hb, hreal]
  · exact himag

/-- The chosen square root squares to its input. -/
@[simp]
theorem _root_.QuadraticAlgebra.sq_sqrt
    (z : QuadraticAlgebra R (-1) 0) : z.sqrt ^ 2 = z := by
  rw [pow_two]
  obtain ⟨hre, him⟩ := QuadraticAlgebra.sqrt_coordinates z
  have hmul : z = z.sqrt * z.sqrt := by
    apply QuadraticAlgebra.ext
    · simp only [QuadraticAlgebra.re_mul]
      linear_combination -hre
    · simp only [QuadraticAlgebra.im_mul]
      linear_combination -him
  exact hmul.symm

omit [LinearOrder R] [IsStrictOrderedRing R] in
/-- Every element of `R[i]` is a square when `R` is real closed, without choosing an order. -/
theorem isSquare (z : QuadraticAlgebra R (-1) 0) : IsSquare z := by
  obtain ⟨o, ho⟩ := IsSemireal.exists_linearOrder (K := R)
  let := o
  have := ho
  use z.sqrt
  simpa [pow_two] using (QuadraticAlgebra.sq_sqrt z).symm

end QuadraticAlgebra
