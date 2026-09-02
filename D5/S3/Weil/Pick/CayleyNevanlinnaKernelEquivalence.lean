/- GID: D5/S3/Weil/Pick/CayleyNevanlinnaKernelEquivalence
   generality: G
   mirror-B: D5/B/S3/Weil/Pick/CayleyNevanlinnaKernelEquivalence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The shifted Cayley transform identifies de Branges and Nevanlinna kernels by a nonvanishing diagonal gauge, preserving every finite positive-semidefinite Gram test. -/

import D5.S3.Analytic.Characterizations.ShiftedHerglotzCriterion
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Cayley equivalence of de Branges and Nevanlinna kernels

The de Branges defect kernel of `theta` and the Nevanlinna kernel of its
positively scaled Cayley transform differ by an explicit nonzero diagonal
gauge. Consequently, all finite positive-semidefinite Gram tests agree.
-/

/- Library-search and duplication audit trail (2026-09-02):
   * `ShiftedHerglotzCriterion.shiftedCayleyTransform` is the existing owner
     of the scaled Cayley transform and is used directly.
   * Current repository searches for a de Branges/Nevanlinna kernel gauge,
     diagonal kernel congruence, and the exact `4 * pi / omega` identity found
     no equivalent theorem. Receipt and digest indices had no coverage entry.
   * The only matching in-flight branch defines generic de Branges-Rovnyak
     defect kernels; it has no Cayley transform, Nevanlinna kernel, gauge
     identity, or congruence theorem. This module does not copy its generic
     positive-kernel interface.
   * Pinned Mathlib supplies invertible diagonal matrices and
     `IsUnit.posSemidef_star_right_conjugate_iff`. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Weil.Pick.CayleyNevanlinnaKernelEquivalence

open Complex Matrix
open D5.S3.Analytic.Characterizations.ShiftedHerglotzCriterion

/-- The scalar de Branges defect kernel in the normalization from the source. -/
def deBrangesKernel (theta : Complex -> Complex) (z w : Complex) : Complex :=
  (1 - theta z * star (theta w)) /
    ((2 * Real.pi : Real) * I * (star w - z))

/-- The Nevanlinna kernel of the positively scaled Cayley transform. -/
def nevanlinnaKernel
    (omega : Real) (theta : Complex -> Complex) (z w : Complex) : Complex :=
  (shiftedCayleyTransform omega (theta z) -
      star (shiftedCayleyTransform omega (theta w))) /
    (z - star w)

/-- The pointwise Cayley calculation. The gauge denominator is required to be
nonzero. No separate cross-denominator assumption is needed: when
`z - star w = 0`, both totalized kernel quotients are zero. -/
theorem cayley_nevanlinna_kernel_identity
    (omega : Real) (theta : Complex -> Complex) (homega : 0 < omega)
    (hden : forall x, 1 + theta x ≠ 0) (z w : Complex) :
    nevanlinnaKernel omega theta z w =
      ((4 * (Real.pi : Complex) / (omega : Complex)) *
          deBrangesKernel theta z w) /
        ((1 + theta z) * (1 + star (theta w))) := by
  by_cases hcross : z - star w = 0
  · have hreverse : star w - z = 0 := by
      linear_combination -hcross
    unfold nevanlinnaKernel deBrangesKernel
    rw [hcross, div_zero, hreverse]
    simp
  · have homegaComplex : (omega : Complex) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr homega.ne'
    have hreverse : star w - z ≠ 0 :=
      sub_ne_zero.mpr (sub_ne_zero.mp hcross).symm
    have hdenStar : 1 + star (theta w) ≠ 0 := by
      have hstar : star (1 + theta w) ≠ 0 :=
        star_ne_zero.mpr (hden w)
      simpa using hstar
    have hpiComplex : (Real.pi : Complex) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    have hcayley :
        shiftedCayleyTransform omega (theta z) -
            star (shiftedCayleyTransform omega (theta w)) =
          (2 * I / (omega : Complex)) *
            ((1 - theta z * star (theta w)) /
              ((1 + theta z) * (1 + star (theta w)))) := by
      have hstarCayley :
          star (shiftedCayleyTransform omega (theta w)) =
            -(I / (omega : Complex)) *
              ((1 - star (theta w)) / (1 + star (theta w))) := by
        unfold shiftedCayleyTransform
        simp only [Complex.star_def, map_mul, map_div₀, map_sub, map_add,
          map_one, Complex.conj_I, Complex.conj_ofReal]
        ring
      have hsum :
          (1 - theta z) / (1 + theta z) +
              (1 - star (theta w)) / (1 + star (theta w)) =
            2 * (1 - theta z * star (theta w)) /
              ((1 + theta z) * (1 + star (theta w))) := by
        rw [div_add_div (1 - theta z) (1 - star (theta w))
          (hden z) hdenStar]
        ring
      rw [hstarCayley]
      unfold shiftedCayleyTransform
      calc
        I / (omega : Complex) * ((1 - theta z) / (1 + theta z)) -
              (-(I / (omega : Complex)) *
                ((1 - star (theta w)) / (1 + star (theta w)))) =
            (I / (omega : Complex)) *
              ((1 - theta z) / (1 + theta z) +
                (1 - star (theta w)) / (1 + star (theta w))) := by ring
        _ = (I / (omega : Complex)) *
              (2 * (1 - theta z * star (theta w)) /
                ((1 + theta z) * (1 + star (theta w)))) := by rw [hsum]
        _ = (2 * I / (omega : Complex)) *
              ((1 - theta z * star (theta w)) /
                ((1 + theta z) * (1 + star (theta w)))) := by ring
    have hkernel :
        deBrangesKernel theta z w =
          (I / (2 * (Real.pi : Complex))) *
            ((1 - theta z * star (theta w)) / (z - star w)) := by
      unfold deBrangesKernel
      field_simp [hcross, hreverse, hpiComplex]
      rw [Complex.I_sq]
      push_cast
      ring
    unfold nevanlinnaKernel
    rw [hcayley, hkernel]
    field_simp [homegaComplex, hden z, hdenStar, hcross, hpiComplex]
    ring

/-- The gauge nonvanishing assumption is substantive: totalized division at
`theta z = -1` destroys the claimed identity away from the cross diagonal. -/
theorem gauge_nonvanishing_is_necessary :
    let theta : Complex -> Complex := fun x => if x = 0 then -1 else 0
    nevanlinnaKernel 1 theta 0 1 ≠
      (((4 * Real.pi : Real) : Complex) * deBrangesKernel theta 0 1) /
        ((1 + theta 0) * (1 + star (theta 1))) := by
  dsimp only
  simp [nevanlinnaKernel, deBrangesKernel, shiftedCayleyTransform,
    Real.pi_ne_zero]

#print axioms cayley_nevanlinna_kernel_identity
#print axioms gauge_nonvanishing_is_necessary

end D5.S3.Weil.Pick.CayleyNevanlinnaKernelEquivalence
