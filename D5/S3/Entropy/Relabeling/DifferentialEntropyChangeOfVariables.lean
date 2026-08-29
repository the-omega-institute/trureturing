/- GID: D5/S3/Entropy/Relabeling/DifferentialEntropyChangeOfVariables
   generality: G
   mirror-B: D5/B/S3/Entropy/Relabeling/DifferentialEntropyChangeOfVariables
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Differential entropy gains expected log Jacobian; a constant Jacobian gives log c. -/

import D5.S3.Entropy.Relabeling.InjectiveInvariance
import Mathlib.MeasureTheory.Function.Jacobian

/- Library-search audit trail (2026-08-29):
   * Current-tree name and body-shape searches found no D5 theorem constructing
     a transformed density and proving the differential-entropy Jacobian law.
     No `def` or `abbrev` is introduced here.
   * Pinned Mathlib has no differential-entropy theorem, but its
     `integral_image_eq_integral_abs_det_fderiv_smul` and
     `integrableOn_image_iff_integrableOn_abs_det_fderiv_smul` are the exact
     change-of-variables primitives used below.
   * The source's qualitative observation that the correction is generally
     map- and distribution-dependent is not promoted to a universal clause. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Set

namespace D5.S3.Entropy.Relabeling.DifferentialEntropyChangeOfVariables

/-- **Differential entropy change of variables.** A nonnegative normalized density on
`Fin n -> Real`, a differentiable equivalence, and an everywhere-positive absolute Jacobian
determinant construct the transformed density by division through that determinant. Finite source
entropy and finite density-weighted log-Jacobian expectation imply that the transformed entropy
integrand is integrable and that its entropy gains exactly the expected log-Jacobian correction.

If the absolute determinant is the positive constant `c` on the support of the density, the
correction is `log c`. The positive-real subtype exposes the source condition `c > 0` without an
unused premise. -/
theorem differential_entropy_change_of_variables
    (n : Nat)
    (density : (Fin n -> Real) -> Real)
    (f : (Fin n -> Real) ≃ (Fin n -> Real))
    (derivative : (Fin n -> Real) -> ((Fin n -> Real) →L[Real] (Fin n -> Real)))
    (density_nonnegative : forall x, 0 <= density x)
    (density_mass : (∫ x, density x) = 1)
    (entropy_integrable : Integrable (fun x => density x * Real.log (density x)))
    (logJacobian_integrable : Integrable (fun x =>
      density x * Real.log |(derivative x).det|))
    (hasDerivative : forall x, HasFDerivAt (fun y => f y) (derivative x) x)
    (jacobian_positive : forall x, 0 < |(derivative x).det|) :
    let jacobian := fun x => |(derivative x).det|
    let transformedDensity := fun y => density (f.symm y) / jacobian (f.symm y)
    let differentialEntropy := fun p : (Fin n -> Real) -> Real =>
      -(∫ x, p x * Real.log (p x))
    Integrable (fun y => transformedDensity y * Real.log (transformedDensity y)) ∧
      differentialEntropy transformedDensity =
        differentialEntropy density + ∫ x, density x * Real.log (jacobian x) ∧
      forall c : {c : Real // 0 < c},
        (forall x, x ∈ Function.support density -> jacobian x = c.1) ->
          (∫ x, density x * Real.log (jacobian x)) = Real.log c.1 := by
  let jacobian := fun x : Fin n -> Real => |(derivative x).det|
  let transformedDensity := fun y : Fin n -> Real =>
    density (f.symm y) / jacobian (f.symm y)
  let differentialEntropy := fun p : (Fin n -> Real) -> Real =>
    -(∫ x, p x * Real.log (p x))
  change Integrable (fun y => transformedDensity y * Real.log (transformedDensity y)) ∧
    differentialEntropy transformedDensity =
      differentialEntropy density + ∫ x, density x * Real.log (jacobian x) ∧
    forall c : {c : Real // 0 < c},
      (forall x, x ∈ Function.support density -> jacobian x = c.1) ->
        (∫ x, density x * Real.log (jacobian x)) = Real.log c.1
  have entropyIntegrand (x : Fin n -> Real) :
      jacobian x *
          (transformedDensity (f x) * Real.log (transformedDensity (f x))) =
        density x * Real.log (density x) - density x * Real.log (jacobian x) := by
    simp only [transformedDensity, f.symm_apply_apply]
    by_cases densityZero : density x = 0
    · simp [densityZero]
    · have densityPositive : 0 < density x :=
        lt_of_le_of_ne (density_nonnegative x) (Ne.symm densityZero)
      have jacobianNe : jacobian x ≠ 0 := (jacobian_positive x).ne'
      rw [Real.log_div densityPositive.ne' jacobianNe]
      field_simp [jacobianNe]
  have changeOfVariables (g : (Fin n -> Real) -> Real) :
      (∫ y, g y) = ∫ x, jacobian x * g (f x) := by
    simpa [jacobian, smul_eq_mul] using
      (integral_image_eq_integral_abs_det_fderiv_smul
        (μ := volume) (s := Set.univ) (f := fun x => f x) (f' := derivative)
        MeasurableSet.univ
        (fun x _ => (hasDerivative x).hasFDerivWithinAt)
        f.injective.injOn g)
  have weightedEntropyIntegrable : Integrable (fun x =>
      jacobian x *
        (transformedDensity (f x) * Real.log (transformedDensity (f x)))) := by
    exact (entropy_integrable.sub logJacobian_integrable).congr
      (Filter.Eventually.of_forall fun x => (entropyIntegrand x).symm)
  have transformedEntropyIntegrable : Integrable (fun y =>
      transformedDensity y * Real.log (transformedDensity y)) := by
    have imageIntegrable : IntegrableOn
        (fun y => transformedDensity y * Real.log (transformedDensity y))
        ((fun x => f x) '' (Set.univ : Set (Fin n -> Real))) volume :=
      (integrableOn_image_iff_integrableOn_abs_det_fderiv_smul
        (μ := volume) (s := Set.univ) (f := fun x => f x) (f' := derivative)
        MeasurableSet.univ
        (fun x _ => (hasDerivative x).hasFDerivWithinAt)
        f.injective.injOn
        (fun y => transformedDensity y * Real.log (transformedDensity y))).2 (by
          simpa [jacobian, smul_eq_mul] using weightedEntropyIntegrable)
    simpa [Set.image_univ, f.surjective] using imageIntegrable
  have transformedIntegral :
      (∫ y, transformedDensity y * Real.log (transformedDensity y)) =
        (∫ x, density x * Real.log (density x)) -
          ∫ x, density x * Real.log (jacobian x) := by
    calc
      (∫ y, transformedDensity y * Real.log (transformedDensity y)) =
          ∫ x, jacobian x *
            (transformedDensity (f x) * Real.log (transformedDensity (f x))) :=
        changeOfVariables _
      _ = ∫ x, density x * Real.log (density x) -
          density x * Real.log (jacobian x) :=
        integral_congr_ae (Filter.Eventually.of_forall entropyIntegrand)
      _ = (∫ x, density x * Real.log (density x)) -
          ∫ x, density x * Real.log (jacobian x) :=
        integral_sub entropy_integrable logJacobian_integrable
  refine ⟨transformedEntropyIntegrable, ?_, ?_⟩
  · simp only [differentialEntropy]
    rw [transformedIntegral]
    ring
  · intro c constantJacobian
    calc
      (∫ x, density x * Real.log (jacobian x)) =
          ∫ x, density x * Real.log c.1 := by
        apply integral_congr_ae
        filter_upwards [] with x
        by_cases densityZero : density x = 0
        · simp [densityZero]
        · have supportMembership : x ∈ Function.support density := densityZero
          rw [constantJacobian x supportMembership]
      _ = (∫ x, density x) * Real.log c.1 := integral_mul_const _ _
      _ = Real.log c.1 := by rw [density_mass, one_mul]

end D5.S3.Entropy.Relabeling.DifferentialEntropyChangeOfVariables
