/- GID: D5/S3/SpectralTopology/PointGapLocalizerInertiaStability
   generality: G
   mirror-B: D5/B/S3/SpectralTopology/PointGapLocalizerInertiaStability
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Point-gap Weyl certificates stabilize finite localizer inertia. -/

import D5.S3.SpectralTopology.FiniteHermitianInertiaStability
import D5.S3.SpectralTopology.PointGapRadialGapPath

/-!
# Inertia stability along a point-gap localizer path

The radial-gap node constructs an explicit Hermitian invertible path from the
zero-scale localizer to every scale inside the Neumann budget. The generic
finite-inertia node proves that an invertible Hermitian perturbation preserves
positive and negative inertia when supplied with a two-sided Weyl certificate.

This node composes both interfaces. A localizer Weyl certificate consists of:

* a two-sided threshold gap for the zero-scale localizer;
* a two-sided eigenvalue-radius bound for the scaled position direction.

Under a point gap and the explicit Neumann budget, this certificate identifies
the finite-scale inertia with the zero-scale inertia. The existing exact
counting theorem then gives

`n₊(Lκ) = n₋(Lκ) = Fintype.card n`

and therefore zero finite localizer signature. A uniform radius certificate
for every `t` in `[0,1]` upgrades the endpoint result to the whole radial path.

The threshold and radius certificates are explicit formal inputs. Deriving
them automatically from a computable singular-value or operator-norm margin is
a subsequent research node.
-/

/- Library-search audit trail (2026-09-03):
   * `PointGapRadialGapPath` owns the star-shaped admissible scale region and
     Hermitian invertibility of the radial path.
   * `FiniteHermitianInertiaStability` owns the two-sided Weyl inertia
     continuation theorem.
   * `PointGapExactInertia` owns the exact zero-scale chiral counts.
   * Repository search found no existing owner composing these three layers
     into finite-scale or radial-path localizer inertia stability. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Matrix Set
open scoped Matrix.Norms.L2Operator

namespace D5.S3.SpectralTopology.PointGapLocalizerInertiaStability

open RHLinalg
open D5.S3.SpectralTopology.FiniteSpectralLocalizer
open D5.S3.SpectralTopology.PointGapExactInertia
open D5.S3.SpectralTopology.PointGapFiniteScaleStability
open D5.S3.SpectralTopology.PointGapRadialGapPath
open D5.S3.SpectralTopology.FiniteHermitianInertiaStability

noncomputable section

universe u

variable {n : Type u} [Fintype n] [DecidableEq n]

/-- The Hermitian perturbation taking the zero-scale localizer to scale
`kappa`. -/
def localizerPositionPerturbation
    (X : Matrix n n ℂ) (kappa x : ℝ) :
    Matrix (n ⊕ n) (n ⊕ n) ℂ :=
  (kappa : ℂ) • positionDirection X x

/-- A real scale and a Hermitian position observable give a Hermitian
localizer perturbation. -/
theorem localizer_position_perturbation_isHermitian
    (X : Matrix n n ℂ) (kappa x : ℝ) (hX : X.IsHermitian) :
    (localizerPositionPerturbation X kappa x).IsHermitian := by
  unfold localizerPositionPerturbation
  exact (position_direction_isHermitian X x hX).smul
    (by rw [isSelfAdjoint_iff]; simp)

/-- The localizer-specific Weyl certificate at one finite scale. -/
def HasLocalizerWeylCertificate
    (X H : Matrix n n ℂ) (kappa x : ℝ) (z : ℂ)
    (hX : X.IsHermitian) (theta : ℝ) : Prop :=
  HasTwoSidedThresholdGap
      (finite_spectral_localizer_zero_scale_isHermitian X H x z) theta ∧
    HasTwoSidedEigenvalueRadiusBound
      (localizer_position_perturbation_isHermitian X kappa x hX) theta

/-- A uniform localizer Weyl certificate along the whole radial unit
segment. -/
def HasUniformRadialLocalizerWeylCertificate
    (X H : Matrix n n ℂ) (kappa x : ℝ) (z : ℂ)
    (hX : X.IsHermitian) (theta : ℝ) : Prop :=
  HasTwoSidedThresholdGap
      (finite_spectral_localizer_zero_scale_isHermitian X H x z) theta ∧
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasTwoSidedEigenvalueRadiusBound
        (localizer_position_perturbation_isHermitian X (t * kappa) x hX)
        theta

/-- The radial finite localizer signature. -/
def radialLocalizerSignature
    (X H : Matrix n n ℂ) (kappa x : ℝ) (z : ℂ)
    (hX : X.IsHermitian) (t : ℝ) : ℤ :=
  finiteLocalizerSignature X H (t * kappa) x z hX

/-- A one-scale Weyl certificate identifies finite-scale localizer inertia
with zero-scale inertia. -/
theorem finite_localizer_inertia_eq_zero_scale_of_weyl_certificate
    (X H : Matrix n n ℂ) (kappa x : ℝ) (z : ℂ)
    (hX : X.IsHermitian)
    (hAdmissible : IsAdmissibleScale X H kappa x z)
    (theta : ℝ)
    (hCertificate :
      HasLocalizerWeylCertificate X H kappa x z hX theta) :
    posIndex (finite_spectral_localizer_isHermitian X H kappa x z hX) =
        posIndex
          (finite_spectral_localizer_zero_scale_isHermitian X H x z) ∧
      negIndex (finite_spectral_localizer_isHermitian X H kappa x z hX) =
        negIndex
          (finite_spectral_localizer_zero_scale_isHermitian X H x z) := by
  have hZeroUnit : IsUnit (finiteSpectralLocalizer X H 0 x z) :=
    (has_point_gap_iff_zero_scale_localizer_isUnit X H x z).1
      hAdmissible.1
  have hFiniteUnit : IsUnit (finiteSpectralLocalizer X H kappa x z) := by
    apply finite_scale_localizer_isUnit_of_scale_bound
      X H kappa x z hAdmissible.1
    simpa only [scaleGapBudget] using hAdmissible.2
  have hDecomposition :
      finiteSpectralLocalizer X H 0 x z +
          localizerPositionPerturbation X kappa x =
        finiteSpectralLocalizer X H kappa x z := by
    symm
    simpa only [localizerPositionPerturbation] using
      finite_spectral_localizer_scale_decomposition X H kappa x z
  have hAddUnit :
      IsUnit
        (finiteSpectralLocalizer X H 0 x z +
          localizerPositionPerturbation X kappa x) := by
    rw [hDecomposition]
    exact hFiniteUnit
  have hCounts :=
    inertia_eq_of_two_sided_weyl_certificate
      (finite_spectral_localizer_zero_scale_isHermitian X H x z)
      (localizer_position_perturbation_isHermitian X kappa x hX)
      hZeroUnit hAddUnit hCertificate.1 hCertificate.2
  rw [hDecomposition] at hCounts
  simpa only using hCounts

/-- Under a point gap, an admissible scale and a localizer Weyl certificate
give exact half-dimensional inertia at finite scale. -/
theorem finite_localizer_exact_inertia_of_weyl_certificate
    (X H : Matrix n n ℂ) (kappa x : ℝ) (z : ℂ)
    (hX : X.IsHermitian)
    (hAdmissible : IsAdmissibleScale X H kappa x z)
    (theta : ℝ)
    (hCertificate :
      HasLocalizerWeylCertificate X H kappa x z hX theta) :
    posIndex (finite_spectral_localizer_isHermitian X H kappa x z hX) =
        Fintype.card n ∧
      negIndex (finite_spectral_localizer_isHermitian X H kappa x z hX) =
        Fintype.card n := by
  have hStable :=
    finite_localizer_inertia_eq_zero_scale_of_weyl_certificate
      X H kappa x z hX hAdmissible theta hCertificate
  have hZero :=
    zero_scale_localizer_inertia_of_point_gap X H x z hAdmissible.1
  exact ⟨hStable.1.trans hZero.1, hStable.2.trans hZero.2⟩

/-- The finite localizer signature vanishes under the same quantitative Weyl
certificate. -/
theorem finite_localizer_signature_eq_zero_of_weyl_certificate
    (X H : Matrix n n ℂ) (kappa x : ℝ) (z : ℂ)
    (hX : X.IsHermitian)
    (hAdmissible : IsAdmissibleScale X H kappa x z)
    (theta : ℝ)
    (hCertificate :
      HasLocalizerWeylCertificate X H kappa x z hX theta) :
    finiteLocalizerSignature X H kappa x z hX = 0 := by
  unfold finiteLocalizerSignature hermitianSignature
  obtain ⟨hPositive, hNegative⟩ :=
    finite_localizer_exact_inertia_of_weyl_certificate
      X H kappa x z hX hAdmissible theta hCertificate
  rw [hPositive, hNegative]
  simp

/-- A uniform radial Weyl certificate gives exact inertia at every point of
the admissible radial path. -/
theorem radial_localizer_exact_inertia_of_uniform_weyl_certificate
    (X H : Matrix n n ℂ) (kappa x : ℝ) (z : ℂ)
    (hX : X.IsHermitian)
    (hAdmissible : IsAdmissibleScale X H kappa x z)
    (theta : ℝ)
    (hCertificate :
      HasUniformRadialLocalizerWeylCertificate
        X H kappa x z hX theta) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      posIndex (radial_localizer_isHermitian X H kappa x t z hX) =
          Fintype.card n ∧
        negIndex (radial_localizer_isHermitian X H kappa x t z hX) =
          Fintype.card n := by
  intro t ht
  have hScaledAdmissible :
      IsAdmissibleScale X H (t * kappa) x z :=
    admissible_scale_radial X H kappa x t z hAdmissible ht.1 ht.2
  have hExact :=
    finite_localizer_exact_inertia_of_weyl_certificate
      X H (t * kappa) x z hX hScaledAdmissible theta
      ⟨hCertificate.1, hCertificate.2 t ht⟩
  simpa only [radialLocalizer] using hExact

/-- A uniform radial Weyl certificate makes the finite localizer signature
zero on the whole radial unit segment. -/
theorem radial_localizer_signature_eq_zero_of_uniform_weyl_certificate
    (X H : Matrix n n ℂ) (kappa x : ℝ) (z : ℂ)
    (hX : X.IsHermitian)
    (hAdmissible : IsAdmissibleScale X H kappa x z)
    (theta : ℝ)
    (hCertificate :
      HasUniformRadialLocalizerWeylCertificate
        X H kappa x z hX theta) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      radialLocalizerSignature X H kappa x z hX t = 0 := by
  intro t ht
  unfold radialLocalizerSignature
  have hScaledAdmissible :
      IsAdmissibleScale X H (t * kappa) x z :=
    admissible_scale_radial X H kappa x t z hAdmissible ht.1 ht.2
  exact finite_localizer_signature_eq_zero_of_weyl_certificate
    X H (t * kappa) x z hX hScaledAdmissible theta
    ⟨hCertificate.1, hCertificate.2 t ht⟩

#print axioms localizer_position_perturbation_isHermitian
#print axioms finite_localizer_inertia_eq_zero_scale_of_weyl_certificate
#print axioms finite_localizer_exact_inertia_of_weyl_certificate
#print axioms finite_localizer_signature_eq_zero_of_weyl_certificate
#print axioms radial_localizer_exact_inertia_of_uniform_weyl_certificate
#print axioms radial_localizer_signature_eq_zero_of_uniform_weyl_certificate

end

end D5.S3.SpectralTopology.PointGapLocalizerInertiaStability
