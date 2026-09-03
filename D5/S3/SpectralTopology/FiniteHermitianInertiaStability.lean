/- GID: D5/S3/SpectralTopology/FiniteHermitianInertiaStability
   generality: G
   mirror-B: D5/B/S3/SpectralTopology/FiniteHermitianInertiaStability
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Two-sided Weyl certificates preserve finite Hermitian inertia. -/

import D5.S3.SpectralTopology.PointGapExactInertia
import D5.S3.Weil.ZetaLinear.Weyl
import Mathlib.Tactic.Abel

/-!
# Quantitative stability of finite Hermitian inertia

For finite Hermitian matrices `A` and `E`, Weyl's thresholded count bounds
supply one-sided control of the positive index of `A + E`. Applying the same
bound to the reverse perturbation and to the negated matrices supplies
one-sided control of both positive and negative inertia.

If `A` and `A + E` are invertible, both inertia sums equal the full carrier
dimension. Hence the two lower bounds force equality of the positive and
negative counts.

The theorem is phrased through explicit certificates:

* the spectrum of `A` has no positive or negative eigenvalue in the threshold
  strip `(0, theta]`;
* the eigenvalues of `E` and `-E` are bounded in absolute value by `theta`;
* both endpoints are invertible.

This gives a finite quantitative inertia-continuation principle without using
an unformalized general eigenvalue-continuity theorem.
-/

/- Library-search audit trail (2026-09-03):
   * `RHLinalg.weyl_posIndexAbove_le` owns the one-sided thresholded positive
     index perturbation bound.
   * `PointGapExactInertia.posIndex_add_negIndex_eq_rank` owns the partition of
     nonzero Hermitian eigenvalues into positive and negative inertia.
   * `FiniteSpectralLocalizer.posIndex_neg_eq_negIndex` owns the conversion of
     negative inertia into the positive index of the negated matrix.
   * Pinned Mathlib supplies full rank of a unit matrix and cancellative
     arithmetic for natural-number sums.
   * Repository search found no existing owner combining these ingredients
     into a two-sided finite inertia stability theorem. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Matrix

namespace D5.S3.SpectralTopology.FiniteHermitianInertiaStability

open RHLinalg
open D5.S3.SpectralTopology.FiniteSpectralLocalizer
open D5.S3.SpectralTopology.PointGapExactInertia

noncomputable section

universe u

/-- Every eigenvalue of a Hermitian perturbation lies in the closed radius
`theta`. -/
def HasEigenvalueRadiusBound
    {K m : Type*} [RCLike K] [Fintype m] [DecidableEq m]
    {E : Matrix m m K} (hE : E.IsHermitian) (theta : ℝ) : Prop :=
  ∀ i, |hE.eigenvalues i| ≤ theta

/-- The radius certificate is supplied separately for a perturbation and its
negative, avoiding any dependence on a particular eigenvalue enumeration. -/
def HasTwoSidedEigenvalueRadiusBound
    {K m : Type*} [RCLike K] [Fintype m] [DecidableEq m]
    {E : Matrix m m K} (hE : E.IsHermitian) (theta : ℝ) : Prop :=
  HasEigenvalueRadiusBound hE theta ∧
    HasEigenvalueRadiusBound hE.neg theta

/-- A threshold gap means that raising the positive counting threshold from
zero to `theta` removes no positive eigenvalues. -/
def HasPositiveThresholdGap
    {K m : Type*} [RCLike K] [Fintype m] [DecidableEq m]
    {A : Matrix m m K} (hA : A.IsHermitian) (theta : ℝ) : Prop :=
  posIndexAbove hA theta = posIndex hA

/-- A two-sided threshold gap excludes positive eigenvalues of `A` and of
`-A` from the threshold strip next to zero. -/
def HasTwoSidedThresholdGap
    {K m : Type*} [RCLike K] [Fintype m] [DecidableEq m]
    {A : Matrix m m K} (hA : A.IsHermitian) (theta : ℝ) : Prop :=
  HasPositiveThresholdGap hA theta ∧
    HasPositiveThresholdGap hA.neg theta

/-- A threshold gap for `A`, together with a radius bound for the reverse
perturbation, prevents the positive index from decreasing. -/
theorem posIndex_le_add_of_threshold_gap
    {K m : Type*} [RCLike K] [Fintype m] [DecidableEq m]
    {A E : Matrix m m K}
    (hA : A.IsHermitian) (hE : E.IsHermitian) {theta : ℝ}
    (hGap : HasPositiveThresholdGap hA theta)
    (hBound : HasEigenvalueRadiusBound hE.neg theta) :
    posIndex hA ≤ posIndex (hA.add hE) := by
  have hWeyl :=
    weyl_posIndexAbove_le (hA.add hE) hE.neg hBound
  have hMatrix : (A + E) + (-E) = A := by
    abel
  rw [hMatrix] at hWeyl
  simpa only [HasPositiveThresholdGap, hGap] using hWeyl

/-- A threshold gap for `-A`, together with a radius bound for `E`, prevents
the negative index from decreasing. -/
theorem negIndex_le_add_of_threshold_gap
    {K m : Type*} [RCLike K] [Fintype m] [DecidableEq m]
    {A E : Matrix m m K}
    (hA : A.IsHermitian) (hE : E.IsHermitian) {theta : ℝ}
    (hGap : HasPositiveThresholdGap hA.neg theta)
    (hBound : HasEigenvalueRadiusBound hE theta) :
    negIndex hA ≤ negIndex (hA.add hE) := by
  have hWeyl :=
    weyl_posIndexAbove_le (hA.add hE).neg hE hBound
  have hMatrix : -(A + E) + E = -A := by
    abel
  rw [hMatrix] at hWeyl
  have hPositive : posIndex hA.neg ≤ posIndex (hA.add hE).neg := by
    simpa only [HasPositiveThresholdGap, hGap] using hWeyl
  calc
    negIndex hA = posIndex hA.neg :=
      (posIndex_neg_eq_negIndex hA).symm
    _ ≤ posIndex (hA.add hE).neg := hPositive
    _ = negIndex (hA.add hE) :=
      posIndex_neg_eq_negIndex (hA.add hE)

/-- Two-sided Weyl certificates and invertible endpoints force equality of
both finite Hermitian inertia counts. -/
theorem inertia_eq_of_two_sided_weyl_certificate
    {K m : Type*} [RCLike K] [Fintype m] [DecidableEq m]
    {A E : Matrix m m K}
    (hA : A.IsHermitian) (hE : E.IsHermitian) {theta : ℝ}
    (hAUnit : IsUnit A)
    (hAddUnit : IsUnit (A + E))
    (hGap : HasTwoSidedThresholdGap hA theta)
    (hBound : HasTwoSidedEigenvalueRadiusBound hE theta) :
    posIndex (hA.add hE) = posIndex hA ∧
      negIndex (hA.add hE) = negIndex hA := by
  have hPositive : posIndex hA ≤ posIndex (hA.add hE) :=
    posIndex_le_add_of_threshold_gap hA hE hGap.1 hBound.2
  have hNegative : negIndex hA ≤ negIndex (hA.add hE) :=
    negIndex_le_add_of_threshold_gap hA hE hGap.2 hBound.1
  have hTotalA :
      posIndex hA + negIndex hA = Fintype.card m := by
    calc
      posIndex hA + negIndex hA = A.rank :=
        posIndex_add_negIndex_eq_rank hA
      _ = Fintype.card m := Matrix.rank_of_isUnit A hAUnit
  have hTotalAdd :
      posIndex (hA.add hE) + negIndex (hA.add hE) =
        Fintype.card m := by
    calc
      posIndex (hA.add hE) + negIndex (hA.add hE) = (A + E).rank :=
        posIndex_add_negIndex_eq_rank (hA.add hE)
      _ = Fintype.card m := Matrix.rank_of_isUnit (A + E) hAddUnit
  have hPositiveReverse :
      posIndex (hA.add hE) ≤ posIndex hA := by
    apply Nat.le_of_add_le_add_right
    calc
      posIndex (hA.add hE) + negIndex hA ≤
          posIndex (hA.add hE) + negIndex (hA.add hE) :=
        Nat.add_le_add_left hNegative _
      _ = Fintype.card m := hTotalAdd
      _ = posIndex hA + negIndex hA := hTotalA.symm
  have hNegativeReverse :
      negIndex (hA.add hE) ≤ negIndex hA := by
    apply Nat.le_of_add_le_add_left
    calc
      posIndex hA + negIndex (hA.add hE) ≤
          posIndex (hA.add hE) + negIndex (hA.add hE) :=
        Nat.add_le_add_right hPositive _
      _ = Fintype.card m := hTotalAdd
      _ = posIndex hA + negIndex hA := hTotalA.symm
  exact ⟨Nat.le_antisymm hPositiveReverse hPositive,
    Nat.le_antisymm hNegativeReverse hNegative⟩

/-- Over the complex numbers, the same certificate preserves the repository's
existing Hermitian signature coordinate. -/
theorem hermitianSignature_add_eq_of_two_sided_weyl_certificate
    {m : Type u} [Fintype m] [DecidableEq m]
    {A E : Matrix m m ℂ}
    (hA : A.IsHermitian) (hE : E.IsHermitian) {theta : ℝ}
    (hAUnit : IsUnit A)
    (hAddUnit : IsUnit (A + E))
    (hGap : HasTwoSidedThresholdGap hA theta)
    (hBound : HasTwoSidedEigenvalueRadiusBound hE theta) :
    hermitianSignature (hA.add hE) = hermitianSignature hA := by
  obtain ⟨hPositive, hNegative⟩ :=
    inertia_eq_of_two_sided_weyl_certificate
      hA hE hAUnit hAddUnit hGap hBound
  unfold hermitianSignature
  rw [hPositive, hNegative]

#print axioms posIndex_le_add_of_threshold_gap
#print axioms negIndex_le_add_of_threshold_gap
#print axioms inertia_eq_of_two_sided_weyl_certificate
#print axioms hermitianSignature_add_eq_of_two_sided_weyl_certificate

end

end D5.S3.SpectralTopology.FiniteHermitianInertiaStability
