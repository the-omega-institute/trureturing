/- GID: D5/S3/Analytic/Characterizations/ShiftedHerglotzCriterion
   generality: G
   mirror-B: D5/B/S3/Analytic/Characterizations/ShiftedHerglotzCriterion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Positive Cayley scaling equates Schur and Herglotz maps with degenerate audits. -/
/- Library-search audit trail (2026-08-25): repository searches by object name,
digest, Cayley body, nearby module, general shape, and alternate vocabulary found no
equivalent declaration. Loogle type-shape searches for the imaginary-part identity and
the Schur/Herglotz equivalence returned no hits. Two matching LeanSearch API requests
failed with exit code 1, so no search-completeness claim is made. Pinned Mathlib source
search found `UpperHalfPlane.upperHalfPlaneSet`, complex division differentiation, and
`continuousAt_update_same`, but no packaged Herglotz or Schur Cayley criterion. -/

import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Topology.Piecewise
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Analytic.Characterizations.ShiftedHerglotzCriterion

open Complex

/-- A holomorphic map of the upper half-plane whose values have norm at most one. -/
def IsSchurOnUpperHalfPlane (theta : Complex → Complex) : Prop :=
  DifferentiableOn Complex theta UpperHalfPlane.upperHalfPlaneSet ∧
    ∀ z ∈ UpperHalfPlane.upperHalfPlaneSet, ‖theta z‖ ≤ 1

/-- A holomorphic map of the upper half-plane with nonnegative imaginary part. -/
def IsHerglotzOnUpperHalfPlane (m : Complex → Complex) : Prop :=
  DifferentiableOn Complex m UpperHalfPlane.upperHalfPlaneSet ∧
    ∀ z ∈ UpperHalfPlane.upperHalfPlaneSet, 0 ≤ (m z).im

/-- The value Cayley transform from the source, including its positive scale. -/
noncomputable def shiftedCayleyTransform (omega : Real) (u : Complex) : Complex :=
  (I / (omega : Complex)) * ((1 - u) / (1 + u))

/-- The exact imaginary part of the shifted Cayley transform. -/
theorem shifted_cayley_imaginary_part
    (omega : Real) (u : Complex) :
    (shiftedCayleyTransform omega u).im =
      (1 - Complex.normSq u) / (omega * Complex.normSq (1 + u)) := by
  by_cases homega : omega = 0
  · subst omega
    simp [shiftedCayleyTransform]
  by_cases hden : 1 + u = 0
  · simp [hden, shiftedCayleyTransform]
  have homegaC : (omega : Complex) ≠ 0 := Complex.ofReal_ne_zero.mpr homega
  have hnorm : Complex.normSq (1 + u) ≠ 0 := mt Complex.normSq_eq_zero.mp hden
  unfold shiftedCayleyTransform
  rw [Complex.mul_im, Complex.div_re, Complex.div_im, Complex.div_re,
    Complex.div_im]
  simp only [I_re, I_im, ofReal_re, ofReal_im, zero_mul, one_mul, add_zero,
    one_re, one_im, sub_re, sub_im, add_re, add_im, normSq_apply]
  field_simp [homega, hnorm]
  ring
#print axioms shifted_cayley_imaginary_part

private lemma shifted_cayley_nonnegative_imaginary_part_iff
    (omega : Real) (u : Complex) (homega : 0 < omega) :
    0 ≤ (shiftedCayleyTransform omega u).im ↔ ‖u‖ ≤ 1 := by
  by_cases hden : 1 + u = 0
  · have hu : u = -1 := by linear_combination hden
    subst u
    norm_num [shiftedCayleyTransform]
  rw [shifted_cayley_imaginary_part omega u]
  have hdenPos : 0 < omega * Complex.normSq (1 + u) :=
    mul_pos homega (Complex.normSq_pos.mpr hden)
  constructor
  · intro hquotient
    have hnumerator : 0 ≤ 1 - Complex.normSq u := by
      have hproduct := mul_nonneg hquotient hdenPos.le
      rw [div_mul_cancel₀ _ hdenPos.ne'] at hproduct
      exact hproduct
    have hsquare : ‖u‖ ^ 2 ≤ (1 : Real) ^ 2 := by
      rw [Complex.sq_norm]
      nlinarith
    exact (sq_le_sq₀ (norm_nonneg u) zero_le_one).mp hsquare
  · intro hnorm
    apply div_nonneg
    · rw [← Complex.sq_norm]
      nlinarith [norm_nonneg u]
    · exact hdenPos.le

/-- Strict Herglotz positivity is exactly the strict disk inequality. -/
theorem shifted_cayley_positive_imaginary_part
    (omega : Real) (u : Complex) (homega : 0 < omega) :
    0 < (shiftedCayleyTransform omega u).im ↔ ‖u‖ < 1 := by
  by_cases hden : 1 + u = 0
  · have hu : u = -1 := by linear_combination hden
    subst u
    norm_num [shiftedCayleyTransform]
  rw [shifted_cayley_imaginary_part omega u]
  have hdenPos : 0 < omega * Complex.normSq (1 + u) :=
    mul_pos homega (Complex.normSq_pos.mpr hden)
  rw [div_pos_iff_of_pos_right hdenPos]
  rw [← Complex.sq_norm]
  constructor <;> intro h <;> nlinarith [norm_nonneg u]
#print axioms shifted_cayley_positive_imaginary_part

private noncomputable def inverseShiftedCayleyTransform
    (omega : Real) (m : Complex → Complex) (z : Complex) : Complex :=
  (I - (omega : Complex) * m z) / (I + (omega : Complex) * m z)

/-- Positive shifted Cayley scaling equates the Schur and Herglotz properties. -/
theorem shifted_herglotz_criterion
    (omega : Real) (theta : Complex → Complex) (homega : 0 < omega)
    (hden : ∀ z ∈ UpperHalfPlane.upperHalfPlaneSet, 1 + theta z ≠ 0) :
    IsHerglotzOnUpperHalfPlane
        (fun z => shiftedCayleyTransform omega (theta z)) ↔
      IsSchurOnUpperHalfPlane theta := by
  constructor
  · rintro ⟨hmDiff, hmIm⟩
    have hinverseDen : ∀ z ∈ UpperHalfPlane.upperHalfPlaneSet,
        I + (omega : Complex) * shiftedCayleyTransform omega (theta z) ≠ 0 := by
      intro z hz hzero
      have him := congrArg Complex.im hzero
      simp only [Complex.add_im, I_im, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, add_zero, Complex.zero_im] at him
      have hnonneg := hmIm z hz
      nlinarith
    have hconstant : DifferentiableOn Complex (fun _z : Complex => I)
        UpperHalfPlane.upperHalfPlaneSet := differentiableOn_const I
    have hscaled : DifferentiableOn Complex
        (fun z => (omega : Complex) * shiftedCayleyTransform omega (theta z))
        UpperHalfPlane.upperHalfPlaneSet :=
      (differentiableOn_const (omega : Complex)).mul hmDiff
    have hinverseDiff : DifferentiableOn Complex
        (inverseShiftedCayleyTransform omega
          (fun z => shiftedCayleyTransform omega (theta z)))
        UpperHalfPlane.upperHalfPlaneSet := by
      exact (hconstant.sub hscaled).div (hconstant.add hscaled) hinverseDen
    have hrecover : ∀ z ∈ UpperHalfPlane.upperHalfPlaneSet,
        theta z = inverseShiftedCayleyTransform omega
          (fun w => shiftedCayleyTransform omega (theta w)) z := by
      intro z hz
      have homegaC : (omega : Complex) ≠ 0 :=
        Complex.ofReal_ne_zero.mpr homega.ne'
      have hdenz := hden z hz
      unfold inverseShiftedCayleyTransform shiftedCayleyTransform
      field_simp [homegaC, hdenz]
      ring
    refine ⟨hinverseDiff.congr hrecover, ?_⟩
    intro z hz
    exact (shifted_cayley_nonnegative_imaginary_part_iff omega (theta z)
      homega).mp (hmIm z hz)
  · rintro ⟨hthetaDiff, hthetaNorm⟩
    have hone : DifferentiableOn Complex (fun _z : Complex => (1 : Complex))
        UpperHalfPlane.upperHalfPlaneSet := differentiableOn_const 1
    have hquotient : DifferentiableOn Complex
        (fun z => (1 - theta z) / (1 + theta z))
        UpperHalfPlane.upperHalfPlaneSet := by
      exact (hone.sub hthetaDiff).div (hone.add hthetaDiff) hden
    have hscale : DifferentiableOn Complex
        (fun _z : Complex => I / (omega : Complex))
        UpperHalfPlane.upperHalfPlaneSet := differentiableOn_const _
    refine ⟨hscale.mul hquotient, ?_⟩
    intro z hz
    exact (shifted_cayley_nonnegative_imaginary_part_iff omega (theta z)
      homega).mpr (hthetaNorm z hz)
#print axioms shifted_herglotz_criterion

/-- Zero and negative scales give concrete failures of the two implications. -/
theorem positive_scale_is_necessary :
    IsHerglotzOnUpperHalfPlane
        (fun _z => shiftedCayleyTransform 0 (2 : Complex)) ∧
      (¬ IsSchurOnUpperHalfPlane (fun _z => (2 : Complex))) ∧
      IsSchurOnUpperHalfPlane (fun _z => (0 : Complex)) ∧
      (¬ IsHerglotzOnUpperHalfPlane
        (fun _z => shiftedCayleyTransform (-1) (0 : Complex))) := by
  constructor
  · constructor
    · simp [shiftedCayleyTransform]
    · simp [shiftedCayleyTransform]
  constructor
  · intro hschur
    have hbound := hschur.2 I (by simp [UpperHalfPlane.upperHalfPlaneSet])
    norm_num at hbound
  constructor
  · exact ⟨differentiableOn_const 0, by simp⟩
  · intro hherglotz
    have hbound := hherglotz.2 I (by simp [UpperHalfPlane.upperHalfPlaneSet])
    norm_num [shiftedCayleyTransform, Complex.div_im] at hbound
#print axioms positive_scale_is_necessary

/-- Omitting denominator nonvanishing lets totalized division hide discontinuity. -/
theorem denominator_nonvanishing_is_necessary :
    let theta : Complex → Complex :=
      Function.update (fun _z : Complex => 1) I (-1)
    IsHerglotzOnUpperHalfPlane
        (fun z => shiftedCayleyTransform 1 (theta z)) ∧
      ¬ IsSchurOnUpperHalfPlane theta ∧
      ¬ ∀ z ∈ UpperHalfPlane.upperHalfPlaneSet, 1 + theta z ≠ 0 := by
  dsimp only
  let theta : Complex → Complex :=
    Function.update (fun _z : Complex => 1) I (-1)
  have hshift :
      (fun z => shiftedCayleyTransform 1 (theta z)) = fun _z => 0 := by
    funext z
    by_cases hz : z = I
    · simp [theta, hz, shiftedCayleyTransform]
    · simp [theta, hz, shiftedCayleyTransform]
  constructor
  · rw [hshift]
    exact ⟨differentiableOn_const 0, by simp⟩
  constructor
  · intro hschur
    have hI : I ∈ UpperHalfPlane.upperHalfPlaneSet := by
      simp [UpperHalfPlane.upperHalfPlaneSet]
    have hcont :=
      ((hschur.1 I hI).differentiableAt
        (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds hI)).continuousAt
    change ContinuousAt
      (Function.update (fun _z : Complex => 1) I (-1)) I at hcont
    rw [continuousAt_update_same] at hcont
    have hone : (1 : Complex) = -1 := by
      simpa only [tendsto_const_nhds_iff] using hcont
    norm_num at hone
  · intro hden
    have := hden I (by simp [UpperHalfPlane.upperHalfPlaneSet])
    simp at this
#print axioms denominator_nonvanishing_is_necessary

/-- Constant, identity, and division-by-zero inputs expose the totalized edge cases. -/
theorem degenerate_function_audit :
    IsSchurOnUpperHalfPlane (fun _z => (-1 : Complex)) ∧
      (¬ ∀ z ∈ UpperHalfPlane.upperHalfPlaneSet,
        1 + (fun _w => (-1 : Complex)) z ≠ 0) ∧
      IsHerglotzOnUpperHalfPlane
        (fun _z => shiftedCayleyTransform 1 (-1 : Complex)) ∧
      (¬ IsSchurOnUpperHalfPlane id) := by
  constructor
  · exact ⟨differentiableOn_const (-1), by simp⟩
  constructor
  · intro hden
    exact (hden I (by simp [UpperHalfPlane.upperHalfPlaneSet])) (by norm_num)
  constructor
  · constructor
    · simp [shiftedCayleyTransform]
    · simp [shiftedCayleyTransform]
  · intro hidentity
    let z : Complex := 2 * I
    have hz : z ∈ UpperHalfPlane.upperHalfPlaneSet := by
      simp [z, UpperHalfPlane.upperHalfPlaneSet]
    have hbound := hidentity.2 z hz
    simp [z] at hbound
#print axioms degenerate_function_audit

end D5.S3.Analytic.Characterizations.ShiftedHerglotzCriterion
