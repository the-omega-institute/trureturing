/- GID: D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMNativeOccupation
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMNativeOccupation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Marked Taylor selection in the actual signed native Gaussian. -/

import D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMPhysicalCovariance

/-! Marked spatial Taylor selectors in the actual four-point affine Gaussian. -/

set_option autoImplicit false

noncomputable section
open Complex Filter
open scoped Topology BigOperators NNReal

namespace D5.S3.VertexAlgebra.TwistedGround.OriginalFourMNativeOccupation

open OriginalFourMSignedOverlap (signedHalfSource)

open LatticeGeneratingFieldLocality
open OriginalGaussianExternalBlocks (External explicitEffectiveKernel externalFreeEntry)
open OriginalGaussianSewnAnalytic (coefficient explicitMean)
open OriginalGaussianExternalResolvent (externalJ)
open LatticeHalfFock (gramComplex)
open OriginalFourMSignedOverlap (taggedMode covarianceMode native_tagged_entry native_mean_hasSum)
open NativeAffineExternalCoefficient (coordinateJet jetOccupation)
open OriginalChargedRowSource (affineCoefficient)
open FactorialFockMetric (weight)
open D5.S3.Analytic.OriginalHalfBinomialSlitPeriod (slitPeriod)
open private coefficient_of_hasSum from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMSignedOverlap

private def leg {J : Type*} : J ⊕ J → Bool
  | .inl _ => false
  | .inr _ => true

private def baseLabel {J : Type*} : J ⊕ J → J := Sum.elim id id

private theorem tag_baseLabel {J : Type*} (i : J ⊕ J) :
    taggedMode (leg i) (baseLabel i) = i := by cases i <;> rfl

private theorem explicit_covariance_symmetric (D : LatticeData) {J : Type*}
    (labels : J → External D) {w : ℂ} (hw : ‖w‖ < 1) (i j : J ⊕ J) :
    explicitEffectiveKernel D labels w i j = explicitEffectiveKernel D labels w j i := by
  have hfree (a b : External D) : externalFreeEntry D a b = externalFreeEntry D b a := by
    unfold externalFreeEntry
    by_cases h : a.1 = b.1
    · simp [h]
    · by_cases hm : a.2.2 = b.2.2
      · simp [h, Ne.symm h, hm]
      · simp [h, Ne.symm h, hm, Ne.symm hm]
  have hsame (i j : J) :
      gramComplex D (labels i).2.1 (labels j).2.1 *
        (externalFreeEntry D (labels i) (labels j) +
          externalJ (labels i).1 (labels i).2.2 (labels j).1 (labels j).2.2 w) =
      gramComplex D (labels j).2.1 (labels i).2.1 *
        (externalFreeEntry D (labels j) (labels i) +
          externalJ (labels j).1 (labels j).2.2 (labels i).1 (labels i).2.2 w) := by
    have hJ := OriginalGaussianExternalEquations.literal_symmetry false (labels i).1
      (labels j).1 (labels i).2.2 (labels j).2.2 hw
    simp only [Bool.false_eq_true, ite_false] at hJ
    rw [hfree, hJ]
    change (D.G (labels i).2.1 (labels j).2.1 : ℂ) * _ =
      (D.G (labels j).2.1 (labels i).2.1 : ℂ) * _
    rw [D.symmetric]
  cases i <;> cases j
  · exact hsame _ _
  · rfl
  · rfl
  · exact hsame _ _

private theorem mean_scalar_coefficient (D : LatticeData) (a : Charge D)
    (l e : Bool) (i : Fin D.rank) (n : ℕ) {w : ℂ} (hw : ‖w‖ < 1) :
    coefficient n (fun u => -(bilinear D (unitCharge D i) a : ℂ) *
        signedHalfSource l e u (w ^ 2) / slitPeriod (w ^ 2)) =
      explicitMean D a (fun _ : Unit => (e,i,n)) w (taggedMode l ()) := by
  let R : ℝ≥0 := ⟨(1 - ‖w‖) / 2, by linarith⟩
  have hR : 0 < R := by change 0 < (1 - ‖w‖) / 2; linarith
  have hR₀ : ‖(R : ℂ)‖ = (R : ℝ) := by simp
  refine coefficient_of_hasSum hR
    (native_mean_hasSum D a l e i (w := w) (u := (R : ℂ))
      (by rw [hR₀]; change (1 - ‖w‖)/2 + ‖w‖ < 1; linarith)).summable.norm ?_ n
  have hsmall : ∀ᶠ u : ℂ in 𝓝 0, ‖u‖ + ‖w‖ < 1 :=
    (isOpen_lt (continuous_norm.add continuous_const) continuous_const).mem_nhds (by simpa using hw)
  exact hsmall.mono fun u hu => native_mean_hasSum D a l e i hu

private def selectedCovariance (D : LatticeData) {J : Type*} (labels : J → External D)
    (w : ℂ) (i j : J ⊕ J) : ℂ :=
  let a := labels (baseLabel i)
  let b := labels (baseLabel j)
  coefficient b.2.2 (fun v => coefficient a.2.2 (fun u =>
    gramComplex D a.2.1 b.2.1 * covarianceMode (leg i) (leg j) a.1 b.1 u v (w ^ 2)))

private def selectedMean (D : LatticeData) (a : Charge D) {J : Type*}
    (labels : J → External D) (w : ℂ) (i : J ⊕ J) : ℂ :=
  let x := labels (baseLabel i)
  coefficient x.2.2 (fun u => -(bilinear D (unitCharge D x.2.1) a : ℂ) *
    signedHalfSource (leg i) x.1 u (w ^ 2) / slitPeriod (w ^ 2))

/-- The marked exponential of the signed spatial Taylor selectors is the
original affine occupation in the literal sewn Gaussian. Repeated marked
oscillators retain their original factorial weight. -/
theorem native_selected_occupation (D : LatticeData) (a : Charge D)
    {J X : Type*} [Fintype J] [Fintype X] [DecidableEq X]
    (labels : J → External D) (mode : X → J ⊕ J) (l : List X) {w : ℂ} (hw : ‖w‖ < 1) :
    let d := jetOccupation (l.map mode)
    coordinateJet l (fun t => Complex.exp (
      (1 / 2 : ℂ) * (∑ i, ∑ j, selectedCovariance D labels w (mode i) (mode j) * t i * t j) +
        ∑ i, selectedMean D a labels w (mode i) * t i)) 0 =
      (weight d : ℂ) * affineCoefficient (explicitEffectiveKernel D labels w)
        (explicitMean D a labels w) d := by
  classical
  have hk (i j : J ⊕ J) : selectedCovariance D labels w i j =
      explicitEffectiveKernel D labels w i j := by
    unfold selectedCovariance
    rw [← native_tagged_entry D labels (leg i) (leg j) (baseLabel i) (baseLabel j) hw,
      tag_baseLabel, tag_baseLabel]
  have hm (i : J ⊕ J) : selectedMean D a labels w i = explicitMean D a labels w i := by
    unfold selectedMean
    rw [mean_scalar_coefficient D a _ _ _ _ hw]
    cases i <;> rfl
  dsimp only
  simp only [hk, hm]
  exact OriginalFourMPhysicalCovariance.marked_gaussian_jet mode l _ _
    (explicit_covariance_symmetric D labels hw)

end D5.S3.VertexAlgebra.TwistedGround.OriginalFourMNativeOccupation
