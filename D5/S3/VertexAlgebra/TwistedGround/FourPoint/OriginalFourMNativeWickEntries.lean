/- GID: D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMNativeWickEntries
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMNativeWickEntries
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Native chart mean and covariance after finite inverse jet substitution. -/

import D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMSpatialWickPartition
import D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMBivariateInverseJets
import D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMDFourCurrent

/-! The surviving affine Wick factors use the original A and B slit entries
and the actual D lip entries after finite inverse coordinate substitution. -/

set_option autoImplicit false
noncomputable section
open scoped Topology BigOperators
open Filter

namespace D5.S3.VertexAlgebra.TwistedGround.OriginalFourMNativeWickEntries

open LatticeGeneratingFieldLocality LatticeHalfFock
open FourPoint.OriginalFourMActualChart
open OriginalFourMOccupationTransport (flags rawLocal physicalSource)
open OriginalFourMPhysicalCovariance (jac relative)
open OriginalFourMPhysicalProduct (physicalMean)
open OriginalFourMSignedOverlap (chartCovariance chart_covariance_analytic chosenChartSource legSign
  chosen_chart_source_eq_native chart_covariance_eq_native chosen_chart_source_at_zero)
open OriginalFourMChartProduct (chartPeriod)
open OriginalFourMSpatialWickPartition (nativeTaylor)
open OriginalFourMInverseJets (inverseJetWeight coefficient_comp_pair_div_jac
  coefficient_comp_rawLocal_div_halfJacobian)
open OriginalFourMSlitMean (slitMeanEntry slitCovarianceEntry coefficient_congr
  slitCovariance slitCovariance_eq_native slitMean_eq_sourceMode)
open D5.S3.Analytic.OriginalHalfBinomialSlitPeriod (slitPeriod)
open OriginalGaussianSewnAnalytic (coefficient)
open private nativeKernel from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMSpatialWickPartition
open private true_lip_source true_lip_covariance from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMDFourCurrent
open private dLipCovarianceEntry dLipMeanEntry from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMDLipChannel

private theorem pair_coeff_congr {f g : ℂ × ℂ → ℂ} (h : f =ᶠ[𝓝 (0, 0)] g) (a b : ℕ) :
    coefficient b (fun v => coefficient a (fun u => f (u, v))) =
      coefficient b (fun v => coefficient a (fun u => g (u, v))) := by
  obtain ⟨U, hU, V, hV, hUV⟩ := mem_nhds_prod_iff.mp h
  apply coefficient_congr _ b
  filter_upwards [hV] with v hv
  apply coefficient_congr _ a
  filter_upwards [hU] with u hu
  exact hUV ⟨hu, hv⟩

private theorem coeff_mul_left (a : ℕ) (k : ℂ) (f : ℂ → ℂ) :
    coefficient a (fun u => k * f u) = k * coefficient a f := by
  simp only [coefficient, iteratedDeriv_const_mul_field, mul_div_assoc]

private theorem coeff_mul_right (a : ℕ) (k : ℂ) (f : ℂ → ℂ) :
    coefficient a (fun u => f u * k) = coefficient a f * k := by
  simpa only [mul_comm] using coeff_mul_left a k f

private theorem nativeTaylor_eq (D : LatticeData) {X : Type*}
    (upperA : Bool) (c : Chart) {x : ℝ} (hx : 0 < x) (hx₁ : x < 1)
    (slot : X → Puncture) (colour : X → Fin D.rank) (n : X → ℕ) (i j : X)
    (V : ℕ → ℕ → ℂ)
    (hV : ∀ a b, coefficient b (fun v => coefficient a (fun u =>
      (D.G (colour i) (colour j) : ℂ) *
      chartCovariance upperA c x (flags c (slot i)).1 (flags c (slot j)).1
        (flags c (slot i)).2 (flags c (slot j)).2 u v)) = V a b) :
    nativeTaylor D upperA c x slot colour n i j =
      (relative c (slot i) * relative c (slot j)) *
        ∑ a ∈ Finset.range (n i + 1), ∑ b ∈ Finset.range (n j + 1),
          V a b * inverseJetWeight c x (slot i) (n i) a *
            inverseJetWeight c x (slot j) (n j) b := by
  let K (z : ℂ × ℂ) := (D.G (colour i) (colour j) : ℂ) *
    chartCovariance upperA c x (flags c (slot i)).1 (flags c (slot j)).1
      (flags c (slot i)).2 (flags c (slot j)).2 z.1 z.2
  have hK : AnalyticAt ℂ K (0, 0) :=
    analyticAt_const.mul (chart_covariance_analytic hx hx₁ upperA c _ _ _ _)
  have h := coefficient_comp_pair_div_jac hK hx hx₁ c (slot i) (slot j) (n i) (n j)
  have he (u v : ℂ) : nativeKernel D upperA c x slot colour i j u v =
      (K (rawLocal c x (slot i) u, rawLocal c x (slot j) v) /
        (jac c x (slot i) u * jac c x (slot j) v)) *
        (relative c (slot i) * relative c (slot j)) := by
    simp only [nativeKernel, K, div_eq_mul_inv]
    ring
  simp only [nativeTaylor, Matrix.of_apply, he, coeff_mul_right, h]
  simp only [K, hV]
  ring

/-- Both spatial degrees of a physical native A or B edge act on the
literal slit covariance entries by the two finite inverse jet weights. -/
theorem nativeTaylor_ab (D : LatticeData) {X : Type*}
    (upperA : Bool) (c : Chart) {x : ℝ} (hx : 0 < x) (hx₁ : x < 1)
    (hc : c = .A ∨ c = .B) (hr : ‖parameter c (x : ℂ)‖ < 1)
    (slot : X → Puncture) (colour : X → Fin D.rank) (n : X → ℕ) (i j : X) :
    nativeTaylor D upperA c x slot colour n i j =
      (relative c (slot i) * relative c (slot j)) *
        ∑ a ∈ Finset.range (n i + 1), ∑ b ∈ Finset.range (n j + 1),
          slitCovarianceEntry D (flags c (slot i)).1 (flags c (slot j)).1
            ((flags c (slot i)).2, colour i, a) ((flags c (slot j)).2, colour j, b)
            (parameter c x) * inverseJetWeight c x (slot i) (n i) a *
              inverseJetWeight c x (slot j) (n j) b := by
  apply nativeTaylor_eq D upperA c hx hx₁ slot colour n i j
  intro a b
  unfold slitCovarianceEntry
  let r := parameter c (x : ℂ)
  let l₁ := (flags c (slot i)).1
  let l₂ := (flags c (slot j)).1
  let e₁ := (flags c (slot i)).2
  let e₂ := (flags c (slot j)).2
  let G : ℂ := (D.G (colour i) (colour j) : ℂ)
  refine pair_coeff_congr
    (f := fun z => G * chartCovariance upperA c x l₁ l₂ e₁ e₂ z.1 z.2)
    (g := fun z => G * slitCovariance l₁ l₂ e₁ e₂ z.1 z.2 r) ?_ a b
  have hsmall : ∀ᶠ u : ℂ in 𝓝 0, ‖u‖ + ‖r‖ < 1 :=
    (isOpen_lt (continuous_norm.add continuous_const) continuous_const).mem_nhds
      (by simpa [r] using hr)
  filter_upwards [chart_covariance_eq_native hx hx₁ upperA c hc
    l₁ l₂ e₁ e₂ hr,
    continuous_fst.continuousAt.eventually hsmall, continuous_snd.continuousAt.eventually hsmall]
    with z hz h₁ h₂
  exact congrArg (G * ·) (hz.trans (slitCovariance_eq_native l₁ l₂ e₁ e₂ h₁ h₂).symm)

/-- The physical D edge uses the true lip covariance entry with the
same two inverse jet weights and the actual D orientation signs. -/
theorem nativeTaylor_d (D : LatticeData) {X : Type*} {x : ℝ} (hx : 0 < x) (hx₁ : x < 1)
    (slot : X → Puncture) (colour : X → Fin D.rank) (n : X → ℕ) (i j : X) :
    nativeTaylor D true .D x slot colour n i j =
      (relative .D (slot i) * relative .D (slot j)) *
        ∑ a ∈ Finset.range (n i + 1), ∑ b ∈ Finset.range (n j + 1),
          dLipCovarianceEntry D true (flags .D (slot i)).1 (flags .D (slot j)).1
            ((flags .D (slot i)).2, colour i, a) ((flags .D (slot j)).2, colour j, b)
            (parameter .D x) * inverseJetWeight .D x (slot i) (n i) a *
              inverseJetWeight .D x (slot j) (n j) b := by
  apply nativeTaylor_eq D true .D hx hx₁ slot colour n i j
  intro a b
  simp only [dLipCovarianceEntry, true_lip_covariance hx hx₁]
  rfl

private def rawMean (upperA : Bool) (c : Chart) (x : ℝ) (i : Puncture) (u : ℂ) : ℂ :=
  -legSign (flags c i).1 * chosenChartSource c x (flags c i).2 u / chartPeriod upperA c x

private theorem meanTaylor_eq (D : LatticeData) {X : Type*}
    (q : Charge D) (upperA : Bool) (c : Chart) {x : ℝ} (hx : 0 < x) (hx₁ : x < 1)
    (slot : X → Puncture) (colour : X → Fin D.rank) (n : X → ℕ) (i : X)
    (M : ℕ → ℂ) (hM : ∀ a, coefficient a (rawMean upperA c x (slot i)) = M a) :
    coefficient (n i) (fun u => physicalMean D q upperA c x slot colour i u *
      relative c (slot i)) =
      ((bilinear D (unitCharge D (colour i)) q : ℂ) * relative c (slot i)) *
        ∑ a ∈ Finset.range (n i + 1), M a * inverseJetWeight c x (slot i) (n i) a := by
  have ha : AnalyticAt ℂ (rawMean upperA c x (slot i)) 0 :=
    (analyticAt_const.mul (chosen_chart_source_at_zero hx hx₁ c (flags c (slot i)).2).1).div_const
  have he (u : ℂ) : physicalMean D q upperA c x slot colour i u * relative c (slot i) =
      ((bilinear D (unitCharge D (colour i)) q : ℂ) * relative c (slot i)) *
        (rawMean upperA c x (slot i) (rawLocal c x (slot i) u) / jac c x (slot i) u) := by
    simp only [physicalMean, physicalSource, rawMean, jac, div_eq_mul_inv]
    ring
  have hs := coefficient_comp_rawLocal_div_halfJacobian ha hx hx₁ c (slot i) (n i)
  simp_rw [he, coeff_mul_left]
  congr 1
  change coefficient (n i) (fun u => rawMean upperA c x (slot i) (rawLocal c x (slot i) u) /
    jac c x (slot i) u) =
    ∑ a ∈ Finset.range (n i + 1), coefficient a (rawMean upperA c x (slot i)) *
      inverseJetWeight c x (slot i) (n i) a at hs
  simpa only [hM] using hs

/-- The charge-linear A or B singleton retains the original signed slit
mean and the full inverse jet weight at its own puncture. -/
theorem meanTaylor_ab (D : LatticeData) {X : Type*}
    (q : Charge D) (upperA : Bool) (c : Chart) {x : ℝ} (hx : 0 < x) (hx₁ : x < 1)
    (hc : c = .A ∨ c = .B) (hr : ‖parameter c (x : ℂ)‖ < 1)
    (slot : X → Puncture) (colour : X → Fin D.rank) (n : X → ℕ) (i : X) :
    coefficient (n i) (fun u => physicalMean D q upperA c x slot colour i u *
      relative c (slot i)) =
      ((bilinear D (unitCharge D (colour i)) q : ℂ) * relative c (slot i)) *
        ∑ a ∈ Finset.range (n i + 1),
          slitMeanEntry (flags c (slot i)).1 (flags c (slot i)).2 a (parameter c x) *
            inverseJetWeight c x (slot i) (n i) a := by
  apply meanTaylor_eq D q upperA c hx hx₁ slot colour n i
  intro a
  have hp : chartPeriod upperA c x = slitPeriod (parameter c (x : ℂ)) := by
    rcases hc with rfl | rfl <;> rfl
  unfold slitMeanEntry
  refine coefficient_congr ?_ a
  have hsmall : ∀ᶠ u : ℂ in 𝓝 0, ‖u‖ + ‖parameter c (x : ℂ)‖ < 1 :=
    (isOpen_lt (continuous_norm.add continuous_const) continuous_const).mem_nhds
      (by simpa using hr)
  filter_upwards [chosen_chart_source_eq_native hx hx₁ c hc (flags c (slot i)).2 hr,
    hsmall] with u hu hsmall
  simp only [rawMean, hp, hu, slitMean_eq_sourceMode _ hsmall]

/-- The charge-linear singleton on the actual D lip has its original
orientation, charge bilinear, and inverse jet coefficient. -/
theorem meanTaylor_d (D : LatticeData) {X : Type*} (q : Charge D)
    {x : ℝ} (hx : 0 < x) (hx₁ : x < 1)
    (slot : X → Puncture) (colour : X → Fin D.rank) (n : X → ℕ) (i : X) :
    coefficient (n i) (fun u => physicalMean D q true .D x slot colour i u *
      relative .D (slot i)) =
      ((bilinear D (unitCharge D (colour i)) q : ℂ) * relative .D (slot i)) *
        ∑ a ∈ Finset.range (n i + 1),
          dLipMeanEntry true (flags .D (slot i)).1 (flags .D (slot i)).2 a (parameter .D x) *
            inverseJetWeight .D x (slot i) (n i) a := by
  apply meanTaylor_eq D q true .D hx hx₁ slot colour n i
  intro a
  simp only [dLipMeanEntry, true_lip_source hx hx₁]
  rfl

end D5.S3.VertexAlgebra.TwistedGround.OriginalFourMNativeWickEntries
