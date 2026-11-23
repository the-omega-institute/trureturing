/- GID: D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMAssignedOccupation
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMAssignedOccupation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact native occupations of assigned modes in the actual charts. -/

import D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMFixedChargeWick
import D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMNativeOccurrenceReadout
import D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMCurrentRegression

/-! The native chart entries of an assigned occurrence word are exactly
the compact entries of its four occupations, including repeated colours. -/

set_option autoImplicit false
noncomputable section
open scoped Topology
open Filter

namespace D5.S3.VertexAlgebra.TwistedGround.OriginalFourMAssignedOccupation

open LatticeGeneratingFieldLocality LatticeHalfFock
open FourPoint.OriginalFourMActualChart
open D5.S3.Analytic.OriginalHalfBinomialSlitPeriod (slitDomain ball_subset_slitDomain)
open OriginalFourMSlitMean (slitCovarianceEntry_analyticOnNhd)
open OriginalFourMPeriodSource (dLip dLip_mem_doubleSlit)
open OriginalFourMOccupationTransport (flags)
open OriginalFourMFixedChargeWick (Mode nativeModeCovariance nativeModeMean)
open OriginalGaussianSourceRestriction (CompactExternal compactExternal externalOccupation)
open OriginalFourMSectorContinuation (slitMatrix slitLinear)
open AffineOccurrenceWick (wick affineMoment_eq_wick)
open OriginalFourMNativeOccurrenceReadout (slotOccupation native_occurrence_readout)
open NativeAffineExternalCoefficient (jetOccupation)
open OriginalChargedRowSource (affineCoefficient)
open FactorialFockMetric (weight)
open private slit_matrix_symm from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMCurrentRegression
open private leg from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMSectorContinuation
open private slitDomain_star midpoint_mem from
  D5.S3.Analytic.OriginalHalfBinomialSlitPeriod
open private dLip_neBot from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMPeriodSource
open private dMatrix dLinear dLipCovarianceEntry dLipCovarianceEntry_analyticAt
  dLipCovarianceEntry_eq_slit from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMDLipChannel
open private external from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMFixedChargeWick

variable {X : Type*} {n : X → ℕ}

/-- The two chart flags select the tagged leg and orientation of an assigned
oscillator in the common finite native support. -/
def compactMode (D : LatticeData) (c : Chart) (slot : X → Puncture)
    (colour : X → Fin D.rank) (F : Finset (Index D))
    (hF : ∀ a : Mode n, (colour a.1, a.2.val) ∈ F)
    (a : Mode n) : CompactExternal D F ⊕ CompactExternal D F :=
  let oscillator : {b // b ∈ F} := ⟨(colour a.1, a.2.val), hF a⟩
  let e : CompactExternal D F := if (flags c (slot a.1)).2 then .inr oscillator else .inl oscillator
  if (flags c (slot a.1)).1 then .inr e else .inl e

/-- Compact chart matrix containing exactly the native slit or true-D lip entries. -/
def compactCovariance (D : LatticeData) (c : Chart) (x : ℝ)
    (F : Finset (Index D)) : Matrix (CompactExternal D F ⊕ CompactExternal D F)
      (CompactExternal D F ⊕ CompactExternal D F) ℂ :=
  Matrix.of fun a b => match c with
    | .A | .B => slitMatrix D (compactExternal D F) (parameter c x) a b
    | .D => dMatrix D true (compactExternal D F) (parameter c x) a b

/-- Native compact mean with the original charge bilinear on each colour. -/
def compactMean (D : LatticeData) (q : Charge D) (c : Chart) (x : ℝ)
    (F : Finset (Index D)) (a : CompactExternal D F ⊕ CompactExternal D F) : ℂ :=
  let e := compactExternal D F
  (bilinear D (unitCharge D (Sum.elim e e a).2.1) q : ℂ) *
    match c with
    | .A | .B => slitLinear D e (parameter c x) a
    | .D => dLinear D true e (parameter c x) a

/-- Compact mode identification for the literal A, B, and D covariances
and their charge-linear means. -/
theorem mode_array_pullback (D : LatticeData) (q : Charge D) (c : Chart) (x : ℝ)
    (slot : X → Puncture) (colour : X → Fin D.rank) (F : Finset (Index D))
    (hF : ∀ a : Mode n, (colour a.1, a.2.val) ∈ F) :
    let f := compactMode D c slot colour F hF
    nativeModeCovariance D c x slot colour n = (compactCovariance D c x F).submatrix f f ∧
      nativeModeMean D q c x slot colour n = compactMean D q c x F ∘ f := by
  dsimp only
  have hl (a : Mode n) : leg (compactMode D c slot colour F hF a) = (flags c (slot a.1)).1 := by
    cases he : (flags c (slot a.1)).1 <;> simp [compactMode, leg, he]
  have hd (a : Mode n) :
      (compactMode D c slot colour F hF a).isRight = (flags c (slot a.1)).1 := by
    cases he : (flags c (slot a.1)).1 <;> simp [compactMode, he]
  have he (a : Mode n) : Sum.elim (compactExternal D F) (compactExternal D F)
      (compactMode D c slot colour F hF a) = external D c slot colour a := by
    cases h₁ : (flags c (slot a.1)).1 <;> cases h₂ : (flags c (slot a.1)).2 <;>
      simp [compactExternal, compactMode, h₁, h₂, external]
  constructor
  · ext a b
    cases c <;> simp only [nativeModeCovariance, compactCovariance, Matrix.of_apply,
      Matrix.submatrix_apply, slitMatrix, dMatrix, hl, hd, he]
  · funext a
    cases c <;> simp only [nativeModeMean, compactMean, Function.comp_apply, slitLinear, dLinear,
      hl, hd, he, external]

/-- Each native assigned word evaluates to the ordinary compact affine
coefficient multiplied by the four literal Fock factorials. -/
theorem assigned_word_affine [Finite X] (D : LatticeData) (q : Charge D) (c : Chart) (x : ℝ)
    (slot : X → Puncture) (colour : X → Fin D.rank) (F : Finset (Index D))
    (hF : ∀ a : Mode n, (colour a.1, a.2.val) ∈ F)
    (hs : ∀ a b, compactCovariance D c x F a b = compactCovariance D c x F b a)
    (l : List (Mode n)) :
    let labels := l.map (compactMode D c slot colour F hF)
    let left := labels.filterMap Sum.getLeft?
    let right := labels.filterMap Sum.getRight?
    let b := slotOccupation D F (left.filterMap Sum.getLeft?)
    let g := slotOccupation D F (left.filterMap Sum.getRight?)
    let d := slotOccupation D F (right.filterMap Sum.getLeft?)
    let e := slotOccupation D F (right.filterMap Sum.getRight?)
    wick (nativeModeCovariance D c x slot colour n) (nativeModeMean D q c x slot colour n) l =
      (weight b : ℂ) * (weight g : ℂ) * ((weight d : ℂ) * (weight e : ℂ)) *
        affineCoefficient (compactCovariance D c x F) (compactMean D q c x F)
          (externalOccupation D F b g d e) := by
  let := Fintype.ofFinite X
  dsimp only
  let f := compactMode D c slot colour F hF
  let K := compactCovariance D c x F
  let μ := compactMean D q c x F
  have ⟨hK, hμ⟩ := mode_array_pullback D q c x slot colour F hF
  rw [hK, hμ, ← affineMoment_eq_wick K μ hs f l]
  have h := native_occurrence_readout D F K μ hs f l
  rw [AffineOccurrenceWick.affineMoment_pullback K μ hs f l] at h
  exact h

/-- The compact slit array used in the A and B readouts is symmetric
throughout the original radial disk. -/
theorem compactCovariance_ab_symm (D : LatticeData) (c : Chart) (x : ℝ)
    (F : Finset (Index D)) (hc : c = .A ∨ c = .B) (hr : ‖parameter c (x : ℂ)‖ < 1)
    (a b : CompactExternal D F ⊕ CompactExternal D F) :
    compactCovariance D c x F a b = compactCovariance D c x F b a := by
  rcases hc with rfl | rfl <;> exact slit_matrix_symm D (compactExternal D F) hr a b

private theorem slit_symm_all (D : LatticeData) {Y : Type*}
    (e : Y → OriginalGaussianExternalBlocks.External D) (a b : Y ⊕ Y) :
    Set.EqOn (fun r => slitMatrix D e r a b) (fun r => slitMatrix D e r b a) slitDomain := by
  have ha (a b : Y ⊕ Y) : AnalyticOnNhd ℂ (fun r => slitMatrix D e r a b) slitDomain := by
    cases a <;> cases b <;> exact slitCovarianceEntry_analyticOnNhd D _ _ _ _
  have h0 : (0 : ℂ) ∈ slitDomain := ball_subset_slitDomain
    (Metric.mem_ball_self (by norm_num))
  have hfreq : ∃ᶠ r : ℂ in 𝓝[≠] (0 : ℂ), slitMatrix D e r a b = slitMatrix D e r b a := by
    have hb : ∀ᶠ r : ℂ in 𝓝 (0 : ℂ), ‖r‖ < 1 :=
      (isOpen_lt continuous_norm continuous_const).mem_nhds (by simp)
    exact ((hb.filter_mono nhdsWithin_le_nhds).mono fun r hr =>
      slit_matrix_symm D e hr a b).frequently
  exact (ha a b).eqOn_of_preconnected_of_frequently_eq (ha b a)
    (slitDomain_star.isPathConnected midpoint_mem.1).isConnected.isPreconnected h0 hfreq

/-- The original D covariance is symmetric at the true boundary lip.
The proof continues the literal compact slit entries and takes their
one-sided limits in the actual D entry formula. -/
theorem compactCovariance_d_symm (D : LatticeData) {x : ℝ} (hx : 0 < x) (hx₁ : x < 1)
    (F : Finset (Index D)) (a b : CompactExternal D F ⊕ CompactExternal D F) :
    compactCovariance D .D x F a b = compactCovariance D .D x F b a := by
  let e := compactExternal D F
  let t : ℝ := x⁻¹
  have ht : 1 < t := (one_lt_inv₀ hx).2 hx₁
  have ha (a b : CompactExternal D F ⊕ CompactExternal D F) :
      AnalyticAt ℂ (fun r => dMatrix D true e r a b) (t : ℂ) :=
    dLipCovarianceEntry_analyticAt D true _ _ _ _ ht
  have he (a b : CompactExternal D F ⊕ CompactExternal D F) {r : ℂ}
      (hr : r ∈ dLip true) : dMatrix D true e r a b = slitMatrix D e r a b := by
    cases a <;> cases b <;> exact dLipCovarianceEntry_eq_slit D true _ _ _ _ hr
  let := dLip_neBot true t
  have hEq : (fun r => dMatrix D true e r a b) =ᶠ[𝓝[dLip true] (t : ℂ)]
      (fun r => dMatrix D true e r b a) := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    rw [he a b hr, he b a hr]
    exact slit_symm_all D e a b (dLip_mem_doubleSlit hr).1
  change dMatrix D true e (parameter .D (x : ℂ)) a b =
    dMatrix D true e (parameter .D (x : ℂ)) b a
  rw [show parameter .D (x : ℂ) = (t : ℂ) by simp [t, parameter, Complex.ofReal_inv]]
  exact tendsto_nhds_unique_of_eventuallyEq
    ((ha a b).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    ((ha b a).continuousAt.tendsto.mono_left nhdsWithin_le_nhds) hEq

end D5.S3.VertexAlgebra.TwistedGround.OriginalFourMAssignedOccupation
