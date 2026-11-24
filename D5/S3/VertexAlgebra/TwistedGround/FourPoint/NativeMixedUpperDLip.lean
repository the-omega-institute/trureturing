/- GID: D5/S3/VertexAlgebra/TwistedGround/FourPoint/NativeMixedUpperDLip
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/FourPoint/NativeMixedUpperDLip
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The native mixed R/mu product in D order continues to the true upper Laurent lip. -/

import D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedUpperProductCusp
import D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMDLipChannel

/-! The D product has inner insertions P and R, outer insertion Q and detector S.
The D coordinate approaches the cut from below, so minus that coordinate
approaches the upper Laurent branch. -/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

noncomputable section

open scoped BigOperators Topology TensorProduct VertexOperator
open Filter Metric

namespace D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedUpperDLip

open Complex (I)
open LatticeGeneratingFieldLocality LatticeHalfFock LatticePositiveEnergy
open LatticeHalfFockChargedTensorCoefficients LatticeHalfFockGradedTrace
open LatticeTwistedGroundRealization LatticeTwistedGroundRealization.SignQuotient
open ActualLeechHyperbolic (leechData leech_spec)
open Orbifold.NativeOddTwistedIntertwiner (Twisted leechUnit)
open OriginalFourMActualChart (Puncture parameter loweringParameter)
open OriginalFourMVariableSupport
  (occupationReadout inverseFlow nativeSector wordAt loweredOscillator)
open OriginalFourMSectorContinuation (slitChargeSector slitChargeSector_differentiableOn
  dLipChargeSector dLipChargeSector_analyticAt dLipChargeSector_eq_slit)
open OriginalFourMPeriodSource (dLip)
open D5.S3.Analytic.OriginalHalfBinomialSlitPeriod
  (slitDomain isOpen_slitDomain ball_subset_slitDomain doubleSlit isOpen_doubleSlit
    doubleSlit_preconnected)
open NativeMixedUpperProductCusp (bProductCoeff bProductCoeff_eq_taylor bSewnNumerator)
open NativeMixedWickChartTransport
  (bpzPhase laurentPower laurentRoot laurentRoot_values gaussianOccupation normalizedOccupation)
open OriginalGaussianSewnAnalytic (coefficient)

open private mixedGroundWeight from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedWickCuspGerm
open private analytic_neg_square_even_part from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMChargeGerm
open private detectorSewn detectorSewn_analyticAt detectorSewn_eq
  punctureModes punctureExcitation punctureExcitation_cast b_loweredOscillator_eq_inverseFlow
  from D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedUpperProductCusp

/-- The literal R/mu energy coefficient in D order. The inner exponent is
`2E-(6+M+L)` and the outer exponent is `N-K-2E`. -/
def dProductCoeff (s t : Bool) (M K L N : ℕ)
    (v : Twisted leechData leechUnit s) (w : Twisted leechData leechUnit (!s))
    (u : Twisted leechData leechUnit t) (b : Twisted leechData leechUnit (!t))
    (E : ℕ) : ℂ :=
  bProductCoeff s t K M L N v w u b E

private def dOccupation (M L N : ℕ) (P Q R S : Oscillator leechData)
    (sector : Exponent leechData → Exponent leechData → Exponent leechData →
      Exponent leechData → ℂ) : ℂ :=
  occupationReadout leechData (inverseFlow leechData (M / 2 + 1) P)
    (inverseFlow leechData (L / 2 + 1) R) Q (inverseFlow leechData (N / 2 + 1) S) sector

/-- The continued numerator with ground forms in native order
`B_T(r,C_a p) * B_T(d,C_a q)`. -/
def dSlitNumerator (M L N : ℕ) (P Q R S : Oscillator leechData)
    (p q r d : ActualGround leechData leechUnit) (z : ℂ) : ℂ :=
  ∑ a : ModTwoCharge leechData, mixedGroundWeight p r q d a *
    dOccupation M L N P Q R S (fun β γ δ η => slitChargeSector leechData a β γ δ η z)

/-- The upper Laurent lift on the positive D coordinate. -/
def dLaurentRoot (z : ℂ) : ℂ := I * z ^ (1 / 2 : ℂ)

theorem dLaurentRoot_eq_cpow {z : ℂ} (hz : z ∈ dLip true) :
    dLaurentRoot z = (-z) ^ (1 / 2 : ℂ) := by
  have him : z.im < 0 := hz
  have h₀ : z ≠ 0 := by
    intro he
    simp [he] at him
  have hlog : Complex.log (-z) = Complex.log z + (Real.pi : ℂ) * I := by
    simp only [Complex.log, norm_neg, Complex.arg_neg_eq_arg_add_pi_of_im_neg him,
      Complex.ofReal_add]
    ring
  rw [dLaurentRoot, Complex.cpow_def_of_ne_zero h₀,
    Complex.cpow_def_of_ne_zero (neg_ne_zero.mpr h₀), hlog, add_mul, Complex.exp_add]
  rw [show (Real.pi : ℂ) * I * (1 / 2 : ℂ) = (Real.pi : ℂ) / 2 * I by ring,
    Complex.exp_pi_div_two_mul_I, mul_comm]

private theorem dLaurentRoot_analyticAt {z : ℂ} (hz : z ∈ Complex.slitPlane) :
    AnalyticAt ℂ dLaurentRoot z := by
  unfold dLaurentRoot
  exact analyticAt_const.mul (analyticAt_id.cpow analyticAt_const hz)

private theorem halfPower_sq (z : ℂ) : (z ^ (1 / 2 : ℂ)) ^ (2 : ℕ) = z := by
  simpa only [one_div, Nat.cast_ofNat] using
    Complex.cpow_nat_inv_pow z (by decide : (2 : ℕ) ≠ 0)

theorem dLaurentRoot_on_inverse {y : ℝ} (hy : 0 < y) :
    dLaurentRoot (parameter .D (y : ℂ)) = I / (Real.sqrt y : ℂ) := by
  change I * ((y : ℂ)⁻¹) ^ (1 / 2 : ℂ) = _
  rw [← Complex.ofReal_inv, show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num,
    ← Complex.ofReal_cpow (inv_nonneg.mpr hy.le), ← Real.sqrt_eq_rpow, Real.sqrt_inv,
    Complex.ofReal_inv, div_eq_mul_inv]

/-- The continued native Laurent product in the D coordinate. -/
def dSlitProduct (M K L N : ℕ) (P Q R S : Oscillator leechData)
    (p q r d : ActualGround leechData leechUnit) (z : ℂ) : ℂ :=
  dLaurentRoot z ^ (-(6 + (M : ℤ) + L)) * bpzPhase M K L N .D *
    dSlitNumerator M L N P Q R S p q r d z

theorem dSlitNumerator_analyticOnNhd (M L N : ℕ) (P Q R S : Oscillator leechData)
    (p q r d : ActualGround leechData leechUnit) :
    AnalyticOnNhd ℂ (dSlitNumerator M L N P Q R S p q r d) slitDomain := by
  intro z hz
  have hsector (a : ModTwoCharge leechData) (β γ δ η : Exponent leechData) :
      AnalyticAt ℂ (slitChargeSector leechData a β γ δ η) z :=
    DifferentiableOn.analyticOnNhd
      (slitChargeSector_differentiableOn leechData leech_spec.2.2.1 a β γ δ η)
      isOpen_slitDomain z hz
  unfold dSlitNumerator dOccupation occupationReadout
  fun_prop

theorem dSlitProduct_analyticOnNhd (M K L N : ℕ) (P Q R S : Oscillator leechData)
    (p q r d : ActualGround leechData leechUnit) :
    AnalyticOnNhd ℂ (dSlitProduct M K L N P Q R S p q r d) doubleSlit := by
  intro z hz
  have hroot : dLaurentRoot z ≠ 0 :=
    mul_ne_zero Complex.I_ne_zero
      (Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.slitPlane_ne_zero hz.2)))
  unfold dSlitProduct
  exact (((dLaurentRoot_analyticAt hz.2).zpow hroot).mul analyticAt_const).mul
    (dSlitNumerator_analyticOnNhd M L N P Q R S p q r d z hz.1)

set_option maxHeartbeats 4000000 in
/-- The energy-grid series of the actual permuted fields at the complex cusp.
Its summation variable is the D coordinate, with the cusp monomial
written in the principal square root of that coordinate. -/
theorem d_upper_product_hasSum (s t : Bool) (M K L N : ℕ)
    (v : Twisted leechData leechUnit s) (w : Twisted leechData leechUnit (!s))
    (u : Twisted leechData leechUnit t) (b : Twisted leechData leechUnit (!t))
    (P Q R S : Oscillator leechData) (p q r d : ActualGround leechData leechUnit)
    (hv : v.val ∈ actualGrade leechData leechUnit M)
    (hw : w.val ∈ actualGrade leechData leechUnit L)
    (hu : u.val ∈ actualGrade leechData leechUnit K)
    (hb : b.val ∈ actualGrade leechData leechUnit N)
    (hvP : v.val = P ⊗ₜ[ℂ] p) (hwR : w.val = R ⊗ₜ[ℂ] r)
    (huQ : u.val = Q ⊗ₜ[ℂ] q) (hbS : b.val = S ⊗ₜ[ℂ] d)
    (hML : Odd ((M : ℤ) + L)) (hNK : Odd ((N : ℤ) - K)) :
    ∀ᶠ z in 𝓝 (0 : ℂ), z ≠ 0 →
      HasSum (fun E : ℕ => dProductCoeff s t M K L N v w u b E *
        (z ^ (1 / 2 : ℂ)) ^ (2 * (E : ℤ) - (6 + (M : ℤ) + L)))
        (dSlitProduct M K L N P Q R S p q r d z) := by
  let F := detectorSewn M L N Q P R S q p r d
  let A : ℤ := 6 + (M : ℤ) + L
  obtain ⟨G, hG, hpull⟩ := analytic_neg_square_even_part
    (detectorSewn_analyticAt M L N Q P R S q p r d)
  have hcont : ContinuousAt (fun z : ℂ => z ^ (1 / 2 : ℂ)) 0 := by
    apply Complex.continuousAt_cpow_const_of_re_pos (Or.inl (by simp))
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num, Complex.ofReal_re]
    norm_num
  have hroot : Tendsto (fun z : ℂ => z ^ (1 / 2 : ℂ)) (𝓝 0) (𝓝 0) := by
    simpa only [Complex.zero_cpow (by norm_num : (1 / 2 : ℂ) ≠ 0)] using hcont.tendsto
  have hneg : Tendsto (fun z : ℂ => -z) (𝓝 0) (𝓝 0) := by
    have h : ContinuousAt (fun z : ℂ => -z) 0 := continuous_neg.continuousAt
    simpa only [neg_zero] using h.tendsto
  filter_upwards [hneg.eventually hG.eventually_hasSum, hroot.eventually hpull,
    hroot.eventually_mem (Metric.ball_mem_nhds (0 : ℂ) zero_lt_one)]
    with z hsum hlocal hball hz
  let ρ : ℂ := z ^ (1 / 2 : ℂ)
  have hsq : ρ ^ (2 : ℕ) = z := halfPower_sq z
  have hρ : ρ ≠ 0 := by
    intro h
    exact hz (hsq.symm.trans (by simp [h]))
  have hsmall : ‖ρ‖ < 1 := mem_ball_zero_iff.mp hball
  have hsmallneg : ‖-ρ‖ < 1 := by simpa only [norm_neg] using hsmall
  have hvalue : G (-z) =
      I ^ ((L : ℤ) - 2 * (M : ℤ) - 3) * dSlitNumerator M L N P Q R S p q r d z := by
    change G (-(ρ ^ 2)) = (F ρ + F (-ρ)) / 2 at hlocal
    have he : G (-z) = (F ρ + F (-ρ)) / 2 := by simpa only [hsq] using hlocal
    change G (-z) =
      I ^ ((L : ℤ) - 2 * (M : ℤ) - 3) * bSewnNumerator M L N Q P R S q p r d z
    rw [he]
    dsimp only [F]
    rw [detectorSewn_eq M L N Q P R S q p r d hsmall,
      detectorSewn_eq M L N Q P R S q p r d hsmallneg, neg_sq, hsq]
    ring
  have hnegative : HasSum (fun E : ℕ =>
      ((-1 : ℂ) ^ E * coefficient (2 * E) F) * (-z) ^ E) (G (-z)) := by
    simpa only [zero_add, FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul] using hsum
  have hpositive : HasSum (fun E : ℕ => coefficient (2 * E) F * z ^ E) (G (-z)) := by
    refine hnegative.congr_fun fun E => ?_
    rw [neg_pow]
    have hsign : (-1 : ℂ) ^ E * (-1 : ℂ) ^ E = 1 := by
      rw [← mul_pow]
      norm_num
    calc
      _ = (coefficient (2 * E) F * z ^ E) * 1 := by ring
      _ = (coefficient (2 * E) F * z ^ E) * ((-1 : ℂ) ^ E * (-1 : ℂ) ^ E) := by
        rw [hsign]
      _ = _ := by ring
  have hpow (E : ℕ) : ρ ^ (2 * (E : ℤ) - A) = ρ ^ (-A) * z ^ E := by
    rw [show 2 * (E : ℤ) - A = -A + 2 * (E : ℤ) by ring,
      zpow_add₀ hρ, zpow_mul, zpow_natCast _ E, zpow_ofNat ρ 2, hsq]
  have hphase :
      (I * ρ) ^ (-A) * bpzPhase M K L N .D =
        (ρ ^ (-A) * I ^ ((N : ℤ) - K)) * I ^ ((L : ℤ) - 2 * (M : ℤ) - 3) := by
    rw [bpzPhase, mul_zpow]
    calc
      _ = ρ ^ (-A) * (I ^ (-A) * I ^ (3 + 2 * (L : ℤ) + N - M - K)) := by ring
      _ = _ := by
        rw [← zpow_add₀ Complex.I_ne_zero, mul_assoc, ← zpow_add₀ Complex.I_ne_zero]
        rw [show -A + (3 + 2 * (L : ℤ) + N - M - K) =
          ((N : ℤ) - K) + ((L : ℤ) - 2 * (M : ℤ) - 3) by dsimp only [A]; ring]
  change HasSum (fun E : ℕ => dProductCoeff s t M K L N v w u b E * ρ ^ (2 * (E : ℤ) - A))
    ((I * ρ) ^ (-A) * bpzPhase M K L N .D * dSlitNumerator M L N P Q R S p q r d z)
  rw [hphase, mul_assoc (ρ ^ (-A) * I ^ ((N : ℤ) - K)), ← hvalue]
  refine (hpositive.mul_left (ρ ^ (-A) * I ^ ((N : ℤ) - K))).congr_fun fun E => ?_
  rw [dProductCoeff, bProductCoeff_eq_taylor s t K M L N v w u b Q P R S q p r d
    hv hw hu hb hvP hwR huQ hbS hML hNK, hpow]
  change (I ^ ((N : ℤ) - K) * coefficient (2 * E) F) * (ρ ^ (-A) * z ^ E) = _
  ring

/-- A holomorphic function on the connected double slit that sums the
original D field series near the cusp is the explicit slit product. -/
theorem dSlitProduct_unique (s t : Bool) (M K L N : ℕ)
    (v : Twisted leechData leechUnit s) (w : Twisted leechData leechUnit (!s))
    (u : Twisted leechData leechUnit t) (b : Twisted leechData leechUnit (!t))
    (P Q R S : Oscillator leechData) (p q r d : ActualGround leechData leechUnit)
    (hv : v.val ∈ actualGrade leechData leechUnit M)
    (hw : w.val ∈ actualGrade leechData leechUnit L)
    (hu : u.val ∈ actualGrade leechData leechUnit K)
    (hb : b.val ∈ actualGrade leechData leechUnit N)
    (hvP : v.val = P ⊗ₜ[ℂ] p) (hwR : w.val = R ⊗ₜ[ℂ] r)
    (huQ : u.val = Q ⊗ₜ[ℂ] q) (hbS : b.val = S ⊗ₜ[ℂ] d)
    (hML : Odd ((M : ℤ) + L)) (hNK : Odd ((N : ℤ) - K))
    {F : ℂ → ℂ} (hF : AnalyticOnNhd ℂ F doubleSlit)
    (hSum : ∀ᶠ z in 𝓝 (0 : ℂ), z ∈ doubleSlit →
      HasSum (fun E : ℕ => dProductCoeff s t M K L N v w u b E *
        (z ^ (1 / 2 : ℂ)) ^ (2 * (E : ℤ) - (6 + (M : ℤ) + L))) (F z)) :
    Set.EqOn F (dSlitProduct M K L N P Q R S p q r d) doubleSlit := by
  have he : ∀ᶠ z in 𝓝 (0 : ℂ), z ∈ doubleSlit →
      F z = dSlitProduct M K L N P Q R S p q r d z := by
    filter_upwards [hSum, d_upper_product_hasSum s t M K L N v w u b P Q R S p q r d
      hv hw hu hb hvP hwR huQ hbS hML hNK] with z h₁ h₂ hz
    exact (h₁ hz).unique (h₂ (Complex.slitPlane_ne_zero hz.2))
  obtain ⟨U, hU, hUopen, h0⟩ := _root_.eventually_nhds_iff.mp he
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hUopen (0 : ℂ) h0
  let x : ℝ := min (ε / 2) (1 / 2)
  have hx : 0 < x := lt_min (by linarith) (by norm_num)
  have hxε : x < ε := (min_le_left _ _).trans_lt (by linarith)
  have hx₁ : x < 1 := (min_le_right _ _).trans_lt (by norm_num)
  have hxball {r₀ : ℝ} (h : x < r₀) : (x : ℂ) ∈ ball (0 : ℂ) r₀ := by
    rwa [mem_ball_zero_iff, Complex.norm_real, Real.norm_of_nonneg hx.le]
  have hxslit : (x : ℂ) ∈ doubleSlit :=
    ⟨ball_subset_slitDomain (hxball hx₁), Complex.ofReal_mem_slitPlane.mpr hx⟩
  apply hF.eqOn_of_preconnected_of_eventuallyEq
    (dSlitProduct_analyticOnNhd M K L N P Q R S p q r d) doubleSlit_preconnected hxslit
  filter_upwards [hUopen.mem_nhds (hball (hxball hxε)),
    isOpen_doubleSlit.mem_nhds hxslit] with z hz hslit
  exact hU z hz hslit

private def dLipOccupation (M L N : ℕ) (P Q R S : Oscillator leechData)
    (a : ModTwoCharge leechData) (z : ℂ) : ℂ :=
  dOccupation M L N P Q R S (fun β γ δ η => dLipChargeSector leechData true a β γ δ η z)

private def dLipNumerator (M L N : ℕ) (P Q R S : Oscillator leechData)
    (p q r d : ActualGround leechData leechUnit) (z : ℂ) : ℂ :=
  ∑ a : ModTwoCharge leechData, mixedGroundWeight p r q d a *
    dLipOccupation M L N P Q R S a z

/-- Analytic representative of the product germ at a real point of the true D lip. -/
def dLipProduct (M K L N : ℕ) (P Q R S : Oscillator leechData)
    (p q r d : ActualGround leechData leechUnit) (z : ℂ) : ℂ :=
  dLaurentRoot z ^ (-(6 + (M : ℤ) + L)) * bpzPhase M K L N .D *
    dLipNumerator M L N P Q R S p q r d z

theorem dLipProduct_analyticAt (M K L N : ℕ) (P Q R S : Oscillator leechData)
    (p q r d : ActualGround leechData leechUnit) {x : ℝ} (hx : 1 < x) :
    AnalyticAt ℂ (dLipProduct M K L N P Q R S p q r d) (x : ℂ) := by
  have hsector (a : ModTwoCharge leechData) (β γ δ η : Exponent leechData) :
      AnalyticAt ℂ (dLipChargeSector leechData true a β γ δ η) (x : ℂ) :=
    dLipChargeSector_analyticAt leechData leech_spec.2.2.1 true a β γ δ η hx
  have hn : AnalyticAt ℂ (dLipNumerator M L N P Q R S p q r d) (x : ℂ) := by
    unfold dLipNumerator dLipOccupation dOccupation occupationReadout
    fun_prop
  have hx₀ : 0 < x := zero_lt_one.trans hx
  have hroot : dLaurentRoot (x : ℂ) ≠ 0 := by
    apply mul_ne_zero Complex.I_ne_zero
    exact Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr hx₀.ne'))
  unfold dLipProduct
  exact (((dLaurentRoot_analyticAt (Complex.ofReal_mem_slitPlane.mpr hx₀)).zpow hroot).mul
    analyticAt_const).mul hn

theorem dLipProduct_eq_slit (M K L N : ℕ) (P Q R S : Oscillator leechData)
    (p q r d : ActualGround leechData leechUnit) {z : ℂ} (hz : z ∈ dLip true) :
    dLipProduct M K L N P Q R S p q r d z = dSlitProduct M K L N P Q R S p q r d z := by
  simp only [dLipProduct, dSlitProduct, dLipNumerator, dSlitNumerator, dLipOccupation,
    dLipChargeSector_eq_slit leechData true _ _ _ _ _ hz]

/-- Open-lip agreement makes the analytic representative a genuine boundary
extension of the same function that sums the original field coefficients. -/
theorem dSlitProduct_tendsto_dLip (M K L N : ℕ) (P Q R S : Oscillator leechData)
    (p q r d : ActualGround leechData leechUnit) {x : ℝ} (hx : 1 < x) :
    Tendsto (dSlitProduct M K L N P Q R S p q r d) (𝓝[dLip true] (x : ℂ))
      (𝓝 (dLipProduct M K L N P Q R S p q r d (x : ℂ))) := by
  have hlip : ∀ᶠ z in 𝓝[dLip true] (x : ℂ), z ∈ dLip true := self_mem_nhdsWithin
  exact ((dLipProduct_analyticAt M K L N P Q R S p q r d hx).continuousAt.tendsto.mono_left
    nhdsWithin_le_nhds).congr' (hlip.mono fun _ hz =>
      dLipProduct_eq_slit M K L N P Q R S p q r d hz)

open OriginalFourMCompactLowering (punctureLowering)
open private oscillatorWord punctureLowering_eq_word from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMNativeLaurent

private theorem d_loweredP_eq_inverseFlow {X : Type*} (slot : X → Puncture)
    (colour : X → Fin leechData.rank) (n : X → ℕ) (l : List X) :
    loweredOscillator leechData slot colour .D n l .P =
      inverseFlow leechData (punctureExcitation slot colour n l .P / 2 + 1)
        (wordAt leechData slot colour n l .P) := by
  -- Use the same marks with the B chart's lowered Q label.
  classical
  let relabel : X → Puncture := fun x => if slot x = .P then Puncture.Q else Puncture.P
  let modes := punctureModes slot colour n l .P
  have hm : punctureModes relabel colour n l .Q = modes := by
    have hfilter : (fun a => decide (relabel a = .Q)) =
        (fun a => decide (slot a = .P)) := by
      funext a
      by_cases ha : slot a = .P <;> simp [relabel, ha]
    dsimp only [modes, punctureModes]
    rw [hfilter]
  have h := b_loweredOscillator_eq_inverseFlow relabel colour n l .Q rfl
  let modesB := punctureModes relabel colour n l .Q
  change punctureLowering leechData .B .Q modesB =
    inverseFlow leechData (((modesB.map fun a => 2 * a.2 + 1).sum) / 2 + 1)
      (oscillatorWord leechData modesB) at h
  change punctureLowering leechData .D .P modes =
    inverseFlow leechData (((modes.map fun a => 2 * a.2 + 1).sum) / 2 + 1)
      (oscillatorWord leechData modes)
  have hlowering : punctureLowering leechData .D .P modes =
      punctureLowering leechData .B .Q modes := rfl
  rw [hlowering]
  have hm' : modesB = modes := hm
  rwa [hm'] at h

/-- The normalized native D occupation with exactly the product's upper
Laurent power and BPZ phase. -/
theorem d_normalizedOccupation_eq {X : Type*} (slot : X → Puncture)
    (colour : X → Fin leechData.rank) (n : X → ℕ) (l : List X)
    {y : ℝ} (hy₁ : y < 1) (a : ModTwoCharge leechData) :
    let H := punctureExcitation slot colour n l
    let V := wordAt leechData slot colour n l
    normalizedOccupation leechData slot colour n l .D y a =
      (I / (Real.sqrt y : ℂ)) ^ (-(6 + (H .P : ℤ) + H .R)) *
        I ^ (3 + 2 * (H .R : ℤ) + H .S - H .P - H .Q) *
        dLipOccupation (H .P) (H .R) (H .S)
          (V .P) (V .Q) (V .R) (V .S) a (parameter .D (y : ℂ)) := by
  dsimp only
  unfold normalizedOccupation
  simp only [← punctureExcitation_cast slot colour n l, bpzPhase, laurentPower,
    (laurentRoot_values hy₁).2.2]
  have hP := d_loweredP_eq_inverseFlow slot colour n l
  have hQ : loweredOscillator leechData slot colour .D n l .Q =
      wordAt leechData slot colour n l .Q :=
    punctureLowering_eq_word leechData .D .Q rfl (punctureModes slot colour n l .Q)
  have hR : loweredOscillator leechData slot colour .D n l .R =
      inverseFlow leechData (punctureExcitation slot colour n l .R / 2 + 1)
        (wordAt leechData slot colour n l .R) := by
    simpa only [loweredOscillator, punctureLowering, loweringParameter] using
      b_loweredOscillator_eq_inverseFlow slot colour n l .R rfl
  have hS : loweredOscillator leechData slot colour .D n l .S =
      inverseFlow leechData (punctureExcitation slot colour n l .S / 2 + 1)
        (wordAt leechData slot colour n l .S) := by
    simpa only [loweredOscillator, punctureLowering, loweringParameter] using
      b_loweredOscillator_eq_inverseFlow slot colour n l .S rfl
  have hoccupation : gaussianOccupation leechData slot colour n l .D y a =
      dLipOccupation (punctureExcitation slot colour n l .P)
        (punctureExcitation slot colour n l .R) (punctureExcitation slot colour n l .S)
        (wordAt leechData slot colour n l .P) (wordAt leechData slot colour n l .Q)
        (wordAt leechData slot colour n l .R) (wordAt leechData slot colour n l .S)
        a (parameter .D (y : ℂ)) := by
    change occupationReadout leechData
      (loweredOscillator leechData slot colour .D n l .P)
      (loweredOscillator leechData slot colour .D n l .R)
      (loweredOscillator leechData slot colour .D n l .Q)
      (loweredOscillator leechData slot colour .D n l .S)
      (nativeSector leechData .D y a) = _
    rw [hP, hR, hQ, hS]
    rfl
  rw [hoccupation]
  ring

/-- The analytic lip representative evaluates to the normalized D occupations
with both ordered ground forms. -/
theorem dLipProduct_eq_weighted_normalizedOccupation {X : Type*} (slot : X → Puncture)
    (colour : X → Fin leechData.rank) (n : X → ℕ) (l : List X)
    (p q r d : ActualGround leechData leechUnit) {y : ℝ} (hy : 0 < y) (hy₁ : y < 1) :
    let H := punctureExcitation slot colour n l
    let V := wordAt leechData slot colour n l
    dLipProduct (H .P) (H .Q) (H .R) (H .S) (V .P) (V .Q) (V .R) (V .S) p q r d
        (parameter .D (y : ℂ)) =
      ∑ a : ModTwoCharge leechData, mixedGroundWeight p r q d a *
        normalizedOccupation leechData slot colour n l .D y a := by
  classical
  dsimp only
  simp only [d_normalizedOccupation_eq slot colour n l hy₁, dLipProduct, dLipNumerator,
    dLaurentRoot_on_inverse hy, bpzPhase, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => by ring

/-- At `r_D = 1/y` the marked product tends to the weighted normalized D value
along the true upper Laurent lip. -/
theorem dSlitProduct_tendsto_weighted_normalizedOccupation {X : Type*} (slot : X → Puncture)
    (colour : X → Fin leechData.rank) (n : X → ℕ) (l : List X)
    (p q r d : ActualGround leechData leechUnit) {y : ℝ} (hy : 0 < y)
    (hy₁ : y < 1) :
    let H := punctureExcitation slot colour n l
    let V := wordAt leechData slot colour n l
    Tendsto (dSlitProduct (H .P) (H .Q) (H .R) (H .S) (V .P) (V .Q) (V .R) (V .S) p q r d)
      (𝓝[dLip true] (parameter .D (y : ℂ)))
      (𝓝 (∑ a : ModTwoCharge leechData, mixedGroundWeight p r q d a *
        normalizedOccupation leechData slot colour n l .D y a)) := by
  classical
  dsimp only
  have hx : 1 < y⁻¹ := (one_lt_inv₀ hy).2 hy₁
  have hlimit := dSlitProduct_tendsto_dLip (punctureExcitation slot colour n l .P)
    (punctureExcitation slot colour n l .Q) (punctureExcitation slot colour n l .R)
    (punctureExcitation slot colour n l .S) (wordAt leechData slot colour n l .P)
    (wordAt leechData slot colour n l .Q) (wordAt leechData slot colour n l .R)
    (wordAt leechData slot colour n l .S) p q r d hx
  have hparam : ((y⁻¹ : ℝ) : ℂ) = parameter .D (y : ℂ) := Complex.ofReal_inv y
  rw [hparam, dLipProduct_eq_weighted_normalizedOccupation slot colour n l p q r d hy hy₁]
    at hlimit
  exact hlimit

end D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedUpperDLip
