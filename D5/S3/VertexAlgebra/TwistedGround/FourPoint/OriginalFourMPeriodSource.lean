/- GID: D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMPeriodSource
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMPeriodSource
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The original four-point covariance correction on the paired period lips. -/

import D5.S3.Analytic.OriginalHalfBinomialPfaffNome
import D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMActualChart

/-! The complementary Euler periods determine the free covariance discrepancy
for the native four-point chart changes. -/

set_option autoImplicit false

noncomputable section

open Complex Filter Set
open scoped Topology

namespace D5.S3.VertexAlgebra.TwistedGround.OriginalFourMPeriodSource

open D5.S3.Analytic.OriginalHalfBinomialSlitPeriod
open D5.S3.Analytic.OriginalHalfBinomialPfaffNome (tau_pfaff_upper tau_pfaff_lower)
open FourPoint.OriginalFourMActualChart (Chart parameter spatialKernel pullB pullD)

private theorem slit_of_re_lt {r : ℂ} (h : r.re < 1) : r ∈ slitDomain :=
  Complex.mem_slitPlane_iff.2 (Or.inl (by simpa [sub_re] using sub_pos.mpr h))

private theorem doubleSlit_of_re {r : ℂ} (h₀ : 0 < r.re) (h₁ : r.re < 1) :
    r ∈ doubleSlit :=
  ⟨slit_of_re_lt h₁, Complex.mem_slitPlane_iff.2 (Or.inl h₀)⟩

private theorem mem_doubleSlit_of_im {r : ℂ} (h : r.im ≠ 0) : r ∈ doubleSlit :=
  ⟨Complex.mem_slitPlane_iff.2 (Or.inr (by simpa using h)),
    Complex.mem_slitPlane_iff.2 (Or.inr h)⟩

private theorem complement_mem {r : ℂ} (h : r ∈ doubleSlit) :
    1 - r ∈ slitDomain := by
  change 1 - (1 - r) ∈ Complex.slitPlane
  simpa using h.2

/-- The logarithmic derivative in the units of the elliptic covariance. -/
def periodCorrection (P : ℂ → ℂ) (r : ℂ) : ℂ :=
  r * (1 - r) * deriv P r / P r

private theorem pfaffMap_eq (t : ℂ) (ht : t ≠ 0) :
    (1 - t) / (1 - t - 1) = 1 - t⁻¹ := by
  rw [show (1 : ℂ) - t - 1 = -t by ring]
  field_simp
  ring

/-- Differentiate the principal Pfaff identity on its open domain. -/
theorem pfaff_correction {r : ℂ} (hr : r ∈ slitDomain) :
    periodCorrection slitPeriod (r / (r - 1)) =
      periodCorrection slitPeriod r / (1 - r) - r / (2 * (1 - r)) := by
  let q := r / (r - 1)
  let S := (1 - r) ^ (1 / 2 : ℂ)
  have hn : 1 - r ≠ 0 := Complex.slitPlane_ne_zero hr
  have hr' : r - 1 ≠ 0 := sub_ne_zero.mpr (sub_ne_zero.mp hn).symm
  have hS : S ≠ 0 := by
    intro h
    apply hn
    have hsq : S ^ 2 = 1 - r := by
      dsimp [S]
      rw [← Complex.cpow_mul_nat]
      norm_num
    rw [← hsq, h]
    norm_num
  have hq : HasDerivAt (fun u : ℂ => u / (u - 1)) (-1 / (1 - r)^2) r := by
    convert (hasDerivAt_id r).fun_div ((hasDerivAt_id r).sub_const 1) hr' using 1 <;> try rfl
    change -1 / (1 - r)^2 = (1 * (r - 1) - r * 1) / (r - 1)^2
    rw [show r - 1 = -(1 - r) by ring, neg_sq]
    ring
  have hroot : HasDerivAt (fun u : ℂ => (1 - u) ^ (1 / 2 : ℂ))
      (-(S / (2 * (1 - r)))) r := by
    convert ((hasDerivAt_id r).const_sub 1).cpow_const (c := (1 / 2 : ℂ)) hr using 1 <;> try rfl
    change -(S / (2 * (1 - r))) = (1 / 2) *
      (1 - r) ^ ((1 / 2 : ℂ) - 1) * -1
    rw [Complex.cpow_sub _ _ hn, Complex.cpow_one]
    dsimp only [S]
    field_simp [hn]
  have hqmem := pfaff_mem_slitDomain hr
  have hleft := (slitPeriod_differentiableAt hqmem).hasDerivAt.comp r hq
  have hright := hroot.mul (slitPeriod_differentiableAt hr).hasDerivAt
  have hopen : IsOpen slitDomain :=
    Complex.isOpen_slitPlane.preimage (continuous_const.sub continuous_id)
  have he : (fun u : ℂ => slitPeriod (u / (u - 1))) =ᶠ[𝓝 r]
      (fun u : ℂ => (1 - u) ^ (1 / 2 : ℂ) * slitPeriod u) :=
    (show ∀ᶠ u in 𝓝 r, u ∈ slitDomain from hopen.mem_nhds hr).mono fun _ hu => pfaff hu
  have hd := hleft.deriv.symm.trans (he.deriv_eq.trans hright.deriv)
  change deriv slitPeriod q * (-1 / (1 - r)^2) =
    -(S / (2 * (1 - r))) * slitPeriod r + S * deriv slitPeriod r at hd
  have hp := slitPeriod_ne_zero hr
  have hvalue : slitPeriod q = S * slitPeriod r := pfaff hr
  have htransport : deriv slitPeriod q =
      (1 - r) / 2 * S * slitPeriod r - (1 - r)^2 * S * deriv slitPeriod r := by
    field_simp [hn] at hd
    linear_combination -hd / 2
  unfold periodCorrection
  change q * (1 - q) * deriv slitPeriod q / slitPeriod q = _
  rw [hvalue, htransport]
  dsimp only [q]
  field_simp [hp, hS, hn, hr']
  ring

private theorem complementary_correction {r : ℂ} (hr : r ∈ doubleSlit) :
    periodCorrection slitPeriod r + periodCorrection slitPeriod (1 - r) =
      1 / ((Real.pi : ℂ) * slitPeriod r * slitPeriod (1 - r)) := by
  have hp := slitPeriod_ne_zero hr.1
  have hq := slitPeriod_ne_zero (complement_mem hr)
  have hπ := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hW := slit_wronskian hr
  unfold periodCorrection
  rw [sub_sub_cancel]
  field_simp [hp, hq, hπ] at hW ⊢
  linear_combination hW

private theorem chartA_mem {z : ℝ} (hz : 0 < z) :
    parameter .A (z : ℂ) ∈ slitDomain := by
  apply slit_of_re_lt
  simp only [parameter, sub_re, one_re, ← ofReal_inv, ofReal_re]
  linarith [inv_pos.mpr hz]

/-- The B comparison differentiates at the actual A argument and its
Pfaff image, both interior to the Euler slit domain. -/
theorem chartB_pfaff_correction {z : ℝ} (hz : 0 < z) :
    (z : ℂ) * periodCorrection slitPeriod (parameter .A (z : ℂ)) + (1 - (z : ℂ))/2 =
      periodCorrection slitPeriod (1 - (z : ℂ)) := by
  have hz₀ : (z : ℂ) ≠ 0 := ofReal_ne_zero.mpr hz.ne'
  have h := pfaff_correction (chartA_mem hz)
  rw [parameter, pfaffMap_eq _ (inv_ne_zero hz₀), inv_inv, sub_sub_cancel] at h
  rw [h]
  simp only [parameter]
  field_simp [hz₀]
  ring

/-- The D side is lower when A is upper, and upper when A is lower. -/
def dLip (upperA : Bool) : Set ℂ :=
  {t | if upperA then t.im < 0 else 0 < t.im}

private def lipSign (upperA : Bool) : ℂ := if upperA then 1 else -1

/-- Analytic continuation of the D period to either lip, in the native
D argument. The sign is the jump of the complementary ratio in A. -/
def dPeriod (upperA : Bool) (t : ℂ) : ℂ :=
  (tau (1 - t⁻¹) + lipSign upperA) * slitPeriod (1 - t) / Complex.I

private theorem isOpen_dLip (upperA : Bool) : IsOpen (dLip upperA) := by
  cases upperA
  · exact isOpen_lt continuous_const Complex.continuous_im
  · exact isOpen_lt Complex.continuous_im continuous_const

private theorem dLip_im_ne_zero {upperA : Bool} {t : ℂ} (ht : t ∈ dLip upperA) :
    t.im ≠ 0 := by
  cases upperA
  · exact (show 0 < t.im from ht).ne'
  · exact (show t.im < 0 from ht).ne

/-- The explicit D germ agrees with the frozen Euler period on the genuine
adjacent open half-plane. -/
theorem dPeriod_eq_slit {upperA : Bool} {t : ℂ} (ht : t ∈ dLip upperA) :
    dPeriod upperA t = slitPeriod t := by
  have ht₀ : t ≠ 0 := by
    intro h
    exact dLip_im_ne_zero ht (by simp [h])
  have hj : tau (1 - t) = tau (1 - t⁻¹) + lipSign upperA := by
    cases upperA
    · have hu : (1 - t).im < 0 := by
        simpa using (show 0 < t.im from ht)
      rw [← pfaffMap_eq t ht₀]
      simpa only [lipSign, Bool.false_eq_true, ite_false, sub_eq_add_neg] using tau_pfaff_lower hu
    · have hu : 0 < (1 - t).im := by
        simpa using (show t.im < 0 from ht)
      rw [lipSign, ← pfaffMap_eq t ht₀]
      exact tau_pfaff_upper hu
  have hp := slitPeriod_ne_zero (r := 1 - t)
    (complement_mem (mem_doubleSlit_of_im (dLip_im_ne_zero ht)))
  rw [dPeriod, ← hj, tau, sub_sub_cancel]
  field_simp [hp, I_ne_zero]

private theorem analyticAt_tau {r : ℂ} (hr : r ∈ doubleSlit) : AnalyticAt ℂ tau r := by
  have hc := (slitPeriod_analyticOnNhd _ (complement_mem hr)).comp
    (analyticAt_const.sub analyticAt_id)
  exact (analyticAt_const.mul hc).div
    (slitPeriod_analyticOnNhd _ hr.1) (slitPeriod_ne_zero hr.1)

private theorem real_d_aux {t : ℝ} (ht : 1 < t) :
    1 - (t : ℂ) ∈ slitDomain ∧ 1 - (t : ℂ)⁻¹ ∈ doubleSlit := by
  have ht₀ : 0 < t := by linarith
  have hInv := (inv_lt_one₀ ht₀).2 ht
  have hi := inv_pos.mpr ht₀
  rw [← ofReal_inv]
  constructor
  · apply slit_of_re_lt
    simp [ht₀]
  · apply doubleSlit_of_re
    · simpa [sub_re] using sub_pos.mpr hInv
    · simpa [sub_re] using hi

private theorem dPeriod_analyticAt (upperA : Bool) {t : ℝ} (ht : 1 < t) :
    AnalyticAt ℂ (dPeriod upperA) (t : ℂ) := by
  have ht₀ : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr (by linarith)
  have h₁ : AnalyticAt ℂ (fun u : ℂ => 1 - u) (t : ℂ) :=
    analyticAt_const.sub analyticAt_id
  have h₂ : AnalyticAt ℂ (fun u : ℂ => 1 - u⁻¹) (t : ℂ) :=
    analyticAt_const.sub (analyticAt_id.inv ht₀)
  have h := real_d_aux ht
  have hRatio := (analyticAt_tau h.2).comp (f := fun u : ℂ => 1 - u⁻¹) h₂
  have hPeriod := (slitPeriod_analyticOnNhd _ h.1).comp (f := fun u : ℂ => 1 - u) h₁
  exact ((hRatio.add analyticAt_const).mul hPeriod).div_const

private theorem dPeriod_ne_zero (upperA : Bool) {t : ℝ} (ht : 1 < t) :
    dPeriod upperA (t : ℂ) ≠ 0 := by
  have him := tau_im_pos (real_d_aux ht).2
  have hs : tau (1 - (t : ℂ)⁻¹) + lipSign upperA ≠ 0 := by
    intro h
    have hei := congrArg Complex.im h
    cases upperA <;> simp [lipSign] at hei <;> linarith
  exact div_ne_zero (mul_ne_zero hs (slitPeriod_ne_zero (real_d_aux ht).1)) I_ne_zero

private theorem deriv_dPeriod_eq {upperA : Bool} {t : ℂ} (ht : t ∈ dLip upperA) :
    deriv (dPeriod upperA) t = deriv slitPeriod t :=
  Filter.EventuallyEq.deriv_eq <|
    (show ∀ᶠ u in 𝓝 t, u ∈ dLip upperA from
      (isOpen_dLip upperA).mem_nhds ht).mono fun _ hu => dPeriod_eq_slit hu

/-- The D boundary value and its native derivative are both limits from
the designated open lip. -/
theorem dPeriod_boundary (upperA : Bool) {t : ℝ} (ht : 1 < t) :
    Tendsto slitPeriod (𝓝[dLip upperA] (t : ℂ)) (𝓝 (dPeriod upperA t)) ∧
    Tendsto (deriv slitPeriod) (𝓝[dLip upperA] (t : ℂ)) (𝓝 (deriv (dPeriod upperA) t)) := by
  have h := dPeriod_analyticAt upperA ht
  have he : ∀ᶠ u in 𝓝[dLip upperA] (t : ℂ), u ∈ dLip upperA := self_mem_nhdsWithin
  exact ⟨(h.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr'
      (he.mono fun _ hu => dPeriod_eq_slit hu),
    (h.deriv.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr'
      (he.mono fun _ hu => deriv_dPeriod_eq hu)⟩

private theorem dLip_neBot (upperA : Bool) (t : ℝ) :
    (𝓝[dLip upperA] (t : ℂ)).NeBot := by
  let s : ℂ := if upperA then -Complex.I else Complex.I
  let path : ℝ → ℂ := fun v => (t : ℂ) + (v : ℂ) * s
  have hc : Continuous path := by unfold path; fun_prop
  have h₀ : path 0 = t := by simp [path]
  have hp : Tendsto path (𝓝[>] (0 : ℝ)) (𝓝[dLip upperA] (t : ℂ)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · rw [← h₀]
      exact hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with v hv
      have hv' : 0 < v := hv
      cases upperA <;> simpa [path, s, dLip, add_im, mul_im] using hv'
  exact (show (Filter.map path (𝓝[>] (0 : ℝ))).NeBot from inferInstance).mono hp

private theorem chartD_complementary_correction (upperA : Bool) {t : ℝ} (ht : 1 < t) :
    periodCorrection slitPeriod (1 - (t : ℂ)) + periodCorrection (dPeriod upperA) t =
      1 / ((Real.pi : ℂ) * slitPeriod (1 - (t : ℂ)) * dPeriod upperA t) := by
  let L := 𝓝[dLip upperA] (t : ℂ)
  have : L.NeBot := dLip_neBot upperA t
  have ha := slitPeriod_analyticOnNhd _ (real_d_aux ht).1
  have hc : Tendsto (fun u : ℂ => 1 - u) L (𝓝 (1 - (t : ℂ))) :=
    ((continuous_const.sub continuous_id).continuousAt.tendsto).mono_left nhdsWithin_le_nhds
  have hA := ha.continuousAt.tendsto.comp hc
  have hdA := ha.deriv.continuousAt.tendsto.comp hc
  have hD := dPeriod_boundary upperA ht
  have hId : Tendsto id L (𝓝 (t : ℂ)) := nhdsWithin_le_nhds
  have hOne : Tendsto (fun _ : ℂ => (1 : ℂ)) L (𝓝 1) := tendsto_const_nhds
  have hPi : Tendsto (fun _ : ℂ => (Real.pi : ℂ)) L (𝓝 (Real.pi : ℂ)) := tendsto_const_nhds
  have hCA := ((hc.mul (hOne.sub hc)).mul hdA).div hA
    (slitPeriod_ne_zero (real_d_aux ht).1)
  have hCD := ((hId.mul (hOne.sub hId)).mul hD.2).div hD.1
    (dPeriod_ne_zero upperA ht)
  have hden := (hPi.mul hA).mul hD.1
  have hn : (Real.pi : ℂ) * slitPeriod (1 - (t : ℂ)) * dPeriod upperA t ≠ 0 :=
    mul_ne_zero (mul_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero)
      (slitPeriod_ne_zero (real_d_aux ht).1)) (dPeriod_ne_zero upperA ht)
  have he : (fun u : ℂ =>
      periodCorrection slitPeriod (1 - u) + periodCorrection slitPeriod u) =ᶠ[L]
      (fun u : ℂ => 1 / ((Real.pi : ℂ) * slitPeriod (1 - u) * slitPeriod u)) := by
    filter_upwards [self_mem_nhdsWithin] with u hu
    have hw := complementary_correction (mem_doubleSlit_of_im (dLip_im_ne_zero hu))
    simpa only [add_comm, mul_right_comm] using hw
  exact tendsto_nhds_unique_of_eventuallyEq (hCA.add hCD)
    (hOne.div hden hn) he

/-- The period correction in each native chart uses its actual Euler germ. -/
def chartCorrection (upperA : Bool) (c : Chart) (z : ℂ) : ℂ :=
  periodCorrection (match c with
    | .A | .B => slitPeriod
    | .D => dPeriod upperA) (parameter c z)

/-- The Pfaff period on the real overlap has the chart's chosen A root. -/
theorem chartB_pfaff_period {z : ℝ} (hz : 0 < z) :
    slitPeriod (1 - (z : ℂ)) =
      FourPoint.OriginalFourMActualChart.periodRoot .A z * slitPeriod (parameter .A (z : ℂ)) := by
  have hz₀ : (z : ℂ) ≠ 0 := ofReal_ne_zero.mpr hz.ne'
  have he := pfaff (chartA_mem hz)
  rw [parameter, pfaffMap_eq _ (inv_ne_zero hz₀), inv_inv, sub_sub_cancel] at he
  rw [he]
  change ((z : ℂ)⁻¹) ^ (1 / 2 : ℂ) * _ = ((Real.sqrt z : ℝ) : ℂ)⁻¹ * _
  rw [← ofReal_inv, show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num,
    ← ofReal_cpow (inv_nonneg.mpr hz.le), ← Real.sqrt_eq_rpow, Real.sqrt_inv, ofReal_inv]
  rw [parameter, ofReal_inv]

/-- Both spatial kernels have the exact complementary-period covariance
discrepancy. The factors in front of the A kernel are its squared lifts. -/
theorem covariance_discrepancies (upperA : Bool) {z : ℝ} (hz : 0 < z) (hz1 : z < 1)
    {x X : ℂ} (hx : (z : ℂ) * x - 1 ≠ 0) (hX : (z : ℂ) * X - 1 ≠ 0)
    (hxx : x - X ≠ 0) :
    let zc : ℂ := z
    let rA := parameter .A zc
    let rD := parameter .D zc
    let old := spatialKernel (1 - rA) x X - chartCorrection upperA .A zc
    let newB := spatialKernel (1 - zc) (pullB zc x) (pullB zc X) -
      chartCorrection upperA .B zc
    let newD := spatialKernel (1 - rD) (pullD zc x) (pullD zc X) -
      chartCorrection upperA .D zc
    (-Complex.I * (Real.sqrt z : ℂ))^2 * old - newB =
      1 / ((Real.pi : ℂ) * slitPeriod (1 - zc) * slitPeriod zc) ∧
    Complex.I^2 * old - newD = 1 / ((Real.pi : ℂ) * slitPeriod rA * dPeriod upperA rD) := by
  let C : ℂ → ℂ := fun r =>
    if r = parameter .D (z : ℂ) then periodCorrection (dPeriod upperA) r
    else periodCorrection slitPeriod r
  have hinv : 1 < z⁻¹ := (one_lt_inv₀ hz).2 hz1
  have hA : parameter .A (z : ℂ) ≠ parameter .D (z : ℂ) := by
    intro h
    have he := congrArg Complex.re h
    simp only [parameter, sub_re, one_re, ← ofReal_inv, ofReal_re] at he
    linarith
  have hB : (z : ℂ) ≠ parameter .D (z : ℂ) := by
    intro h
    have he := congrArg Complex.re h
    simp only [parameter, ← ofReal_inv, ofReal_re] at he
    linarith
  have hBD : parameter .B (z : ℂ) ≠ parameter .D (z : ℂ) := hB
  have h := FourPoint.OriginalFourMActualChart.covariance_discrepancy hz hz1 hx hX hxx C
  dsimp only at h
  simp only [C, ite_eq_right hA, ite_eq_right hB, ite_eq_right hBD, ite_eq_left rfl] at h
  have hw := complementary_correction (r := 1 - (z : ℂ))
    (doubleSlit_of_re (by simpa [sub_re] using sub_pos.mpr hz1)
      (by simpa [sub_re] using hz))
  have hd := chartD_complementary_correction upperA hinv
  rw [sub_sub_cancel] at hw
  rw [← chartB_pfaff_correction hz] at hw
  rw [ofReal_inv] at hd
  exact ⟨h.1.trans hw, h.2.trans hd⟩

private theorem dRoot_limit (upperA : Bool) {t : ℝ} (ht : 1 < t) :
    Tendsto (fun u : ℂ => (1 - u) ^ (1 / 2 : ℂ)) (𝓝[dLip upperA] (t : ℂ))
      (𝓝 (lipSign upperA * Complex.I * (Real.sqrt (t - 1) : ℂ))) := by
  let a : ℂ := 1 - (t : ℂ)
  let L := 𝓝[dLip upperA] (t : ℂ)
  have ha : a.re < 0 := by simpa [a, sub_re] using sub_neg.mpr ht
  have hai : a.im = 0 := by simp [a]
  have hlog : Tendsto (fun u : ℂ => Complex.log (1 - u)) L
      (𝓝 ((Real.log ‖a‖ : ℂ) + lipSign upperA * ((Real.pi : ℂ) * Complex.I))) := by
    have hc : Tendsto (fun u : ℂ => 1 - u) L (𝓝 a) :=
      (continuous_const.sub continuous_id).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    cases upperA
    · have hm : Tendsto (fun u : ℂ => 1 - u) L (𝓝[{v : ℂ | v.im < 0}] a) := by
        refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hc ?_
        filter_upwards [self_mem_nhdsWithin] with u hu
        simpa using (show 0 < u.im from hu)
      simpa [lipSign, sub_eq_add_neg, Function.comp_def] using
        (Complex.tendsto_log_nhdsWithin_im_neg_of_re_neg_of_im_zero ha hai).comp hm
    · have hm : Tendsto (fun u : ℂ => 1 - u) L (𝓝[{v : ℂ | 0 ≤ v.im}] a) := by
        refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hc ?_
        filter_upwards [self_mem_nhdsWithin] with u hu
        simpa using (show u.im < 0 from hu).le
      simpa [lipSign, Function.comp_def] using
        (Complex.tendsto_log_nhdsWithin_im_nonneg_of_re_neg_of_im_zero ha hai).comp hm
  have hn : ‖a‖ = t - 1 := by
    rw [show a = -((t - 1 : ℝ) : ℂ) by push_cast; unfold a; ring,
      norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (sub_pos.mpr ht)]
  have hreal : Complex.exp ((Real.log ‖a‖ : ℂ) * (1 / 2 : ℂ)) =
      (Real.sqrt (t - 1) : ℂ) := by
    rw [hn, Real.sqrt_eq_rpow, Real.rpow_def_of_pos (sub_pos.mpr ht), ofReal_exp]
    push_cast
    rfl
  have hphase : Complex.exp (lipSign upperA * ((Real.pi : ℂ) * Complex.I) * (1 / 2 : ℂ)) =
      lipSign upperA * Complex.I := by
    cases upperA
    · rw [show lipSign false * ((Real.pi : ℂ) * Complex.I) * (1 / 2 : ℂ) =
        -((Real.pi : ℂ) / 2 * Complex.I) by simp [lipSign]; ring,
        Complex.exp_neg, Complex.exp_pi_div_two_mul_I, Complex.inv_I]
      simp [lipSign]
    · rw [show lipSign true * ((Real.pi : ℂ) * Complex.I) * (1 / 2 : ℂ) =
        (Real.pi : ℂ) / 2 * Complex.I by simp [lipSign]; ring, Complex.exp_pi_div_two_mul_I]
      simp [lipSign]
  have hl := Complex.continuous_exp.continuousAt.tendsto.comp
    (hlog.mul_const (1 / 2 : ℂ))
  have he : ((Real.log ‖a‖ : ℂ) + lipSign upperA * ((Real.pi : ℂ) * Complex.I)) *
      (1 / 2 : ℂ) = (Real.log ‖a‖ : ℂ) * (1 / 2 : ℂ) +
        lipSign upperA * ((Real.pi : ℂ) * Complex.I) * (1 / 2 : ℂ) := add_mul _ _ _
  rw [he, Complex.exp_add, hreal, hphase, mul_comm] at hl
  refine hl.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with u hu
  have hu' : 1 - u ≠ 0 := by
    intro h
    exact dLip_im_ne_zero hu (by simpa using congrArg Complex.im h)
  exact (Complex.cpow_def_of_ne_zero hu' _).symm

/-- On the actual D lower lip the principal root limits to the chosen
chart lift. On the conjugate upper lip it limits to its negative. -/
theorem chartD_root_boundary (upperA : Bool) {z : ℝ} (hz : 0 < z) (hz1 : z < 1) :
    Tendsto (fun u : ℂ => (1 - u) ^ (1 / 2 : ℂ))
      (𝓝[dLip upperA] (parameter .D (z : ℂ)))
      (𝓝 (lipSign upperA * FourPoint.OriginalFourMActualChart.periodRoot .D z)) := by
  have ht := (one_lt_inv₀ hz).2 hz1
  have hl := dRoot_limit upperA ht
  have h : z⁻¹ - 1 = (1 - z) / z := by field_simp
  rw [h, Real.sqrt_div (sub_nonneg.mpr hz1.le), ofReal_div, ofReal_inv] at hl
  change Tendsto _ (𝓝[dLip upperA] ((z : ℂ)⁻¹))
    (𝓝 (lipSign upperA * (Complex.I * (Real.sqrt (1 - z) : ℂ) / (Real.sqrt z : ℂ))))
  simpa only [mul_div_assoc, mul_assoc] using hl

open Matrix LatticeGeneratingFieldLocality

private def gramQuadratic (D : LatticeData) (M : Fin D.rank → ℂ) : ℂ :=
  M ⬝ᵥ (D.G.map (Int.cast : ℤ → ℂ)) *ᵥ M

private theorem gramQuadratic_smul (D : LatticeData) (a : ℂ) (M : Fin D.rank → ℂ) :
    gramQuadratic D (a • M) = a ^ 2 * gramQuadratic D M := by
  rw [gramQuadratic, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, gramQuadratic]
  simp only [smul_eq_mul]
  ring

private theorem complementary_source_exponent (D : LatticeData) (M : Fin D.rank → ℂ)
    {p q a : ℂ} (hp : p ≠ 0) (hq : q ≠ 0) (ha : a ^ 2 = -1) :
    let ζ := (Complex.I / (2 * (Real.pi : ℂ) * p) * a) • M
    let τ := Complex.I * q / p
    2 * (Real.pi : ℂ) * Complex.I * gramQuadratic D ζ / τ =
      (1 / ((Real.pi : ℂ) * p * q)) * gramQuadratic D M / 2 := by
  dsimp only
  rw [gramQuadratic_smul, mul_pow, div_pow, Complex.I_sq, ha]
  have hπ := ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp [hp, hq, hπ, Complex.I_ne_zero]

/-- The exponent of the forward shifted theta multiplier is one half of
the actual covariance discrepancy contracted with the new Gram source.
The inverse multiplier consequently has the negative of this exponent. -/
theorem chart_source_exponents (upperA : Bool) {z : ℝ} (hz : 0 < z) (hz1 : z < 1)
    (D : LatticeData) (MB MD : Fin D.rank → ℂ) :
    let rA := parameter .A (z : ℂ)
    let rD := parameter .D (z : ℂ)
    let pB := slitPeriod (1 - (z : ℂ))
    let qB := slitPeriod (z : ℂ)
    let pD := slitPeriod rA
    let qD := dPeriod upperA rD
    let aB := FourPoint.OriginalFourMActualChart.periodRoot .A z * (-Complex.I * (Real.sqrt z : ℂ))
    let ζB := (Complex.I / (2 * (Real.pi : ℂ) * pB) * aB) • MB
    let ζD := (Complex.I / (2 * (Real.pi : ℂ) * pD) * Complex.I) • MD
    2 * (Real.pi : ℂ) * Complex.I * gramQuadratic D ζB / (Complex.I * qB / pB) =
      (1 / ((Real.pi : ℂ) * pB * qB)) * gramQuadratic D MB / 2 ∧
    2 * (Real.pi : ℂ) * Complex.I * gramQuadratic D ζD / (Complex.I * qD / pD) =
      (1 / ((Real.pi : ℂ) * pD * qD)) * gramQuadratic D MD / 2 := by
  dsimp only
  have hs : (Real.sqrt z : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.2 hz).ne'
  have hb : FourPoint.OriginalFourMActualChart.periodRoot .A z *
      (-Complex.I * (Real.sqrt z : ℂ)) = -Complex.I := by
    change (Real.sqrt z : ℂ)⁻¹ * (-Complex.I * (Real.sqrt z : ℂ)) = _
    rw [mul_comm (-Complex.I), ← mul_assoc, inv_mul_cancel₀ hs, one_mul]
  have hp := slitPeriod_ne_zero (r := 1 - (z : ℂ))
    (slit_of_re_lt (by simpa [sub_re] using hz))
  have hq := slitPeriod_ne_zero (r := (z : ℂ)) (slit_of_re_lt (by simpa using hz1))
  have ht := dPeriod_ne_zero upperA ((one_lt_inv₀ hz).2 hz1)
  rw [ofReal_inv] at ht
  exact ⟨complementary_source_exponent D MB hp hq (by rw [hb, neg_sq, Complex.I_sq]),
    complementary_source_exponent D MD (slitPeriod_ne_zero (chartA_mem hz)) ht Complex.I_sq⟩

end D5.S3.VertexAlgebra.TwistedGround.OriginalFourMPeriodSource
