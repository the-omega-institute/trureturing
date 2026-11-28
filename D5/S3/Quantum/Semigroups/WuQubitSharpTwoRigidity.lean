/- GID: D5/S3/Quantum/Semigroups/WuQubitSharpTwoRigidity
   generality: I
   mirror-B: D5/B/S3/Quantum/Semigroups/WuQubitSharpTwoRigidity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Closed-spectrum normalized qubit entropy deficit, exact equality, and the tracial 4/3 stability floor. -/

import D5.S3.QuantumChannels.ContractionSpectrumOrder
import Mathlib.Analysis.SpecialFunctions.Artanh
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Sharp normalized qubit two-entropy deficit on the closed spectrum

Wu arXiv:2610.33686v1, (3.6)–(3.10) at p = p' = 2.
Here h = β/2, v = tanh u is the spectral polarization of the normalized
sandwiched state, and z is its Bloch direction along the Gibbs axis.
The physical range is h ≥ 0, 0 ≤ v ≤ 1, -1 ≤ z ≤ 1.
The scalar deficit statements below in fact hold for every real z.

We use the continuous entropy expression with Real.log 0 = 0, so v = 1
represents a rank-one state. The coefficient called thermalBias here is
sinh(h)/(1+cosh(h)), distinct from Wu's exponent parameter k = 0 at p = 2.
-/

noncomputable section

open Set

namespace D5.S3.Quantum.Semigroups.WuQubitSharpTwoRigidity

set_option autoImplicit false

/-- The entropy contribution from the two eigenvalues (1 ± v)/2. -/
def polarizationEntropy (v : ℝ) : ℝ :=
  ((1 + v) * Real.log (1 + v) + (1 - v) * Real.log (1 - v)) / 2

/-- The complementary spectral polarization. -/
def spectralRoot (v : ℝ) : ℝ := Real.sqrt (1 - v ^ 2)

def thermalBias (h : ℝ) : ℝ := Real.sinh h / (1 + Real.cosh h)

/-- The sharp coefficient in Wu's normalized deficit, at exponent two. -/
def sharpCoefficient (h : ℝ) : ℝ :=
  if h = 0 then 1 / 2 else thermalBias h / h

/-- Equation (3.6), with the continuous extension to rank one. -/
def normalizedEntropy (h v z : ℝ) : ℝ :=
  polarizationEntropy v + Real.log (Real.cosh h) - h * v * z

/-- Equation (3.7) at exponent two, where the prefactor is one. -/
def normalizedEnergy (h v z : ℝ) : ℝ :=
  1 - (1 + spectralRoot v) / (2 * Real.cosh h) +
    (1 - spectralRoot v) * z ^ 2 / (2 * Real.cosh h) -
    Real.tanh h * v * z

def normalizedDeficit (h v z : ℝ) : ℝ :=
  normalizedEnergy h v z - sharpCoefficient h * normalizedEntropy h v z

/-- The radial remainder in the quadratic completion of the deficit. -/
def radialDeficit (h v : ℝ) : ℝ :=
  1 - (1 + spectralRoot v) / (1 + Real.cosh h) -
    sharpCoefficient h * (polarizationEntropy v + Real.log (Real.cosh h))

section SourceCoordinates

theorem polarizationEntropy_one : polarizationEntropy 1 = Real.log 2 := by
  norm_num [polarizationEntropy]

theorem continuous_polarizationEntropy : Continuous polarizationEntropy := by
  have hp : Continuous (fun v : ℝ => 1 + v) := continuous_const.add continuous_id
  have hm : Continuous (fun v : ℝ => 1 - v) := continuous_const.sub continuous_id
  exact ((Real.continuous_mul_log.comp hp).add (Real.continuous_mul_log.comp hm)).div_const 2

theorem continuous_radialDeficit (h : ℝ) : Continuous (radialDeficit h) := by
  unfold radialDeficit spectralRoot
  have hs : Continuous (fun v : ℝ => Real.sqrt (1 - v ^ 2)) := by fun_prop
  exact (continuous_const.sub ((continuous_const.add hs).div_const _)).sub
    (continuous_const.mul (continuous_polarizationEntropy.add continuous_const))

/-- Entropy in Wu's full-rank hyperbolic parameterization. -/
theorem polarizationEntropy_tanh (u : ℝ) :
    polarizationEntropy (Real.tanh u) =
      u * Real.tanh u - Real.log (Real.cosh u) := by
  have hc := (Real.cosh_pos u).ne'
  have hp : 1 + Real.tanh u = Real.exp u / Real.cosh u := by
    rw [Real.tanh_eq_sinh_div_cosh, ← Real.cosh_add_sinh]
    field_simp [hc]
  have hm : 1 - Real.tanh u = Real.exp (-u) / Real.cosh u := by
    rw [Real.tanh_eq_sinh_div_cosh, ← Real.cosh_sub_sinh]
    field_simp [hc]
  have hlogp : Real.log (1 + Real.tanh u) = u - Real.log (Real.cosh u) := by
    rw [hp, Real.log_div (Real.exp_pos _).ne' hc, Real.log_exp]
  have hlogm : Real.log (1 - Real.tanh u) = -u - Real.log (Real.cosh u) := by
    rw [hm, Real.log_div (Real.exp_pos _).ne' hc, Real.log_exp]
  rw [polarizationEntropy, hlogp, hlogm]
  ring

theorem spectralRoot_tanh (u : ℝ) :
    spectralRoot (Real.tanh u) = 1 / Real.cosh u := by
  unfold spectralRoot
  apply (Real.sqrt_eq_iff_eq_sq (sub_nonneg.mpr (Real.tanh_sq_lt_one u).le)
    (one_div_nonneg.mpr (Real.cosh_pos u).le)).mpr
  rw [Real.tanh_eq_sinh_div_cosh, div_pow, Real.sinh_sq]
  field_simp [(Real.cosh_pos u).ne']
  ring

theorem normalizedEntropy_tanh (h u z : ℝ) :
    normalizedEntropy h (Real.tanh u) z =
      u * Real.tanh u - Real.log (Real.cosh u) + Real.log (Real.cosh h) -
        h * z * Real.tanh u := by
  rw [normalizedEntropy, polarizationEntropy_tanh]
  ring

theorem normalizedEnergy_tanh (h u z : ℝ) :
    normalizedEnergy h (Real.tanh u) z =
      1 - ((1 - z ^ 2) + (1 + z ^ 2) / Real.cosh u) / (2 * Real.cosh h) -
        Real.tanh h * Real.tanh u * z := by
  rw [normalizedEnergy, spectralRoot_tanh]
  ring

/-- The hyperbolic coefficient in (3.8)–(3.9) for h > 0 and p = 2. -/
theorem sharpCoefficient_eq_wu {h : ℝ} (hh : 0 < h) :
    sharpCoefficient h =
      2 * Real.sinh (h / 2) * Real.sinh (h / 2) / (h * Real.sinh h) := by
  have hc : 0 < 1 + Real.cosh h := by positivity
  have hs := Real.sinh_pos_iff.mpr hh
  have hhalf : 2 * Real.sinh (h / 2) * Real.sinh (h / 2) = Real.cosh h - 1 := by
    have he := Real.cosh_two_mul (h / 2)
    rw [show 2 * (h / 2) = h by ring] at he
    nlinarith [Real.cosh_sq_sub_sinh_sq (h / 2)]
  have hk : thermalBias h = (Real.cosh h - 1) / Real.sinh h := by
    unfold thermalBias
    apply (div_eq_div_iff hc.ne' hs.ne').mpr
    nlinarith [Real.cosh_sq_sub_sinh_sq h]
  rw [sharpCoefficient, ite_eq_right hh.ne', hk, hhalf]
  field_simp [hh.ne', hs.ne']

theorem sharpCoefficient_mul (h : ℝ) :
    sharpCoefficient h * h = thermalBias h := by
  by_cases hh : h = 0
  · simp [hh, sharpCoefficient, thermalBias]
  · simp [sharpCoefficient, hh]

private theorem tanh_sub_bias (h : ℝ) :
    Real.tanh h - thermalBias h = thermalBias h / Real.cosh h := by
  rw [Real.tanh_eq_sinh_div_cosh, thermalBias]
  field_simp [(Real.cosh_pos h).ne', (show 0 < 1 + Real.cosh h by positivity).ne']
  ring

/-- The expansion of (3.8)–(3.10). The z-linear entropy term is already
combined with the physical energy term. -/
theorem normalizedDeficit_eq_expanded (h v z : ℝ) :
    normalizedDeficit h v z =
      1 - (1 + spectralRoot v) / (2 * Real.cosh h) +
        (1 - spectralRoot v) * z ^ 2 / (2 * Real.cosh h) -
        (thermalBias h / Real.cosh h) * v * z -
        sharpCoefficient h * (polarizationEntropy v + Real.log (Real.cosh h)) := by
  calc
    normalizedDeficit h v z =
      1 - (1 + spectralRoot v) / (2 * Real.cosh h) +
        (1 - spectralRoot v) * z ^ 2 / (2 * Real.cosh h) -
        (Real.tanh h - sharpCoefficient h * h) * v * z -
        sharpCoefficient h * (polarizationEntropy v + Real.log (Real.cosh h)) := by
          unfold normalizedDeficit normalizedEnergy normalizedEntropy
          ring
    _ = _ := by rw [sharpCoefficient_mul, tanh_sub_bias]

end SourceCoordinates

section RadialRigidity

private theorem sinh_ratio_strictMonoOn :
    StrictMonoOn (fun u : ℝ => Real.sinh u / u) (Ioi 0) := by
  have haux : ∀ u : ℝ, 0 < u → 0 < u * Real.cosh u - Real.sinh u := by
    have hmono : StrictMonoOn (fun x : ℝ => x * Real.cosh x - Real.sinh x)
        (Ici 0) := by
      refine strictMonoOn_of_deriv_pos (convex_Ici _) ?_ ?_
      · exact ((continuous_id.mul Real.continuous_cosh).sub
          Real.continuous_sinh).continuousOn
      · intro x hx
        rw [interior_Ici] at hx
        have hx0 : 0 < x := hx
        have hd : HasDerivAt (fun t : ℝ => t * Real.cosh t - Real.sinh t)
            (x * Real.sinh x) x := by
          convert (((hasDerivAt_id x).mul (Real.hasDerivAt_cosh x)).sub
            (Real.hasDerivAt_sinh x)) using 1
          · rfl
          · simp only [id_eq]
            ring
        rw [hd.deriv]
        exact mul_pos hx0 (Real.sinh_pos_iff.mpr hx0)
    intro u hu
    have hzero : (0 : ℝ) ∈ Ici 0 := by
      change 0 ≤ (0 : ℝ)
      exact le_rfl
    simpa using hmono hzero (show u ∈ Ici 0 from hu.le) hu
  refine strictMonoOn_of_deriv_pos (convex_Ioi _) ?_ ?_
  · exact Real.continuous_sinh.continuousOn.div continuous_id.continuousOn
      (fun x hx => (show 0 < x from hx).ne')
  · intro u hu
    rw [interior_Ioi] at hu
    have hu0 : 0 < u := hu
    have hd : HasDerivAt (fun t : ℝ => Real.sinh t / t)
        ((u * Real.cosh u - Real.sinh u) / u ^ 2) u := by
      convert ((Real.hasDerivAt_sinh u).div (hasDerivAt_id u) hu0.ne') using 1
      · rfl
      · simp only [id_eq]
        ring
    rw [hd.deriv]
    exact div_pos (haux u hu0) (pow_pos hu0 2)

private theorem tanh_nonneg {h : ℝ} (hh : 0 ≤ h) : 0 ≤ Real.tanh h := by
  rw [Real.tanh_eq_sinh_div_cosh]
  exact div_nonneg (Real.sinh_nonneg_iff.mpr hh) (Real.cosh_pos h).le

private theorem tanh_pos {h : ℝ} (hh : 0 < h) : 0 < Real.tanh h := by
  rw [Real.tanh_eq_sinh_div_cosh]
  exact div_pos (Real.sinh_pos_iff.mpr hh) (Real.cosh_pos h)

private theorem tanh_mem (h : ℝ) : Real.tanh h ∈ Ioo (-1 : ℝ) 1 :=
  ⟨Real.neg_one_lt_tanh h, Real.tanh_lt_one h⟩

private theorem one_sub_sq_pos {v : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1) :
    0 < 1 - v ^ 2 := by
  have hv0 : 0 < v := hv.1
  have hv1 : v < 1 := hv.2
  nlinarith [mul_pos hv0 (sub_pos.mpr hv1)]

theorem polarizationEntropy_hasDerivAt {v : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt polarizationEntropy (Real.artanh v) v := by
  have hp : 0 < 1 + v := by linarith [hv.1]
  have hm : 0 < 1 - v := sub_pos.mpr hv.2
  have hdplus : HasDerivAt (fun t : ℝ => 1 + t) 1 v :=
    (hasDerivAt_id v).const_add 1
  have hdminus : HasDerivAt (fun t : ℝ => 1 - t) (-1) v :=
    (hasDerivAt_id v).const_sub 1
  have hd : HasDerivAt polarizationEntropy
      (((Real.log (1 + v) + 1) * 1 + (Real.log (1 - v) + 1) * (-1)) / 2) v :=
    (((Real.hasDerivAt_mul_log hp.ne').comp v hdplus).add
      ((Real.hasDerivAt_mul_log hm.ne').comp v hdminus)).div_const 2
  have hv' : v ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [hv.1], hv.2.le⟩
  rw [Real.artanh_eq_half_log hv', Real.log_div hp.ne' hm.ne']
  convert hd using 1
  ring

private theorem spectralRoot_hasDerivAt {v : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt spectralRoot (-v / spectralRoot v) v := by
  have hd : HasDerivAt (fun t : ℝ => 1 - t ^ 2) (-(2 * v)) v := by
    convert ((hasDerivAt_id v).pow 2).const_sub 1 using 1 <;> simp
  have hs := Real.sqrt_pos_of_pos (one_sub_sq_pos hv)
  unfold spectralRoot
  convert hd.sqrt (one_sub_sq_pos hv).ne' using 1
  field_simp [hs.ne']

/-- The v-coordinate derivative of the radial remainder. It has the
same sign as the derivative (2) in the hyperbolic coordinate. -/
theorem radialDeficit_hasDerivAt (h : ℝ) {v : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (radialDeficit h)
      (Real.sinh (Real.artanh v) / (1 + Real.cosh h) -
        sharpCoefficient h * Real.artanh v) v := by
  have hv' : v ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hv.1], hv.2⟩
  rw [Real.sinh_artanh hv']
  have hd := (((spectralRoot_hasDerivAt hv).const_add 1).div_const
    (1 + Real.cosh h)).const_sub 1
  have he := ((polarizationEntropy_hasDerivAt hv).add_const
    (Real.log (Real.cosh h))).const_mul (sharpCoefficient h)
  have hder := hd.sub he
  unfold radialDeficit
  convert hder using 1
  simp only [spectralRoot]
  ring

private theorem sharpCoefficient_eq_ratio {h : ℝ} (hh : 0 < h) :
    sharpCoefficient h = (Real.sinh h / h) / (1 + Real.cosh h) := by
  rw [sharpCoefficient, ite_eq_right hh.ne', thermalBias]
  field_simp [hh.ne', (show 0 < 1 + Real.cosh h by positivity).ne']

private theorem radial_derivative_neg {h u : ℝ} (hu : 0 < u) (huh : u < h) :
    Real.sinh u / (1 + Real.cosh h) - sharpCoefficient h * u < 0 := by
  have hh := hu.trans huh
  have hc : 0 < 1 + Real.cosh h := by positivity
  have hr := sinh_ratio_strictMonoOn (show u ∈ Ioi 0 from hu)
    (show h ∈ Ioi 0 from hh) huh
  have hm := mul_lt_mul_of_pos_right ((div_lt_div_iff_of_pos_right hc).mpr hr) hu
  have hid : ((Real.sinh u / u) / (1 + Real.cosh h)) * u =
      Real.sinh u / (1 + Real.cosh h) := by
    field_simp [hu.ne', hc.ne']
  rw [hid, ← sharpCoefficient_eq_ratio hh] at hm
  exact sub_neg.mpr hm

private theorem radial_derivative_pos {h u : ℝ} (hh : 0 ≤ h) (hhu : h < u) :
    0 < Real.sinh u / (1 + Real.cosh h) - sharpCoefficient h * u := by
  have hc : 0 < 1 + Real.cosh h := by positivity
  have hu := hh.trans_lt hhu
  rcases eq_or_lt_of_le hh with rfl | hh'
  · norm_num [sharpCoefficient] at ⊢
    linarith [(Real.self_lt_sinh_iff).mpr hu]
  · have hr := sinh_ratio_strictMonoOn (show h ∈ Ioi 0 from hh')
      (show u ∈ Ioi 0 from hu) hhu
    have hm := mul_lt_mul_of_pos_right ((div_lt_div_iff_of_pos_right hc).mpr hr) hu
    have hid : ((Real.sinh u / u) / (1 + Real.cosh h)) * u =
        Real.sinh u / (1 + Real.cosh h) := by
      field_simp [hu.ne', hc.ne']
    rw [hid, ← sharpCoefficient_eq_ratio hh'] at hm
    exact sub_pos.mpr hm

private theorem bias_mul_tanh (h : ℝ) :
    thermalBias h * Real.tanh h = 1 - 1 / Real.cosh h := by
  rw [thermalBias, Real.tanh_eq_sinh_div_cosh]
  have hc := (Real.cosh_pos h).ne'
  have hd : 1 + Real.cosh h ≠ 0 := (show 0 < 1 + Real.cosh h by positivity).ne'
  calc
    Real.sinh h / (1 + Real.cosh h) * (Real.sinh h / Real.cosh h) =
        Real.sinh h ^ 2 / ((1 + Real.cosh h) * Real.cosh h) := by
          field_simp [hc, hd]
    _ = _ := by
      rw [Real.sinh_sq]
      field_simp [hc, hd]
      ring

theorem radialDeficit_tanh (h : ℝ) : radialDeficit h (Real.tanh h) = 0 := by
  rw [radialDeficit, spectralRoot_tanh, polarizationEntropy_tanh]
  rw [show h * Real.tanh h - Real.log (Real.cosh h) + Real.log (Real.cosh h) =
    h * Real.tanh h by ring, ← mul_assoc, sharpCoefficient_mul, bias_mul_tanh]
  field_simp [(Real.cosh_pos h).ne', (show 0 < 1 + Real.cosh h by positivity).ne']
  ring

/-- Strict radial decrease on the entire low-polarization side. -/
theorem radialDeficit_strictAntiOn {h : ℝ} (_hh : 0 ≤ h) :
    StrictAntiOn (radialDeficit h) (Icc 0 (Real.tanh h)) := by
  refine strictAntiOn_of_deriv_neg (convex_Icc _ _)
    (continuous_radialDeficit h).continuousOn ?_
  intro v hv
  rw [interior_Icc] at hv
  have hv' : v ∈ Ioo (0 : ℝ) 1 := ⟨hv.1, hv.2.trans (Real.tanh_lt_one h)⟩
  have hv'' : v ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hv'.1], hv'.2⟩
  have hu : 0 < Real.artanh v := Real.artanh_pos hv'
  have huh : Real.artanh v < h := by
    rw [← Real.artanh_tanh h]
    exact (Real.artanh_lt_artanh_iff hv'' (tanh_mem h)).mpr hv.2
  rw [(radialDeficit_hasDerivAt h hv').deriv]
  exact radial_derivative_neg hu huh

/-- Strict radial increase all the way to the rank-one endpoint.
Only interior differentiability is needed by the mean-value theorem. -/
theorem radialDeficit_strictMonoOn {h : ℝ} (hh : 0 ≤ h) :
    StrictMonoOn (radialDeficit h) (Icc (Real.tanh h) 1) := by
  refine strictMonoOn_of_deriv_pos (convex_Icc _ _)
    (continuous_radialDeficit h).continuousOn ?_
  intro v hv
  rw [interior_Icc] at hv
  have hv' : v ∈ Ioo (0 : ℝ) 1 := ⟨(tanh_nonneg hh).trans_lt hv.1, hv.2⟩
  have hv'' : v ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hv'.1], hv'.2⟩
  have hhu : h < Real.artanh v := by
    rw [← Real.artanh_tanh h]
    exact (Real.artanh_lt_artanh_iff (tanh_mem h) hv'').mpr hv.1
  rw [(radialDeficit_hasDerivAt h hv').deriv]
  exact radial_derivative_pos hh hhu

/-- The radial remainder is strictly positive at every other point of the
closed spectral interval, including rank one. -/
theorem radialDeficit_pos_of_ne {h v : ℝ} (hh : 0 ≤ h)
    (hv : v ∈ Icc (0 : ℝ) 1) (hne : v ≠ Real.tanh h) :
    0 < radialDeficit h v := by
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hstrict := radialDeficit_strictAntiOn hh
      (show v ∈ Icc 0 (Real.tanh h) from ⟨hv.1, hlt.le⟩)
      (show Real.tanh h ∈ Icc 0 (Real.tanh h) from ⟨tanh_nonneg hh, le_rfl⟩)
      hlt
    rwa [radialDeficit_tanh] at hstrict
  · have hstrict := radialDeficit_strictMonoOn hh
      (show Real.tanh h ∈ Icc (Real.tanh h) 1 from ⟨le_rfl, (Real.tanh_lt_one h).le⟩)
      (show v ∈ Icc (Real.tanh h) 1 from ⟨hgt.le, hv.2⟩) hgt
    rwa [radialDeficit_tanh] at hstrict

theorem radialDeficit_nonneg {h v : ℝ} (hh : 0 ≤ h) (hv : v ∈ Icc (0 : ℝ) 1) :
    0 ≤ radialDeficit h v := by
  by_cases he : v = Real.tanh h
  · rw [he, radialDeficit_tanh]
  · exact (radialDeficit_pos_of_ne hh hv he).le

theorem radialDeficit_eq_zero_iff {h v : ℝ} (hh : 0 ≤ h) (hv : v ∈ Icc (0 : ℝ) 1) :
    radialDeficit h v = 0 ↔ v = Real.tanh h := by
  constructor
  · intro hz
    by_contra hne
    exact (radialDeficit_pos_of_ne hh hv hne).ne' hz
  · rintro rfl
    exact radialDeficit_tanh h

end RadialRigidity

section AngularRigidity

private theorem spectralRoot_nonneg (v : ℝ) : 0 ≤ spectralRoot v := Real.sqrt_nonneg _

private theorem spectralRoot_factor {v : ℝ} (hv : v ∈ Icc (0 : ℝ) 1) :
    v ^ 2 / (1 + spectralRoot v) = 1 - spectralRoot v := by
  have hrad : 0 ≤ 1 - v ^ 2 := by
    have hv0 : 0 ≤ v := hv.1
    have hv1 : v ≤ 1 := hv.2
    nlinarith [mul_nonneg hv0 (sub_nonneg.mpr hv1)]
  have hs : spectralRoot v ^ 2 = 1 - v ^ 2 := Real.sq_sqrt hrad
  have hden : 0 < 1 + spectralRoot v := by linarith [spectralRoot_nonneg v]
  apply (div_eq_iff hden.ne').mpr
  nlinarith [hs]

private theorem bias_sq (h : ℝ) :
    thermalBias h ^ 2 = (Real.cosh h - 1) / (Real.cosh h + 1) := by
  rw [thermalBias, div_pow, Real.sinh_sq]
  field_simp [(show 0 < 1 + Real.cosh h by positivity).ne',
    (show 0 < Real.cosh h + 1 by positivity).ne']
  ring

private theorem radial_constant (h : ℝ) :
    1 / (1 + Real.cosh h) - 1 / (2 * Real.cosh h) =
      thermalBias h ^ 2 / (2 * Real.cosh h) := by
  rw [bias_sq]
  field_simp [(Real.cosh_pos h).ne', (show 0 < 1 + Real.cosh h by positivity).ne',
    (show 0 < Real.cosh h + 1 by positivity).ne']
  ring

/-- The square completion is regular on the closed spectrum, even at v = 0.
For v > 0 it is the completion (1) after putting v = tanh u.
The denominator is strictly positive, also at v = 1. -/
theorem normalizedDeficit_eq_radial_add_square (h : ℝ) {v : ℝ}
    (hv : v ∈ Icc (0 : ℝ) 1) (z : ℝ) :
    normalizedDeficit h v z = radialDeficit h v +
      (v * z - thermalBias h * (1 + spectralRoot v)) ^ 2 /
        (2 * Real.cosh h * (1 + spectralRoot v)) := by
  have hc := (Real.cosh_pos h).ne'
  have hs : 1 + spectralRoot v ≠ 0 := by linarith [spectralRoot_nonneg v]
  calc
    normalizedDeficit h v z =
        radialDeficit h v +
          (1 + spectralRoot v) * (1 / (1 + Real.cosh h) - 1 / (2 * Real.cosh h)) +
          (1 - spectralRoot v) * z ^ 2 / (2 * Real.cosh h) -
          (thermalBias h / Real.cosh h) * v * z := by
            rw [normalizedDeficit_eq_expanded]
            unfold radialDeficit
            ring
    _ = radialDeficit h v +
          (1 + spectralRoot v) * (thermalBias h ^ 2 / (2 * Real.cosh h)) +
          (v ^ 2 / (1 + spectralRoot v)) * z ^ 2 / (2 * Real.cosh h) -
          (thermalBias h / Real.cosh h) * v * z := by
            rw [radial_constant, spectralRoot_factor hv]
    _ = _ := by
      field_simp [hc, hs]
      ring

private theorem square_den_pos (h v : ℝ) :
    0 < 2 * Real.cosh h * (1 + spectralRoot v) :=
  mul_pos (mul_pos (by norm_num) (Real.cosh_pos h))
    (by linarith [spectralRoot_nonneg v])

private theorem bias_mul_root_at_tanh (h : ℝ) :
    thermalBias h * (1 + spectralRoot (Real.tanh h)) = Real.tanh h := by
  rw [spectralRoot_tanh, thermalBias, Real.tanh_eq_sinh_div_cosh]
  field_simp [(Real.cosh_pos h).ne', (show 0 < 1 + Real.cosh h by positivity).ne']
  ring

theorem radialDeficit_le_normalizedDeficit (h : ℝ) {v : ℝ}
    (hv : v ∈ Icc (0 : ℝ) 1) (z : ℝ) :
    radialDeficit h v ≤ normalizedDeficit h v z := by
  rw [normalizedDeficit_eq_radial_add_square h hv z]
  exact le_add_of_nonneg_right (div_nonneg (sq_nonneg _) (square_den_pos h v).le)

theorem normalizedDeficit_nonneg {h v : ℝ} (hh : 0 ≤ h)
    (hv : v ∈ Icc (0 : ℝ) 1) (z : ℝ) :
    0 ≤ normalizedDeficit h v z :=
  (radialDeficit_nonneg hh hv).trans (radialDeficit_le_normalizedDeficit h hv z)

/-- Exact normalized equality, including the maximally mixed and rank-one
cases. At h = 0 the orientation carries no information at v = 0. -/
theorem normalizedDeficit_eq_zero_iff {h v : ℝ} (hh : 0 ≤ h)
    (hv : v ∈ Icc (0 : ℝ) 1) (z : ℝ) :
    normalizedDeficit h v z = 0 ↔
      v = Real.tanh h ∧ (h = 0 ∨ z = 1) := by
  constructor
  · intro hzero
    have hrle := radialDeficit_le_normalizedDeficit h hv z
    rw [hzero] at hrle
    have hr : radialDeficit h v = 0 := le_antisymm hrle (radialDeficit_nonneg hh hv)
    have he := (radialDeficit_eq_zero_iff hh hv).mp hr
    refine ⟨he, ?_⟩
    rw [normalizedDeficit_eq_radial_add_square h hv z, hr, zero_add, he,
      bias_mul_root_at_tanh] at hzero
    have hs : (Real.tanh h * z - Real.tanh h) ^ 2 = 0 := by
      exact (div_eq_zero_iff.mp hzero).resolve_right (square_den_pos h (Real.tanh h)).ne'
    have hd : Real.tanh h * z - Real.tanh h = 0 := sq_eq_zero_iff.mp hs
    rcases eq_or_lt_of_le hh with rfl | hh'
    · exact Or.inl rfl
    · right
      have hmul : Real.tanh h * (z - 1) = 0 := by linarith [hd]
      have hz := (mul_eq_zero.mp hmul).resolve_left (tanh_pos hh').ne'
      linarith
  · rintro ⟨he, hz⟩
    rw [normalizedDeficit_eq_radial_add_square h hv z, he, radialDeficit_tanh,
      bias_mul_root_at_tanh]
    rcases hz with rfl | rfl <;> simp

theorem normalizedDeficit_pos_of_ne {h v : ℝ} (hh : 0 ≤ h)
    (hv : v ∈ Icc (0 : ℝ) 1) (z : ℝ)
    (hne : ¬ (v = Real.tanh h ∧ (h = 0 ∨ z = 1))) :
    0 < normalizedDeficit h v z := by
  exact lt_of_le_of_ne (normalizedDeficit_nonneg hh hv z)
    (Ne.symm (fun he => hne ((normalizedDeficit_eq_zero_iff hh hv z).mp he)))

/-- In particular every normalized rank-one qubit has a strictly positive
sharp deficit at each finite nonnegative inverse temperature. -/
theorem normalizedDeficit_rankOne_pos {h : ℝ} (hh : 0 ≤ h) (z : ℝ) :
    0 < normalizedDeficit h 1 z := by
  have hv : (1 : ℝ) ∈ Icc 0 1 := ⟨zero_le_one, le_rfl⟩
  exact (radialDeficit_pos_of_ne hh hv (Real.tanh_lt_one h).ne').trans_le
    (radialDeficit_le_normalizedDeficit h hv z)

end AngularRigidity

section TracialStability

open D5.S3.QuantumChannels.ContractionSpectrumOrder (hasDerivAt_artanh)

private theorem artanh_cubic_bound {t : ℝ} (ht : t ∈ Ioo 0 1) :
    (1 - t ^ 2) * Real.artanh t < t - 2 * t ^ 3 / 3 := by
  have artanhDeriv {x : ℝ} (hx : x ∈ Ico (0 : ℝ) 1) :
      HasDerivAt Real.artanh (1 / (1 - x ^ 2)) x :=
    hasDerivAt_artanh ⟨by linarith [hx.1], hx.2⟩
  have continuousArtanh : ContinuousOn Real.artanh (Ico (0 : ℝ) 1) :=
    fun _ hx => (artanhDeriv hx).continuousAt.continuousWithinAt
  have zeroMem : (0 : ℝ) ∈ Ico 0 1 := ⟨le_rfl, zero_lt_one⟩
  have tMem : t ∈ Ico (0 : ℝ) 1 := ⟨ht.1.le, ht.2⟩
  have self_lt_artanh {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : x < Real.artanh x := by
    have mono : StrictMonoOn (fun y : ℝ => Real.artanh y - y) (Ico 0 1) := by
      refine strictMonoOn_of_deriv_pos (convex_Ico _ _) (continuousArtanh.sub
        continuous_id.continuousOn) ?_
      intro y hy
      rw [interior_Ico] at hy
      have hd : HasDerivAt (fun y : ℝ => Real.artanh y - y) (1 / (1 - y ^ 2) - 1) y :=
        (artanhDeriv ⟨hy.1.le, hy.2⟩).sub (hasDerivAt_id y)
      rw [hd.deriv, sub_pos]
      exact (lt_div_iff₀ (one_sub_sq_pos hy)).mpr (by nlinarith [sq_pos_of_pos hy.1])
    simpa using mono zeroMem (show x ∈ Ico 0 1 from ⟨hx.1.le, hx.2⟩) hx.1
  let gap : ℝ → ℝ := fun x => x - 2 * x ^ 3 / 3 - (1 - x ^ 2) * Real.artanh x
  have continuousGap : ContinuousOn gap (Ico 0 1) := by
    have left : Continuous (fun x : ℝ => x - 2 * x ^ 3 / 3) := by fun_prop
    have factor : Continuous (fun x : ℝ => 1 - x ^ 2) := by fun_prop
    exact left.continuousOn.sub (factor.continuousOn.mul continuousArtanh)
  have mono : StrictMonoOn gap (Ico 0 1) := by
    refine strictMonoOn_of_deriv_pos (convex_Ico _ _) continuousGap ?_
    intro x hx
    rw [interior_Ico] at hx
    have left := (hasDerivAt_id x).sub
      ((((hasDerivAt_id x).pow 3).const_mul 2).div_const 3)
    have factor : HasDerivAt (fun y : ℝ => 1 - y ^ 2) (-(2 * x)) x := by
      convert ((hasDerivAt_id x).pow 2).const_sub 1 using 1 <;> simp
    have hd : HasDerivAt gap (2 * x * (Real.artanh x - x)) x := by
      convert left.sub (factor.mul (artanhDeriv ⟨hx.1.le, hx.2⟩)) using 1
      · rfl
      · simp only [id_eq]
        field_simp [(one_sub_sq_pos hx).ne']
        ring
    rw [hd.deriv]
    exact mul_pos (mul_pos (by norm_num) hx.1) (sub_pos.mpr (self_lt_artanh hx))
  have h := mono zeroMem tMem ht.1
  simpa [gap, sub_pos] using h

private theorem tracial_stability_derivative_pos {v : ℝ} (hv : v ∈ Ioo 0 1) :
    let W := Real.sqrt ((1 + spectralRoot v) / 2)
    0 < (v / spectralRoot v - Real.artanh v) / 2 -
      (2 / 3) * (1 - W) * (v / (W * spectralRoot v)) := by
  let s := spectralRoot v
  let W := Real.sqrt ((1 + s) / 2)
  have hs : 0 < s := Real.sqrt_pos_of_pos (one_sub_sq_pos hv)
  have hs₁ : 0 < 1 + s := by positivity
  have hW : 0 < W := Real.sqrt_pos_of_pos (by positivity)
  -- This coordinate satisfies `artanh v = 2 * artanh t`.
  let t := v / (1 + s)
  have ht : t ∈ Ioo (0 : ℝ) 1 :=
    ⟨div_pos hv.1 hs₁, (div_lt_one hs₁).mpr (by linarith [hv.2])⟩
  have htsq : t ^ 2 * (1 + s) = 1 - s := by
    calc
      t ^ 2 * (1 + s) = v ^ 2 / (1 + s) := by dsimp [t]; field_simp
      _ = 1 - s := spectralRoot_factor ⟨hv.1.le, hv.2.le⟩
  have htplus : (1 + t ^ 2) * (1 + s) = 2 := by nlinarith only [htsq]
  have htminus : (1 - t ^ 2) * (1 + s) = 2 * s := by nlinarith only [htsq]
  have htv : 2 * t / (1 + t ^ 2) = v := by
    apply (div_eq_iff (show 0 < 1 + t ^ 2 by positivity).ne').mpr
    have ht_mul : t * (1 + s) = v := div_mul_cancel₀ v hs₁.ne'
    calc
      2 * t = t * ((1 + t ^ 2) * (1 + s)) := by rw [htplus, mul_comm]
      _ = (t * (1 + s)) * (1 + t ^ 2) := by ring
      _ = v * (1 + t ^ 2) := by rw [ht_mul]
  have hu : Real.artanh v = 2 * Real.artanh t := by
    have ht' : t ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [ht.1], ht.2⟩
    have htan : Real.tanh (2 * Real.artanh t) = v := by
      rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_two_mul, Real.cosh_two_mul,
        Real.sinh_artanh ht', Real.cosh_artanh ht', ← htv]
      field_simp [(Real.sqrt_pos_of_pos (one_sub_sq_pos ht)).ne']
    rw [← htan, Real.artanh_tanh]
  have hrel : (v / s) * (1 - t ^ 2) = 2 * t := by
    rw [(eq_div_iff hs₁.ne').mpr htminus]
    dsimp [t]
    field_simp
  have hvs : 0 < v / s := div_pos hv.1 hs
  have hgap : Real.artanh v < (1 - (2 / 3) * t ^ 2) * (v / s) := by
    apply lt_of_mul_lt_mul_right _ ht.1.le
    calc
      Real.artanh v * t = (v / s) * ((1 - t ^ 2) * Real.artanh t) := by
        rw [hu, ← mul_assoc, hrel]
        ring
      _ < (v / s) * (t - 2 * t ^ 3 / 3) :=
        mul_lt_mul_of_pos_left (artanh_cubic_bound ht) hvs
      _ = ((1 - (2 / 3) * t ^ 2) * (v / s)) * t := by ring
  have hWsq : W ^ 2 = (1 + s) / 2 := Real.sq_sqrt (by positivity)
  have hWunit : W ^ 2 * (1 + t ^ 2) = 1 := by rw [hWsq]; nlinarith only [htplus]
  have hWgap : 4 * (1 - W) ≤ 2 * t ^ 2 * W := by
    apply le_of_mul_le_mul_right _ hW
    nlinarith only [hWunit, sq_nonneg (1 - W)]
  have hweight : (2 / 3) * (1 - W) * (v / (W * s)) ≤ (t ^ 2 / 3) * (v / s) := by
    apply le_of_mul_le_mul_right _ hW
    calc
      (2 / 3) * (1 - W) * (v / (W * s)) * W = (v / s) * (4 * (1 - W)) / 6 := by
        field_simp
        ring
      _ ≤ (v / s) * (2 * t ^ 2 * W) / 6 := by gcongr
      _ = (t ^ 2 / 3) * (v / s) * W := by ring
  change 0 < (v / s - Real.artanh v) / 2 - (2 / 3) * (1 - W) * (v / (W * s))
  linarith only [hgap, hweight]

/-- The tracial radial deficit exceeds the stability floor at every nonzero
polarization, including the rank-one endpoint. -/
private theorem tracial_stability_radial_lt {v : ℝ} (hv : v ∈ Icc 0 1) (hv0 : 0 < v) :
    let W := Real.sqrt ((1 + spectralRoot v) / 2)
    (4 / 3) * (1 - W) ^ 2 < radialDeficit 0 v := by
  let W : ℝ → ℝ := fun x => Real.sqrt ((1 + spectralRoot x) / 2)
  let gap : ℝ → ℝ := fun x => radialDeficit 0 x - (4 / 3) * (1 - W x) ^ 2
  have hW : Continuous W := by dsimp [W, spectralRoot]; fun_prop
  have continuousGap : Continuous gap :=
    (continuous_radialDeficit 0).sub (((continuous_const.sub hW).pow 2).const_mul _)
  have mono : StrictMonoOn gap (Icc 0 1) := by
    refine strictMonoOn_of_deriv_pos (convex_Icc _ _) continuousGap.continuousOn ?_
    intro x hx
    rw [interior_Icc] at hx
    have hs : 0 < spectralRoot x := Real.sqrt_pos_of_pos (one_sub_sq_pos hx)
    have hWx : 0 < W x := Real.sqrt_pos_of_pos (by positivity)
    have hWd : HasDerivAt W (-x / (4 * W x * spectralRoot x)) x := by
      have hd := (((spectralRoot_hasDerivAt hx).const_add 1).div_const 2).sqrt
        (show (1 + spectralRoot x) / 2 ≠ 0 by positivity)
      convert hd using 1
      change -x / (4 * W x * spectralRoot x) = (-x / spectralRoot x / 2) / (2 * W x)
      field_simp
      ring
    have hRd : HasDerivAt (radialDeficit 0) ((x / spectralRoot x - Real.artanh x) / 2) x := by
      have hx' : x ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hx.1], hx.2⟩
      have hd := radialDeficit_hasDerivAt 0 hx
      rw [Real.sinh_artanh hx'] at hd
      convert hd using 1
      norm_num [spectralRoot, sharpCoefficient]
      ring
    have hd : HasDerivAt gap ((x / spectralRoot x - Real.artanh x) / 2 -
        (2 / 3) * (1 - W x) * (x / (W x * spectralRoot x))) x := by
      convert hRd.sub (((hWd.const_sub 1).pow 2).const_mul (4 / 3)) using 1
      field_simp
      ring
    rw [hd.deriv]
    exact tracial_stability_derivative_pos hx
  have hzero : gap 0 = 0 := by
    have hr := radialDeficit_tanh 0
    simp only [Real.tanh_zero] at hr
    norm_num [gap, W, spectralRoot, hr]
  have h := mono (show (0 : ℝ) ∈ Icc 0 1 from ⟨le_rfl, zero_le_one⟩) hv hv0
  rw [hzero] at h
  exact sub_pos.mp h

/-- At zero inverse temperature the normalized one-qubit deficit is strictly
above the `4/3` stability floor for positive polarization. -/
theorem normalizedDeficit_tracial_stability_strict {v : ℝ} (hv : v ∈ Icc 0 1)
    (hv0 : 0 < v) (z : ℝ) :
    let W := Real.sqrt ((1 + spectralRoot v) / 2)
    (4 / 3) * (1 - W) ^ 2 < normalizedDeficit 0 v z :=
  (tracial_stability_radial_lt hv hv0).trans_le (radialDeficit_le_normalizedDeficit 0 hv z)

/-- The `4/3` tracial stability floor on the closed normalized qubit spectrum. -/
theorem normalizedDeficit_tracial_stability {v : ℝ} (hv : v ∈ Icc 0 1) (z : ℝ) :
    let W := Real.sqrt ((1 + spectralRoot v) / 2)
    (4 / 3) * (1 - W) ^ 2 ≤ normalizedDeficit 0 v z := by
  rcases eq_or_lt_of_le hv.1 with hzero | hv0
  · subst v
    have h := (normalizedDeficit_eq_zero_iff (h := 0) le_rfl hv z).mpr (by simp)
    norm_num [spectralRoot, h]
  · exact (normalizedDeficit_tracial_stability_strict hv hv0 z).le

end TracialStability

end D5.S3.Quantum.Semigroups.WuQubitSharpTwoRigidity
