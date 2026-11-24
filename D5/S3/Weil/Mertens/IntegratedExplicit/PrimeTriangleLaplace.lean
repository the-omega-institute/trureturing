/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/PrimeTriangleLaplace
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/PrimeTriangleLaplace
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The centered prime triangle retains nonzero residues at critical-strip zeta zeros. -/

import D5.S3.Weil.Mertens.IntegratedExplicit.CompleteMangoldtLaurent
import D5.S3.Analytic.Laplace.EulerPoleObstruction
import D5.S3.Weil.Mertens.IntegratedExplicit.PrimeQuarterTriangle

/-! The dyadic triangular filter preserves the simple pole contribution of every
zeta zero in the open critical strip, even after subtraction of a continuous
boundary term. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter MeasureTheory Set
open scoped Topology

namespace D5.S3.Weil.Mertens.IntegratedExplicit.PrimeTriangleLaplace

open D5.S3.Weil.Mertens.IntegratedExplicit.CompleteMangoldtLaurent
open D5.S3.Arith.Robin.CompleteMertensPeak (U)
open D5.S3.Weil.Mertens.IntegratedExplicit (U_exp_continuous)
open D5.S3.Analytic.Laplace.EulerPoleObstruction (finiteHead finiteHead_entire kernel)

def multiplier (s : ℂ) : ℂ :=
  (Complex.exp (s * (Real.log 2 : ℂ)) - 1) *
    (Complex.exp (s * (Real.log 2 : ℂ)) - 2)

private theorem multiplier_norm_lower {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    0 < ((2 : ℝ) ^ s.re - 1) * (2 - (2 : ℝ) ^ s.re) ∧
      ((2 : ℝ) ^ s.re - 1) * (2 - (2 : ℝ) ^ s.re) ≤ ‖multiplier s‖ := by
  let z := Complex.exp (s * (Real.log 2 : ℂ))
  have hz : ‖z‖ = (2 : ℝ) ^ s.re := by
    simp only [z, Complex.norm_exp, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero, Real.rpow_def_of_pos (show (0 : ℝ) < 2 by norm_num), mul_comm]
  have h1 : 1 < (2 : ℝ) ^ s.re := Real.one_lt_rpow (by norm_num) hs0
  have h2 : (2 : ℝ) ^ s.re < 2 := by
    simpa only [Real.rpow_one] using
      Real.rpow_lt_rpow_of_exponent_lt (show (1 : ℝ) < 2 by norm_num) hs1
  have hleft : (2 : ℝ) ^ s.re - 1 ≤ ‖z - 1‖ := by
    simpa only [hz, norm_one] using norm_sub_norm_le z (1 : ℂ)
  have hright : 2 - (2 : ℝ) ^ s.re ≤ ‖z - 2‖ := by
    rw [← norm_sub_rev]
    simpa only [hz, Complex.norm_ofNat] using norm_sub_norm_le (2 : ℂ) z
  exact ⟨mul_pos (sub_pos.mpr h1) (sub_pos.mpr h2), by
    simpa only [multiplier, z, norm_mul] using
      mul_le_mul hleft hright (sub_nonneg.mpr h2.le) (norm_nonneg _)⟩

/-- Subtracting a continuous boundary term preserves the nonzero scaled limit. -/
private theorem triangular_filtered_residue {ρ : ℂ} (hz : riemannZeta ρ = 0)
    (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1) {boundary : ℂ → ℂ}
    (hb : ContinuousAt boundary ρ) :
    let c := (analyticOrderNatAt riemannZeta ρ : ℂ) / (ρ * (1 - ρ))
    multiplier ρ * c ≠ 0 ∧
      Tendsto (fun s : ℂ => (s - ρ) * (multiplier s * transform s - boundary s))
        (𝓝[≠] ρ) (𝓝 (multiplier ρ * c)) := by
  dsimp only
  let c := (analyticOrderNatAt riemannZeta ρ : ℂ) / (ρ * (1 - ρ))
  obtain ⟨_, hc, H, hH, hg⟩ := transform_integral_and_zero_germs.2 ρ hz
  have hm : multiplier ρ ≠ 0 :=
    norm_pos_iff.mp ((multiplier_norm_lower hρ0 hρ1).1.trans_le
      (multiplier_norm_lower hρ0 hρ1).2)
  refine ⟨mul_ne_zero hm hc, ?_⟩
  have hM : ContinuousAt multiplier ρ := by unfold multiplier; fun_prop
  let regular := fun s : ℂ => multiplier s * c +
    (s - ρ) * (multiplier s * H s - boundary s)
  have hregular : ContinuousAt regular ρ := by
    dsimp only [regular]
    exact (hM.mul continuousAt_const).add
      ((continuousAt_id.sub continuousAt_const).mul ((hM.mul hH.continuousAt).sub hb))
  have hlimit : Tendsto regular (𝓝[≠] ρ) (𝓝 (multiplier ρ * c)) := by
    have ht : ContinuousWithinAt regular ({ρ} : Set ℂ)ᶜ ρ :=
      hregular.continuousWithinAt
    change Tendsto regular (𝓝[≠] ρ) (𝓝 (regular ρ)) at ht
    simpa only [regular, sub_self, zero_mul, add_zero] using ht
  apply hlimit.congr'
  filter_upwards [hg, @self_mem_nhdsWithin ℂ _ ρ ({ρ} : Set ℂ)ᶜ] with s hs hne
  have hsρ : s - ρ ≠ 0 := sub_ne_zero.mpr (by simpa using hne)
  dsimp only [regular, c]
  rw [hs]
  field_simp
  ring

private def g (t : ℝ) : ℝ := U (Real.exp t)

private theorem forward_shift {s : ℂ} (hs : 1 < s.re) {h : ℝ} (hh : 0 ≤ h) :
    IntegrableOn (kernel (fun t => g (t + h)) s) (Ioi 0) ∧
      (∫ t in Ioi (0 : ℝ), kernel (fun u => g (u + h)) s t) =
        Complex.exp (s * (h : ℂ)) * (transform s - finiteHead g 0 h s) := by
  let f := kernel g s
  have hf : IntegrableOn f (Ioi 0) := (transform_integral_and_zero_germs.1 s hs).1
  have htail : IntegrableOn f (Ioi h) := hf.mono_set (Ioi_subset_Ioi hh)
  have hsplit := intervalIntegral.integral_interval_add_Ioi hf htail
  rw [intervalIntegral.integral_of_le hh] at hsplit
  have horiginal : (∫ t in Ioi (0 : ℝ), f t) = transform s :=
    (transform_integral_and_zero_germs.1 s hs).2
  rw [horiginal] at hsplit
  have htail_eq : (∫ t in Ioi h, f t) = transform s - finiteHead g 0 h s := by
    have heq : finiteHead g 0 h s + (∫ t in Ioi h, f t) = transform s := hsplit
    linear_combination heq
  have htranslated : (Ioi (0 : ℝ)).indicator (fun t => f (t + h)) =
      fun t => (Ioi h).indicator f (t + h) := by
    ext t
    by_cases ht : 0 < t
    · rw [indicator_of_mem (show t ∈ Ioi 0 from ht),
        indicator_of_mem (show t + h ∈ Ioi h by simpa only [mem_Ioi, lt_add_iff_pos_left])]
    · rw [indicator_of_notMem (show t ∉ Ioi 0 from ht),
        indicator_of_notMem (show t + h ∉ Ioi h by simpa only [mem_Ioi, lt_add_iff_pos_left])]
  have hint : IntegrableOn (fun t => f (t + h)) (Ioi 0) := by
    rw [← integrable_indicator_iff measurableSet_Ioi, htranslated]
    exact (measurePreserving_add_right volume h).integrable_comp_of_integrable
      (htail.integrable_indicator measurableSet_Ioi)
  have heq : (∫ t in Ioi (0 : ℝ), f (t + h)) = ∫ t in Ioi h, f t := by
    rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioi, htranslated]
    exact integral_add_right_eq_self ((Ioi h).indicator f) h
  have hfactor : (fun t => kernel (fun u => g (u + h)) s t) =
      fun t => Complex.exp (s * (h : ℂ)) * f (t + h) := by
    ext t
    dsimp [f, kernel]
    rw [← mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  refine ⟨?_, ?_⟩
  · have h' : IntegrableOn (fun t => Complex.exp (s * (h : ℂ)) * f (t + h)) (Ioi 0) :=
      hint.const_mul _
    exact Eq.mpr (congrArg (fun v : ℝ → ℂ => IntegrableOn v (Ioi (0 : ℝ))) hfactor) h'
  · simp_rw [hfactor]
    rw [integral_const_mul, heq, htail_eq]

/-- The exact compact contribution removed when translating the log-Laplace transform. -/
private def cutoffCorrection (s : ℂ) : ℂ :=
  Complex.exp (s * ((2 * Real.log 2 : ℝ) : ℂ)) * finiteHead g 0 (2 * Real.log 2) s -
  3 * Complex.exp (s * (Real.log 2 : ℂ)) * finiteHead g 0 (Real.log 2) s

private theorem cutoffCorrection_entire : Differentiable ℂ cutoffCorrection := by
  have hg (h : ℝ) : Differentiable ℂ (finiteHead g 0 h) :=
    finiteHead_entire U_exp_continuous.integrableOn_Ioc
  unfold cutoffCorrection
  fun_prop (disch := apply hg)

private def logHinge (t : ℝ) : ℝ := g (t + 2 * Real.log 2) - 3 * g (t + Real.log 2) + 2 * g t

private theorem logHinge_eq (t : ℝ) :
    logHinge t = PrimeQuarterTriangle.hinge U (Real.exp t) := by
  have h2 : Real.exp (Real.log 2) = 2 := Real.exp_log (by norm_num)
  have h4 : Real.exp (2 * Real.log 2) = 4 := by
    rw [show 2 * Real.log 2 = Real.log 2 + Real.log 2 by ring, Real.exp_add, h2]
    norm_num
  simp only [logHinge, g, PrimeQuarterTriangle.hinge, Real.exp_add, h2, h4, mul_comm (Real.exp t)]

/-- The transformed actual hinge is the multiplier times the original transform
minus the exact entire correction at the lower end. -/
private theorem logHinge_transform {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (kernel logHinge s) (Ioi 0) ∧
      (∫ t in Ioi (0 : ℝ), kernel logHinge s t) =
        multiplier s * transform s - cutoffCorrection s := by
  let h := Real.log 2
  have hh : 0 ≤ h := Real.log_nonneg (by norm_num)
  obtain ⟨hi2, he2⟩ := forward_shift hs (h := 2 * h) (by positivity)
  obtain ⟨hi1, he1⟩ := forward_shift hs hh
  obtain ⟨hi0, he0⟩ := transform_integral_and_zero_germs.1 s hs
  have hi0' : IntegrableOn (kernel g s) (Ioi 0) := hi0
  have he0' : (∫ t in Ioi (0 : ℝ), kernel g s t) = transform s := he0
  have hsplit : kernel logHinge s =
      fun t => kernel (fun u => g (u + 2 * h)) s t -
        3 * kernel (fun u => g (u + h)) s t + 2 * kernel g s t := by
    ext t
    push_cast [kernel, logHinge, h]
    ring
  rw [hsplit]
  have hidiff : IntegrableOn (fun t => kernel (fun u => g (u + 2 * h)) s t -
      3 * kernel (fun u => g (u + h)) s t) (Ioi 0) := hi2.sub (hi1.const_mul 3)
  refine ⟨hidiff.add (hi0'.const_mul 2), ?_⟩
  rw [integral_add hidiff (hi0'.const_mul 2),
    integral_sub hi2 (hi1.const_mul 3), integral_const_mul, integral_const_mul,
    he2, he1, he0']
  unfold multiplier cutoffCorrection
  dsimp [h]
  rw [show s * (↑(2 * Real.log 2 : ℝ) : ℂ) =
      s * (Real.log 2 : ℂ) + s * (Real.log 2 : ℂ) by push_cast; ring, Complex.exp_add]
  ring

private theorem logHinge_pole {ρ : ℂ} (hz : riemannZeta ρ = 0)
    (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1) :
    let c := (analyticOrderNatAt riemannZeta ρ : ℂ) / (ρ * (1 - ρ))
    multiplier ρ * c ≠ 0 ∧
      Tendsto (fun s : ℂ => (s - ρ) * (multiplier s * transform s - cutoffCorrection s))
        (𝓝[≠] ρ) (𝓝 (multiplier ρ * c)) :=
  triangular_filtered_residue hz hρ0 hρ1 (cutoffCorrection_entire.continuous.continuousAt)

/-- The analytic side of the Laplace transform of the centered Mangoldt
triangle in logarithmic coordinates. -/
def hingeTransform (s : ℂ) : ℂ := multiplier s * transform s - cutoffCorrection s

/-- The arithmetic hinge has an absolutely convergent Laplace transform on
the original half-plane and retains the nonzero residue of each zeta zero
in the open critical strip, multiplied by the dyadic filter. -/
theorem hingeTransform_integral_and_zero_residues :
    let Φ := hingeTransform
    (∀ s : ℂ, 1 < s.re →
      IntegrableOn (kernel (fun t => PrimeQuarterTriangle.hinge U (Real.exp t)) s) (Ioi 0) ∧
      (∫ t in Ioi (0 : ℝ), kernel (fun u => PrimeQuarterTriangle.hinge U (Real.exp u)) s t) = Φ s) ∧
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 →
      let c := (analyticOrderNatAt riemannZeta ρ : ℂ) / (ρ * (1 - ρ))
      multiplier ρ * c ≠ 0 ∧
        Tendsto (fun s : ℂ => (s - ρ) * Φ s) (𝓝[≠] ρ) (𝓝 (multiplier ρ * c)) := by
  constructor
  · intro s hs
    have heq : logHinge = fun t => PrimeQuarterTriangle.hinge U (Real.exp t) :=
      funext logHinge_eq
    simpa only [heq, hingeTransform] using logHinge_transform hs
  · intro ρ hz hρ0 hρ1
    exact logHinge_pole hz hρ0 hρ1

#print axioms hingeTransform_integral_and_zero_residues

end D5.S3.Weil.Mertens.IntegratedExplicit.PrimeTriangleLaplace
