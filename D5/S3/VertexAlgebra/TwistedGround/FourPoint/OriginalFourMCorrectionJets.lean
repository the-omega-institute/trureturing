/- GID: D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMCorrectionJets
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMCorrectionJets
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Bivariate Taylor coefficients of the physical half-current correction. -/

import D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMInverseJets
import D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMPhysicalCovariance
import D5.S3.VertexAlgebra.HalfFock.OriginalHalfCurrentCauchy

/-! The regular half-current correction in the physical coordinate. -/

open Complex Filter
open scoped Topology

noncomputable section

namespace D5.S3.VertexAlgebra.TwistedGround.OriginalFourMInverseJets

open FourPoint.OriginalFourMActualChart
  (Chart Puncture scale scaleRoot loweringParameter chosen_roots)
open OriginalFourMOccupationTransport
open OriginalFourMPhysicalCovariance (jac slotCorrection)
open OriginalFourMSlitMean (coefficient_congr analytic_coefficient_slice)
open OriginalGaussianSewnAnalytic (coefficient)
open FourPoint.FourPointChannelCoefficients (coeff_eq_of_hasFPowerSeriesAt coeff_mul)
open HalfFock.OriginalHalfCurrentTransport (unitPower contractionScalar)
open HalfFock.OriginalHalfCurrentCauchy (regularSeries regular_series_coefficient)
open private root root_analytic root_sq inverse_coordinate from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMInverseJets
open private freeCorrection from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMPhysicalCovariance
open private b c bi ci e half liftOuter inner outer root_laws sumRootInverse sumRootInverse_mul
  outerRoot_coeffZero unitPower_constant from
  D5.S3.VertexAlgebra.HalfFock.OriginalHalfCurrentCauchy

private def slice (f : ℂ × ℂ → ℂ) (p : ℕ) (v : ℂ) : ℂ :=
  coefficient p (fun u => f (u, v))

private def doubleTaylor (f : ℂ × ℂ → ℂ) : PowerSeries (PowerSeries ℂ) :=
  PowerSeries.mk fun q => PowerSeries.mk fun p => coefficient q (slice f p)

private theorem doubleTaylor_congr {f g : ℂ × ℂ → ℂ} (h : f =ᶠ[𝓝 (0, 0)] g) :
    doubleTaylor f = doubleTaylor g := by
  obtain ⟨U, hU, V, hV, hUV⟩ := mem_nhds_prod_iff.mp h
  apply PowerSeries.ext
  intro q
  apply PowerSeries.ext
  intro p
  simp only [doubleTaylor, PowerSeries.coeff_mk]
  apply coefficient_congr
  filter_upwards [hV] with v hv
  apply coefficient_congr
  filter_upwards [hU] with u hu
  exact hUV ⟨hu, hv⟩

private theorem slice_add {f g : ℂ × ℂ → ℂ} (hf : AnalyticAt ℂ f (0, 0))
    (hg : AnalyticAt ℂ g (0, 0)) (p : ℕ) :
    slice (fun z => f z + g z) p =ᶠ[𝓝 0] fun v => slice f p v + slice g p v := by
  have hc : ContinuousAt (fun v : ℂ => ((0 : ℂ), v)) 0 := by fun_prop
  filter_upwards [hc.eventually hf.eventually_analyticAt,
    hc.eventually hg.eventually_analyticAt] with v hv hw
  have hi : AnalyticAt ℂ (fun u : ℂ => (u, v)) 0 := analyticAt_id.prod analyticAt_const
  have hfv : AnalyticAt ℂ (fun u => f (u, v)) 0 := hv.fun_comp_of_eq hi rfl
  have hgv : AnalyticAt ℂ (fun u => g (u, v)) 0 := hw.fun_comp_of_eq hi rfl
  simp only [slice, coefficient, iteratedDeriv_fun_add hfv.contDiffAt hgv.contDiffAt, add_div]

private theorem doubleTaylor_add {f g : ℂ × ℂ → ℂ} (hf : AnalyticAt ℂ f (0, 0))
    (hg : AnalyticAt ℂ g (0, 0)) :
    doubleTaylor (fun z => f z + g z) = doubleTaylor f + doubleTaylor g := by
  apply PowerSeries.ext
  intro q
  apply PowerSeries.ext
  intro p
  simp only [doubleTaylor, map_add, PowerSeries.coeff_mk, coefficient_congr (slice_add hf hg p)]
  have hfa : AnalyticAt ℂ (slice f p) 0 := analytic_coefficient_slice hf p
  have hga : AnalyticAt ℂ (slice g p) 0 := analytic_coefficient_slice hg p
  simp only [coefficient, iteratedDeriv_fun_add hfa.contDiffAt hga.contDiffAt, add_div]

private theorem doubleTaylor_mul {f g : ℂ × ℂ → ℂ} (hf : AnalyticAt ℂ f (0, 0))
    (hg : AnalyticAt ℂ g (0, 0)) :
    doubleTaylor (fun z => f z * g z) = doubleTaylor f * doubleTaylor g := by
  have hc : ContinuousAt (fun v : ℂ => ((0 : ℂ), v)) 0 := by fun_prop
  have hs (p : ℕ) : slice (fun z => f z * g z) p =ᶠ[𝓝 0]
      fun v => ∑ j ∈ Finset.range (p + 1), slice f j v * slice g (p - j) v := by
    filter_upwards [hc.eventually hf.eventually_analyticAt,
      hc.eventually hg.eventually_analyticAt] with v hv hw
    have hi : AnalyticAt ℂ (fun u : ℂ => (u, v)) 0 := analyticAt_id.prod analyticAt_const
    have hfv : AnalyticAt ℂ (fun u => f (u, v)) 0 := hv.fun_comp_of_eq hi rfl
    have hgv : AnalyticAt ℂ (fun u => g (u, v)) 0 := hw.fun_comp_of_eq hi rfl
    exact coeff_mul hfv hgv p
  have hfa (p : ℕ) : AnalyticAt ℂ (slice f p) 0 := analytic_coefficient_slice hf p
  have hga (p : ℕ) : AnalyticAt ℂ (slice g p) 0 := analytic_coefficient_slice hg p
  apply PowerSeries.ext
  intro q
  apply PowerSeries.ext
  intro p
  simp only [doubleTaylor, PowerSeries.coeff_mul, PowerSeries.coeff_mk, map_sum]
  simp only [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  rw [coefficient_congr (hs p)]
  have hsum : coefficient q
      (fun v => ∑ j ∈ Finset.range (p + 1), slice f j v * slice g (p - j) v) =
      ∑ j ∈ Finset.range (p + 1),
        coefficient q (fun v => slice f j v * slice g (p - j) v) := by
    unfold coefficient
    have hterm (j : ℕ) : AnalyticAt ℂ (fun v => slice f j v * slice g (p-j) v) 0 :=
      (hfa j).mul (hga (p-j))
    rw [iteratedDeriv_fun_sum (fun j _ => (hterm j).contDiffAt), Finset.sum_div]
  rw [hsum, Finset.sum_comm]
  congr 1
  funext j
  exact coeff_mul (hfa j) (hga (p-j)) q

private theorem coefficient_const (p : ℕ) (d : ℂ) :
    coefficient p (fun _ => d) = if p = 0 then d else 0 := by
  cases p <;> simp [coefficient, iteratedDeriv_const]

private theorem doubleTaylor_const (d : ℂ) :
    doubleTaylor (fun _ => d) = PowerSeries.C (PowerSeries.C d) := by
  apply PowerSeries.ext
  intro q
  apply PowerSeries.ext
  intro p
  simp only [doubleTaylor, PowerSeries.coeff_mk]
  change coefficient q (fun _ => coefficient p (fun _ => d)) = _
  by_cases h : q = 0 <;> simp [coefficient_const, PowerSeries.coeff_C, h]

private theorem root_coeff (a : ℂ) (p : ℕ) :
    coefficient p (root a) = PowerSeries.coeff p (unitPower a (1 / 2)) := by
  let L : ℂ →L[ℂ] ℂ := (-a) • ContinuousLinearMap.id ℂ ℂ
  have h := Complex.one_add_cpow_hasFPowerSeriesAt_zero (a := (1 / 2 : ℂ))
  rw [← map_zero L] at h
  have hs : HasFPowerSeriesAt (root a)
      (FormalMultilinearSeries.ofScalars ℂ fun k =>
        (-a) ^ k * Ring.choose (1 / 2 : ℂ) k) 0 := by
    convert h.compContinuousLinearMap (u := L) using 1
    · funext u
      simp [root, L, sub_eq_add_neg]
    · ext k
      simp [FormalMultilinearSeries.compContinuousLinearMap, L,
        binomialSeries]
  rw [show coefficient p (root a) = _ from coeff_eq_of_hasFPowerSeriesAt hs p]
  simp [unitPower, PowerSeries.coeff_rescale, PowerSeries.binomialSeries]

private theorem doubleTaylor_root_fst (a : ℂ) :
    doubleTaylor (fun z => root a z.1) = PowerSeries.C (unitPower a (1 / 2)) := by
  apply PowerSeries.ext
  intro q
  apply PowerSeries.ext
  intro p
  simp only [doubleTaylor, PowerSeries.coeff_mk]
  change coefficient q (fun _ => coefficient p (root a)) = _
  by_cases h : q = 0 <;> simp [coefficient_const, root_coeff, PowerSeries.coeff_C, h]

private theorem doubleTaylor_root_snd (a : ℂ) :
    doubleTaylor (fun z => root a z.2) = PowerSeries.map PowerSeries.C (unitPower a (1 / 2)) := by
  apply PowerSeries.ext
  intro q
  apply PowerSeries.ext
  intro p
  simp only [doubleTaylor, PowerSeries.coeff_mk]
  change coefficient q (fun v => coefficient p (fun _ => root a v)) = _
  by_cases h : p = 0 <;>
    simp [coefficient_const, root_coeff, PowerSeries.coeff_C, h]

private def correction (a : ℂ) (z : ℂ × ℂ) : ℂ :=
  a * (1 + root a z.1 * root a z.2) /
    (2 * root a z.1 * root a z.2 * (root a z.1 + root a z.2) ^ 2)

private theorem correction_coeff (a : ℂ) (p q : ℕ) :
    coefficient q (slice (correction a) p) = a ^ (p + q + 1) * contractionScalar p q := by
  let r : ℂ × ℂ → ℂ := fun z => root a z.1
  let s : ℂ × ℂ → ℂ := fun z => root a z.2
  let den : ℂ × ℂ → ℂ := fun z => 2 * r z * s z * (r z + s z) ^ 2
  let num : ℂ × ℂ → ℂ := fun z => a * (1 + r z * s z)
  have hr : AnalyticAt ℂ r (0, 0) := (root_analytic a).fun_comp_of_eq (f := Prod.fst) analyticAt_fst rfl
  have hs : AnalyticAt ℂ s (0, 0) := (root_analytic a).fun_comp_of_eq (f := Prod.snd) analyticAt_snd rfl
  have hd : AnalyticAt ℂ den (0, 0) :=
    ((analyticAt_const.mul hr).mul hs).mul ((hr.add hs).pow 2)
  have hn : AnalyticAt ℂ num (0, 0) := analyticAt_const.mul (analyticAt_const.add (hr.mul hs))
  have hd₀ : den (0, 0) ≠ 0 := by norm_num [den, r, s, root]
  have hk : AnalyticAt ℂ (correction a) (0, 0) := hn.div hd hd₀
  have he : (fun z => den z * correction a z) =ᶠ[𝓝 (0, 0)] num := by
    filter_upwards [hd.continuousAt.eventually_ne hd₀] with z hz
    change den z * (num z / den z) = num z
    field_simp
  have ht := (doubleTaylor_mul hd hk).symm.trans (doubleTaylor_congr he)
  let M := PowerSeries.map (HahnSeries.ofPowerSeries ℤ ℂ)
  have hr' : M (doubleTaylor r) = b a := by
    change M (doubleTaylor (fun z => root a z.1)) = _
    simp [doubleTaylor_root_fst, M, b, outer, liftOuter]
  have hs' : M (doubleTaylor s) = c a := by
    change M (doubleTaylor (fun z => root a z.2)) = _
    rw [doubleTaylor_root_snd, ← RingHom.comp_apply, ← PowerSeries.map_comp]
    have hC : (HahnSeries.ofPowerSeries ℤ ℂ).comp PowerSeries.C = HahnSeries.C := by
      ext d : 1
      exact HahnSeries.ofPowerSeries_C d
    rw [hC]
    rfl
  have hconst (d : ℂ) : M (doubleTaylor (fun _ => d)) =
      PowerSeries.C (HahnSeries.C d) := by
    simp [doubleTaylor_const, M, HahnSeries.ofPowerSeries_C]
  have hsum : doubleTaylor (fun z => r z + s z) = doubleTaylor r + doubleTaylor s :=
    doubleTaylor_add hr hs
  have hprod : doubleTaylor (fun z => r z * s z) = doubleTaylor r * doubleTaylor s :=
    doubleTaylor_mul hr hs
  have htwo : AnalyticAt ℂ (fun z => 2 * r z) (0, 0) := analyticAt_const.mul hr
  have hthree : AnalyticAt ℂ (fun z => 2 * r z * s z) (0, 0) := htwo.mul hs
  have hsq : AnalyticAt ℂ (fun z => r z + s z) (0, 0) := hr.add hs
  have hd' : M (doubleTaylor den) = 2 * b a * c a * (b a + c a) ^ 2 := by
    change M (doubleTaylor (fun z => (2 * r z * s z) * (r z + s z) ^ 2)) = _
    simp only [pow_two]
    have hsq2 : AnalyticAt ℂ (fun z => (r z + s z) * (r z + s z)) (0, 0) := hsq.mul hsq
    rw [doubleTaylor_mul hthree hsq2,
      doubleTaylor_mul htwo hs, doubleTaylor_mul (f := fun _ => 2) analyticAt_const hr,
      doubleTaylor_mul hsq hsq, hsum]
    simp only [map_mul, map_add, hconst, hr', hs', map_ofNat]
  have hn' : M (doubleTaylor num) = e a * (1 + b a * c a) := by
    have hplus : AnalyticAt ℂ (fun z => 1 + r z * s z) (0, 0) :=
      analyticAt_const.add (hr.mul hs)
    change M (doubleTaylor (fun z => a * (1 + r z * s z))) = _
    rw [doubleTaylor_mul (f := fun _ => a) analyticAt_const hplus,
      doubleTaylor_add (f := fun _ => 1) (g := fun z => r z * s z) analyticAt_const
        (hr.mul hs), hprod]
    simp only [map_mul, map_add, hconst, hr', hs', e, map_one]
  have hclear : (2 * b a * c a * (b a + c a) ^ 2) * regularSeries a =
      e a * (1 + b a * c a) := by
    obtain ⟨_, _, hb, hc⟩ := root_laws a
    have hh : (2 : PowerSeries (LaurentSeries ℂ)) * PowerSeries.C half = 1 := by
      have h2 : (2 : LaurentSeries ℂ) ≠ 0 := by
        intro hz
        have hc := congrArg (fun f : LaurentSeries ℂ => f.coeff 0) hz
        change (HahnSeries.single (0 : ℤ) (2 : ℂ)).coeff 0 = (0 : LaurentSeries ℂ).coeff 0 at hc
        simp at hc
      rw [← map_ofNat PowerSeries.C, ← map_mul, half, mul_inv_cancel₀ h2, map_one]
    have hsum := sumRootInverse_mul a
    unfold regularSeries
    calc
      _ = (2 * PowerSeries.C half) * (b a * bi a) * (c a * ci a) *
          ((b a + c a) * sumRootInverse a) ^ 2 * (e a * (1 + b a * c a)) := by ring
      _ = _ := by rw [hh, hb, hc, hsum]; simp
  have hne : M (doubleTaylor den) ≠ 0 := by
    have h0 : (PowerSeries.coeff 0 (M (doubleTaylor den))).coeff ((0 : ℕ) : ℤ) = 8 := by
      rw [show M = PowerSeries.map (HahnSeries.ofPowerSeries ℤ ℂ) from rfl,
        PowerSeries.coeff_map]
      change ((PowerSeries.coeff 0 (doubleTaylor den) : PowerSeries ℂ) :
        LaurentSeries ℂ).coeff ((0 : ℕ) : ℤ) = _
      rw [LaurentSeries.coeff_coe_powerSeries]
      norm_num [doubleTaylor, slice, coefficient, den, r, s, root]
    intro hz
    rw [hz, map_zero, HahnSeries.coeff_zero] at h0
    norm_num at h0
  have hfinal : M (doubleTaylor (correction a)) = regularSeries a := by
    apply mul_left_cancel₀ hne
    rw [← map_mul, ht, hd', hn', hclear]
  have h := congrArg (fun S : PowerSeries (LaurentSeries ℂ) =>
    (PowerSeries.coeff q S).coeff (p : ℤ)) hfinal
  simpa [M, doubleTaylor, LaurentSeries.coeff_coe_powerSeries, regular_series_coefficient] using h

/-- The correction subtracted in the physical covariance has the same-puncture
contraction coefficients of the inverse lowering map. -/
theorem coefficient_neg_slotCorrection_div_jac
    {x : ℝ} (hx : 0 < x) (hx1 : x < 1) (c : Chart) (i : Puncture) (p q : ℕ) :
    coefficient q (fun v => coefficient p (fun u =>
        -(slotCorrection c x i i u v / (jac c x i u * jac c x i v)))) =
      (-loweringParameter c i / scale c x i) ^ (p + q + 1) * contractionScalar p q := by
  let a := -loweringParameter c i / scale c x i
  let r := root a
  have hρ := (chosen_roots hx hx1 c i).1
  have hρ₀ := root_ne hx hx1 c i
  have he : (fun z : ℂ × ℂ =>
      -(slotCorrection c x i i z.1 z.2 / (jac c x i z.1 * jac c x i z.2))) =ᶠ[𝓝 (0, 0)]
      correction a := by
    have hc : ContinuousAt (fun z : ℂ × ℂ => r z.1 + r z.2) (0, 0) :=
      ((root_analytic a).fun_comp_of_eq (f := Prod.fst) analyticAt_fst rfl).continuousAt.add
        ((root_analytic a).fun_comp_of_eq (f := Prod.snd) analyticAt_snd rfl).continuousAt
    filter_upwards [(inverse_coordinate hx hx1 c i).prod_nhds (inverse_coordinate hx hx1 c i),
      hc.eventually_ne (y := (0 : ℂ)) (by norm_num [r, root])] with z ⟨hu, hv⟩ hsum
    have hru : r z.1 ^ 2 = 1 - a * z.1 := root_sq a z.1
    have hrv : r z.2 ^ 2 = 1 - a * z.2 := root_sq a z.2
    have hu₀ : r z.1 ≠ 0 := fun h => hu.2.2 (by rw [← hru, h]; norm_num)
    have hv₀ : r z.2 ≠ 0 := fun h => hv.2.2 (by rw [← hrv, h]; norm_num)
    simp only [slotCorrection, true_and, ite_true, freeCorrection, jac, halfJacobian,
      hu.2.1, hv.2.1, correction]
    change -(loweringParameter c i * (1 + (r z.1)⁻¹ * (r z.2)⁻¹) /
      (2 * (r z.1)⁻¹ * (r z.2)⁻¹ * ((r z.1)⁻¹ + (r z.2)⁻¹) ^ 2) / _) = _
    have hs : (r z.1)⁻¹ + (r z.2)⁻¹ ≠ 0 := by
      intro hh
      have hm : (r z.1)⁻¹ + (r z.2)⁻¹ = (r z.1 + r z.2) / (r z.1 * r z.2) := by
        field_simp
        ring
      exact hsum ((div_eq_zero_iff.mp (hm ▸ hh)).resolve_right (mul_ne_zero hu₀ hv₀))
    change -(loweringParameter c i * (1 + (r z.1)⁻¹ * (r z.2)⁻¹) /
        (2 * (r z.1)⁻¹ * (r z.2)⁻¹ * ((r z.1)⁻¹ + (r z.2)⁻¹) ^ 2) /
        ((scaleRoot c x i / (r z.1)⁻¹ ^ 3) * (scaleRoot c x i / (r z.2)⁻¹ ^ 3))) =
      (-loweringParameter c i / scale c x i) * (1 + r z.1 * r z.2) /
        (2 * r z.1 * r z.2 * (r z.1 + r z.2) ^ 2)
    rw [← hρ]
    have hsumInv : (r z.1)⁻¹ + (r z.2)⁻¹ = (r z.1 + r z.2) / (r z.1 * r z.2) := by
      field_simp
      ring
    rw [hsumInv]
    field_simp [hu₀, hv₀, hρ₀, hsum]
    ring
  have h := congrArg (fun S : PowerSeries (PowerSeries ℂ) =>
    PowerSeries.coeff p (PowerSeries.coeff q S)) (doubleTaylor_congr he)
  change coefficient q (slice (fun z =>
    -(slotCorrection c x i i z.1 z.2 / (jac c x i z.1 * jac c x i z.2))) p) = _
  exact (by simpa only [doubleTaylor, PowerSeries.coeff_mk] using h :
    _ = coefficient q (slice (correction a) p)).trans (correction_coeff a p q)

end D5.S3.VertexAlgebra.TwistedGround.OriginalFourMInverseJets
