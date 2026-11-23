/- GID: D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMInverseJets
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMInverseJets
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Taylor coefficients of inverse half-current chart transport. -/

import D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMSlitTaylor
import D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMOccupationTransport
import D5.S3.VertexAlgebra.TwistedGround.FourPoint.FourPointChannelCoefficients

/-! Taylor coefficients in the physical half-current coordinate. -/

open Complex Filter
open scoped Topology

noncomputable section

namespace D5.S3.VertexAlgebra.TwistedGround.OriginalFourMInverseJets

open FourPoint.OriginalFourMActualChart
  (Chart Puncture scale scaleRoot loweringParameter)
open OriginalFourMOccupationTransport
open OriginalGaussianSewnAnalytic (coefficient)
open FourPoint.FourPointChannelCoefficients (coeff coeff_mul)
open OriginalFourMSlitMean (coefficient_congr)

open private scale_ne from D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMActualChart

private def root (a u : ℂ) : ℂ := (1 - a * u) ^ (1 / 2 : ℂ)

private theorem root_analytic (a : ℂ) : AnalyticAt ℂ (root a) 0 :=
  (analyticAt_const.sub (analyticAt_const.mul analyticAt_id)).cpow analyticAt_const
    (by simp)

private theorem root_sq (a u : ℂ) : root a u ^ 2 = 1 - a * u := by
  unfold root
  rw [← Complex.cpow_mul_nat]
  norm_num

private theorem inverse_coordinate {x : ℝ} (hx : 0 < x) (hx1 : x < 1)
    (c : Chart) (i : Puncture) :
    ∀ᶠ u : ℂ in 𝓝 0,
      rawLocal c x i u =
        u / scale c x i / (1 - (-loweringParameter c i / scale c x i) * u) ∧
      inverseRoot c x i u = (root (-loweringParameter c i / scale c x i) u)⁻¹ ∧
      1 - (-loweringParameter c i / scale c x i) * u ≠ 0 := by
  let lam := scale c x i
  let η := loweringParameter c i
  let a := -η / lam
  have hlam : lam ≠ 0 := scale_ne hx hx1 c i
  have hd : ContinuousAt (fun u : ℂ => 1 - a * u) 0 :=
    continuousAt_const.sub (continuousAt_const.mul continuousAt_id)
  have hs : ContinuousAt (fun u => inverseRoot c x i u + (root a u)⁻¹) 0 :=
    (inverseRoot_analytic hx hx1 c i).continuousAt.add
      ((root_analytic a).continuousAt.inv₀ (by simp [root]))
  filter_upwards [hd.eventually_ne (y := (0 : ℂ)) (by simp),
    hs.eventually_ne (y := (0 : ℂ)) (by norm_num [inverseRoot_zero, root])] with u hu hsum
  have hden : lam + η * u = lam * (1 - a * u) := by
    dsimp [a]
    field_simp
    simp
  have hv : rawLocal c x i u = u / lam / (1 - a * u) := by
    change u / (lam + η * u) = _
    rw [hden, div_div]
  have he : inverseRoot c x i u ^ 2 = ((root a u)⁻¹) ^ 2 := by
    rw [inverseRoot_sq, hv, inv_pow, root_sq]
    change 1 - η * (u / lam / (1 - a * u)) = (1 - a * u)⁻¹
    have hscale : η * (u / lam) = -(a * u) := by dsimp [a]; ring
    rw [← mul_div_assoc, hscale]
    field_simp [hu]
    ring
  exact ⟨hv, sub_eq_zero.mp ((mul_eq_zero.mp
    (show (inverseRoot c x i u + (root a u)⁻¹) *
        (inverseRoot c x i u - (root a u)⁻¹) = 0 by rw [← sq_sub_sq, he, sub_self]
    )).resolve_left hsum), hu⟩

private theorem monomial_coeff (n j : ℕ) :
    coeff (fun u : ℂ => u ^ n) j = if j = n then 1 else 0 := by
  unfold coeff
  rw [iteratedDeriv_fun_pow_zero]
  split_ifs with hj
  · subst j
    exact div_self (show (n.factorial : ℂ) ≠ 0 by exact_mod_cast Nat.factorial_ne_zero n)
  · simp

private theorem inverse_binomial_series (a b : ℂ) :
    HasFPowerSeriesAt (fun u : ℂ => 1 / (1 - a * u) ^ b)
      (.ofScalars ℂ fun k => Ring.choose (b + k - 1) k * a ^ k) 0 := by
  let L : ℂ →L[ℂ] ℂ := a • ContinuousLinearMap.id ℂ ℂ
  have h := (Complex.one_div_one_sub_cpow_hasFPowerSeriesOnBall_zero b).hasFPowerSeriesAt
  rw [← map_zero L] at h
  convert h.compContinuousLinearMap (u := L) using 1
  · rfl
  · ext k
    simp [FormalMultilinearSeries.compContinuousLinearMap, L, mul_comm]

/-- An inverse chart transports a native monomial to physical mode `m` with the
half-current binomial and the chosen lifted scale. -/
theorem coefficient_rawLocal_pow_div_halfJacobian
    {x : ℝ} (hx : 0 < x) (hx1 : x < 1) (c : Chart) (i : Puncture) (m n : ℕ) :
    coefficient m (fun u => rawLocal c x i u ^ n /
      halfJacobian c x i (inverseRoot c x i u)) =
    if n ≤ m then
      (scaleRoot c x i)⁻¹ * ((scale c x i)⁻¹) ^ m *
        (-loweringParameter c i) ^ (m - n) * Ring.choose ((m : ℂ) + 1 / 2) (m - n)
    else 0 := by
  let lam := scale c x i
  let ρ := scaleRoot c x i
  let η := loweringParameter c i
  let a := -η / lam
  let b : ℂ := n + 3 / 2
  let f : ℂ → ℂ := fun u => 1 / (1 - a * u) ^ b
  let s : ℂ := ρ⁻¹ * lam⁻¹ ^ n
  have hf := inverse_binomial_series a b
  have hg : (fun u => rawLocal c x i u ^ n / halfJacobian c x i (inverseRoot c x i u))
      =ᶠ[𝓝 0] (fun u => u ^ n * (s * f u)) := by
    filter_upwards [inverse_coordinate hx hx1 c i] with u ⟨hv, hr, hd⟩
    let d := 1 - a * u
    have hd' : d ^ b = d ^ n * root a u ^ 3 := by
      have hb : (n : ℂ) + (1 / 2 : ℂ) * (3 : ℕ) = b := by dsimp [b]; ring
      change d ^ b = d ^ n * (d ^ (1 / 2 : ℂ)) ^ 3
      rw [← Complex.cpow_mul_nat, ← Complex.cpow_natCast d n,
        ← Complex.cpow_add _ _ hd, hb]
    rw [hv, halfJacobian, hr]
    change (u / lam / d) ^ n / (ρ / (root a u)⁻¹ ^ 3) = u ^ n * (s * (1 / d ^ b))
    rw [hd']
    dsimp only [s]
    simp only [div_eq_mul_inv, inv_pow, mul_inv, inv_inv, one_mul]
    ring
  rw [coefficient_congr hg]
  change coeff (fun u => u ^ n * (s * f u)) m = _
  have hs (k : ℕ) : coeff (fun u => s * f u) k =
      s * (Ring.choose (b + k - 1) k * a ^ k) := by
    unfold coeff
    rw [iteratedDeriv_const_mul s hf.analyticAt.contDiffAt]
    rw [mul_div_assoc]
    congr 1
    exact FourPoint.FourPointChannelCoefficients.coeff_eq_of_hasFPowerSeriesAt hf k
  have hn : AnalyticAt ℂ (fun u : ℂ => u ^ n) 0 := analyticAt_id.pow n
  have hsA : AnalyticAt ℂ (fun u => s * f u) 0 := analyticAt_const.mul hf.analyticAt
  rw [coeff_mul hn hsA]
  simp only [monomial_coeff]
  by_cases h : n ≤ m
  · rw [ite_eq_left h, Finset.sum_eq_single_of_mem n (Finset.mem_range.mpr (Nat.lt_succ_of_le h))]
    · rw [hs]
      simp only [ite_true, one_mul]
      have hb : b + ((m - n : ℕ) : ℂ) - 1 = (m : ℂ) + 1 / 2 := by
        rw [Nat.cast_sub h]
        dsimp [b]
        ring
      have ha : a ^ (m - n) = (-η) ^ (m - n) * lam⁻¹ ^ (m - n) := by
        dsimp only [a]
        rw [div_eq_mul_inv, mul_pow]
      have hp : lam⁻¹ ^ n * lam⁻¹ ^ (m - n) = lam⁻¹ ^ m := by
        rw [← pow_add, Nat.add_sub_of_le h]
      rw [hb, ha]
      change _ = ρ⁻¹ * lam⁻¹ ^ m * (-η) ^ (m - n) * Ring.choose _ _
      rw [← hp]
      dsimp only [s]
      ring
    · intro j _ hj
      simp [hj]
  · rw [ite_eq_right h]
    apply Finset.sum_eq_zero
    intro j hj
    have hjn : j ≠ n := fun he => h (Nat.lt_succ_iff.mp (he ▸ Finset.mem_range.mp hj))
    simp [hjn]

/-- A physical mark of mode `m` depends only on native Taylor modes through `m`. -/
theorem coefficient_comp_rawLocal_div_halfJacobian
    {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) {x : ℝ} (hx : 0 < x) (hx1 : x < 1)
    (c : Chart) (i : Puncture) (m : ℕ) :
    coefficient m (fun u => f (rawLocal c x i u) /
      halfJacobian c x i (inverseRoot c x i u)) =
      ∑ n ∈ Finset.range (m + 1),
        coefficient n f * ((scaleRoot c x i)⁻¹ * ((scale c x i)⁻¹) ^ m *
          (-loweringParameter c i) ^ (m - n) * Ring.choose ((m : ℂ) + 1 / 2) (m - n)) := by
  obtain ⟨R, hR, hTaylor⟩ := hf.exists_eventuallyEq_sum_add_pow_mul (m + 1)
  let v := rawLocal c x i
  let J := fun u => halfJacobian c x i (inverseRoot c x i u)
  let g : ℂ → ℂ := fun u => (scale c x i + loweringParameter c i * u)⁻¹
  have hv : AnalyticAt ℂ v 0 := rawLocal_analytic hx hx1 c i
  have hv₀ : v 0 = 0 := by simp [v, rawLocal]
  have hg : AnalyticAt ℂ g 0 :=
    (analyticAt_const.add (analyticAt_const.mul analyticAt_id)).inv
      (by simpa using scale_ne hx hx1 c i)
  have hJ : AnalyticAt ℂ J 0 :=
    analyticAt_const.div ((inverseRoot_analytic hx hx1 c i).pow 3) (by simp [inverseRoot_zero])
  have hJ₀ : J 0 ≠ 0 := by simpa [J, halfJacobian, inverseRoot_zero] using root_ne hx hx1 c i
  have hrest : AnalyticAt ℂ (fun u => g u ^ (m + 1) * R (v u) / J u) 0 :=
    ((hg.pow _).mul (hR.fun_comp_of_eq hv hv₀)).div hJ hJ₀
  have hech : (fun u => f (v u) / J u) =ᶠ[𝓝 0] fun u =>
      (∑ n ∈ Finset.range (m + 1), coefficient n f * (v u ^ n / J u)) +
        u ^ (m + 1) * (g u ^ (m + 1) * R (v u) / J u) := by
    have hvmap : Tendsto v (𝓝 0) (𝓝 0) := by
      have hc : Tendsto v (𝓝 0) (𝓝 (v 0)) := hv.continuousAt
      rwa [hv₀] at hc
    filter_upwards [hvmap.eventually hTaylor] with u hu
    simp only [hu, add_div, Finset.sum_div, coefficient, smul_eq_mul]
    congr 1
    · apply Finset.sum_congr rfl
      intro n _
      ring
    · have hvg : v u = u * g u := rfl
      rw [show v u ^ (m + 1) = u ^ (m + 1) * g u ^ (m + 1) by rw [hvg, mul_pow]]
      ring
  rw [coefficient_congr hech]
  have hterm (n : ℕ) : AnalyticAt ℂ (fun u => coefficient n f * (v u ^ n / J u)) 0 :=
    analyticAt_const.mul ((hv.pow n).div hJ hJ₀)
  have hsum : AnalyticAt ℂ
      (fun u => ∑ n ∈ Finset.range (m + 1), coefficient n f * (v u ^ n / J u)) 0 :=
    Finset.analyticAt_fun_sum _ fun n _ => hterm n
  have hpow : AnalyticAt ℂ (fun u : ℂ => u ^ (m + 1)) 0 := analyticAt_id.pow _
  have hz : coefficient m (fun u => u ^ (m + 1) * (g u ^ (m + 1) * R (v u) / J u)) = 0 := by
    change coeff _ m = _
    rw [coeff_mul hpow hrest]
    apply Finset.sum_eq_zero
    intro j hj
    simp [monomial_coeff, show j ≠ m + 1 by have := Finset.mem_range.mp hj; omega]
  have hadd : coefficient m (fun u =>
        (∑ n ∈ Finset.range (m + 1), coefficient n f * (v u ^ n / J u)) +
          u ^ (m + 1) * (g u ^ (m + 1) * R (v u) / J u)) =
      ∑ n ∈ Finset.range (m + 1), coefficient n f * coefficient m (fun u => v u ^ n / J u) := by
    have htotal : AnalyticAt ℂ
        (fun u => u ^ (m + 1) * (g u ^ (m + 1) * R (v u) / J u)) 0 :=
      hpow.mul hrest
    simp only [coefficient] at hsum hterm hz ⊢
    rw [iteratedDeriv_fun_add hsum.contDiffAt htotal.contDiffAt, add_div, hz, add_zero,
      iteratedDeriv_fun_sum (fun n _ => (hterm n).contDiffAt), Finset.sum_div]
    simp only [iteratedDeriv_const_mul_field, mul_div_assoc]
  rw [hadd]
  apply Finset.sum_congr rfl
  intro n hn
  rw [show coefficient m (fun u => v u ^ n / J u) =
        _ from coefficient_rawLocal_pow_div_halfJacobian hx hx1 c i m n,
    ite_eq_left (Nat.lt_succ_iff.mp (Finset.mem_range.mp hn))]

end D5.S3.VertexAlgebra.TwistedGround.OriginalFourMInverseJets
