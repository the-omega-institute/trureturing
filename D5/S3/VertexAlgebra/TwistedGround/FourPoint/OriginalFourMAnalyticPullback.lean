/- GID: D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMAnalyticPullback
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMAnalyticPullback
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Ordinary analytic half-current coefficients in the original local coordinates. -/

import D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMOccupationTransport
import D5.S3.VertexAlgebra.TwistedGround.OriginalFourMChargeNormal
import Mathlib.Analysis.Analytic.Binomial

/-! Finite Taylor selection through the Möbius half-current coordinate. -/

set_option autoImplicit false

noncomputable section
open Complex Filter Asymptotics
open scoped BigOperators Topology

namespace D5.S3.VertexAlgebra.TwistedGround.OriginalFourMAnalyticPullback
open OriginalGaussianSewnAnalytic (coefficient)
open private analyticAt_local_cpow from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMSignedOverlap
open private coefficient_pow_shift from
  D5.S3.VertexAlgebra.TwistedGround.OriginalFourMChargeNormal
open private binomial_reflection from
  D5.S3.VertexAlgebra.HalfFock.OriginalHalfCurrentTransport

private theorem analytic_taylor_remainder {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (n : ℕ) :
    (fun z => f z - ∑ k ∈ Finset.range n, coefficient k f * z ^ k)
      =O[𝓝 (0 : ℂ)] (fun z => ‖z‖ ^ n) := by
  have h := hf.hasFPowerSeriesAt.isBigO_sub_partialSum_pow n
  simpa only [zero_add, FormalMultilinearSeries.partialSum,
    FormalMultilinearSeries.apply_eq_prod_smul_coeff, FormalMultilinearSeries.coeff_ofScalars,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_comm, coefficient] using h

private theorem coefficient_vanish_of_order {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) {N : ℕ}
    (h : f =O[𝓝 (0 : ℂ)] (fun z => ‖z‖ ^ N)) (n : ℕ) (hn : n < N) :
    coefficient n f = 0 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have hg : (fun z : ℂ => ‖z‖ ^ N) =O[𝓝 (0 : ℂ)] (fun z => ‖z‖ ^ (n+1)) := by
      apply IsBigO.of_bound 1
      filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds
          (by simp : ‖(0 : ℂ)‖ < (1 : ℝ))] with z hz
      simpa only [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (norm_nonneg _) _), one_mul] using
        pow_le_pow_of_le_one (norm_nonneg z) hz.le (Nat.succ_le_of_lt hn)
    have hsmall := h.trans hg
    have hrem := analytic_taylor_remainder hf (n+1)
    have hs (z : ℂ) : (∑ k ∈ Finset.range (n+1), coefficient k f * z^k) =
        coefficient n f * z^n := by
      apply Finset.sum_eq_single_of_mem n (by simp)
      intro k hk hkne
      have hkn : k < n := by
        have := Finset.mem_range.mp hk
        omega
      rw [ih k hkn (hkn.trans hn), zero_mul]
    simp only [hs] at hrem
    have hterm : (fun z : ℂ => coefficient n f * z^n) =O[𝓝 (0 : ℂ)] (fun z => ‖z‖ ^ (n+1)) := by
      convert hsmall.sub hrem using 1
      ext z
      ring
    let P := (FormalMultilinearSeries.ofScalars ℂ (fun _ => coefficient n f)) n
    have hP : (fun z : ℂ => P (fun _ => z)) =O[𝓝 (0 : ℂ)] (fun z => ‖z‖ ^ (n+1)) := by
      simpa only [P, FormalMultilinearSeries.apply_eq_prod_smul_coeff,
        FormalMultilinearSeries.coeff_ofScalars, Finset.prod_const, Finset.card_univ,
        Fintype.card_fin, smul_eq_mul, mul_comm] using hterm
    simpa [P, FormalMultilinearSeries.ofScalars] using hP.continuousMultilinearMap_apply_eq_zero 1

private theorem coefficient_sub {f g : ℂ → ℂ} (hf : AnalyticAt ℂ f 0)
    (hg : AnalyticAt ℂ g 0) (n : ℕ) :
    coefficient n (fun z => f z - g z) = coefficient n f - coefficient n g := by
  simp only [coefficient, iteratedDeriv_fun_sub hf.contDiffAt hg.contDiffAt, sub_div]

private theorem cpow_affine_coefficient (eta a : ℂ) (n : ℕ) :
    coefficient n (fun z => (1 - eta*z) ^ a) = (-eta)^n * Ring.choose a n := by
  let L : ℂ →L[ℂ] ℂ := (-eta) • ContinuousLinearMap.id ℂ ℂ
  let F := fun z : ℂ => (1+z)^a
  let P := FormalMultilinearSeries.ofScalars ℂ fun n => Ring.choose a n
  have hf : HasFPowerSeriesAt F P (L 0) := by
    simpa [map_zero, F, P, binomialSeries] using
      Complex.one_add_cpow_hasFPowerSeriesAt_zero (a := a)
  have hg := hf.compContinuousLinearMap (u := L)
  have hf' : HasFPowerSeriesAt (fun z => (1-eta*z)^a) (P.compContinuousLinearMap L) 0 := by
    convert hg using 1
    ext z
    simp [F, L, sub_eq_add_neg]
  have he := hf'.analyticAt.hasFPowerSeriesAt.eq_formalMultilinearSeries hf'
  have hc := congrArg (fun p : FormalMultilinearSeries ℂ ℂ ℂ => p.coeff n) he
  have hOne : (List.ofFn (1 : Fin n → ℂ)).prod = 1 := by rw [List.prod_ofFn]; simp
  simpa [coefficient, P, L, FormalMultilinearSeries.coeff,
    FormalMultilinearSeries.compContinuousLinearMap, FormalMultilinearSeries.ofScalars,
    hOne, mul_comm] using hc

/-- The ordinary half-current pullback coefficient uses the first n+1
Taylor entries of the native source germ. -/
theorem analytic_half_pullback_coefficient (root lambda eta : ℂ) {F : ℂ → ℂ}
    (hF : AnalyticAt ℂ F 0) (n : ℕ) :
    coefficient n (fun z => root * (1-eta*z)^(-3/2:ℂ) * F (lambda*z/(1-eta*z))) =
      ∑ p ∈ Finset.range (n+1), coefficient p F *
        (root * lambda^p * eta^(n-p) * Ring.choose ((n:ℂ)+1/2) (n-p)) := by
  let B := fun z : ℂ => 1-eta*z
  let g := fun z : ℂ => lambda*z / B z
  let H := fun z : ℂ => root * (B z)^(-3/2:ℂ)
  let f := fun z : ℂ => H z * F (g z)
  let R := fun z : ℂ => ∑ p ∈ Finset.range (n+1),
    coefficient p F * (root * lambda^p) * (z^p * (B z)^(-(p:ℂ)-3/2))
  have hB : AnalyticAt ℂ B 0 := analyticAt_const.sub (analyticAt_const.mul analyticAt_id)
  have hB₀ : B 0 = 1 := by simp [B]
  have hpow (a : ℂ) : AnalyticAt ℂ (fun z => (B z)^a) 0 :=
    analyticAt_local_cpow hB (by simp [hB₀])
  have hg : AnalyticAt ℂ g 0 :=
    (analyticAt_const.mul analyticAt_id).div hB (by simp [hB₀])
  have hg₀ : g 0 = 0 := by simp [g]
  have hH : AnalyticAt ℂ H 0 := analyticAt_const.mul (hpow _)
  have hf : AnalyticAt ℂ f 0 := hH.mul (hF.comp_of_eq hg hg₀)
  have hterm (p : ℕ) : AnalyticAt ℂ
      (fun z => coefficient p F * (root * lambda^p) * (z^p * (B z)^(-(p:ℂ)-3/2))) 0 :=
    analyticAt_const.mul ((analyticAt_id.pow p).mul (hpow _))
  have hR : AnalyticAt ℂ R 0 := (Finset.range (n+1)).analyticAt_fun_sum (fun p _ => hterm p)
  have hgt : Tendsto g (𝓝 0) (𝓝 0) := by simpa only [hg₀] using hg.continuousAt.tendsto
  have hlinear : g =O[𝓝 (0 : ℂ)] (fun z => z) := by
    have hcont : Tendsto (fun z => lambda / B z) (𝓝 0) (𝓝 (lambda / B 0)) :=
      (continuousAt_const.div hB.continuousAt (by simp [hB₀])).tendsto
    convert (hcont.isBigO_one ℂ).mul (isBigO_refl (fun z : ℂ => z) (𝓝 0)) using 1 <;>
      ext z <;> simp [g, div_eq_mul_inv, mul_assoc, mul_comm z]
  have hrem : (fun z => F (g z) - ∑ k ∈ Finset.range (n+1), coefficient k F * (g z)^k)
      =O[𝓝 (0 : ℂ)] (fun z => ‖g z‖^(n+1)) := by
    exact (analytic_taylor_remainder hF (n+1)).comp_tendsto hgt
  have hpowO : (fun z : ℂ => ‖g z‖^(n+1)) =O[𝓝 (0 : ℂ)] (fun z => ‖z‖^(n+1)) := by
    simpa only [Pi.pow_apply] using (hlinear.norm_left.norm_right).pow (n+1)
  have hcauchy : (fun z => f z - R z) =O[𝓝 (0 : ℂ)] (fun z => ‖z‖^(n+1)) := by
    have hb := hH.continuousAt.tendsto.isBigO_one ℝ
    have hr : (fun z => F (g z) - ∑ k ∈ Finset.range (n+1), coefficient k F * (g z)^k)
        =O[𝓝 (0 : ℂ)] (fun z => ‖z‖^(n+1)) := hrem.trans hpowO
    have hh := hb.mul hr
    apply hh.congr'
    · filter_upwards [hB.continuousAt.eventually_ne (y := (0 : ℂ)) (by simp [hB₀])] with z hz
      change H z * (F (g z) - ∑ p ∈ Finset.range (n+1), coefficient p F * g z ^ p) =
        f z - R z
      change _ = H z * F (g z) - _
      rw [mul_sub, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro p _
      simp only [H, g, mul_pow, div_eq_mul_inv]
      rw [inv_pow, ← Complex.cpow_natCast (B z) p, ← Complex.cpow_neg]
      rw [show -(p:ℂ)-3*(2:ℂ)⁻¹ = (-3*(2:ℂ)⁻¹) + -(p:ℂ) by ring,
        Complex.cpow_add _ _ hz]
      ring
    · exact Eventually.of_forall fun _ => by simp
  have hcoef := coefficient_vanish_of_order (hf.sub hR) hcauchy n (Nat.lt_succ_self _)
  change coefficient n (fun z => f z - R z) = 0 at hcoef
  rw [coefficient_sub hf hR, sub_eq_zero] at hcoef
  change coefficient n f = _
  rw [hcoef]
  change iteratedDeriv n R 0 / (n.factorial : ℂ) = _
  dsimp only [R]
  rw [iteratedDeriv_fun_sum (fun p _ => (hterm p).contDiffAt), Finset.sum_div]
  apply Finset.sum_congr rfl
  intro p hp
  rw [iteratedDeriv_const_mul_field, mul_div_assoc]
  change coefficient p F * (root * lambda^p) *
    coefficient n (fun z => z^p * (B z)^(-(p:ℂ)-3/2)) = _
  have hp' : p ≤ n := by simpa using hp
  rw [coefficient_pow_shift (hpow _) p n, ite_eq_left hp']
  change _ * coefficient (n-p) (fun z => (1-eta*z)^(-(p:ℂ)-3/2)) = _
  rw [cpow_affine_coefficient]
  rw [show -eta = eta * (-1) by ring, mul_pow]
  have hx : (-( -(p:ℂ)-3/2) + ((n-p:ℕ):ℂ)-1) = (n:ℂ)+1/2 := by
    rw [Nat.cast_sub hp']
    ring
  rw [show eta^(n-p) * (-1:ℂ)^(n-p) * Ring.choose (-(p:ℂ)-3/2) (n-p) =
      eta^(n-p) * ((-1:ℂ)^(n-p) * Ring.choose (-(p:ℂ)-3/2) (n-p)) by ring,
    binomial_reflection, hx]
  ring

open OriginalFourMActualChart (Chart Puncture scale scaleRoot loweringParameter)
open OriginalFourMOccupationTransport (inverseRoot)
open private rawLocal halfJacobian from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMChartProduct
open private scale_ne from D5.S3.VertexAlgebra.TwistedGround.OriginalFourMActualChart

/-- The original inverse local map acts on the n-th Taylor coefficient
by the inverse scale at the full incoming weight and the negative
lowering parameter at each finite binomial step. -/
theorem inverse_physical_source_coefficient {x : ℝ} (hx : 0 < x) (hx1 : x < 1)
    (c : Chart) (i : Puncture) {F : ℂ → ℂ} (hF : AnalyticAt ℂ F 0) (n : ℕ) :
    coefficient n (fun u => (halfJacobian c x i (inverseRoot c x i u))⁻¹ *
      F (rawLocal c x i u)) =
      (scaleRoot c x i)⁻¹ ^ (2*n+1) *
        ∑ p ∈ Finset.range (n+1), coefficient p F *
          ((-loweringParameter c i)^(n-p) * Ring.choose ((n:ℂ)+1/2) (n-p)) := by
  let lambda := scale c (x : ℂ) i
  let eta := loweringParameter c i
  let root := scaleRoot c x i
  let e := -eta * lambda⁻¹
  let B := fun u : ℂ => 1-e*u
  have hl : lambda ≠ 0 := scale_ne hx hx1 c i
  have hroot : root^2 = lambda := (OriginalFourMActualChart.chosen_roots hx hx1 c i).1
  have hB : ContinuousAt B 0 := continuousAt_const.sub (continuousAt_const.mul continuousAt_id)
  have hB₀ : B 0 ∈ Complex.slitPlane := by simp [B]
  have hnear : ∀ᶠ u : ℂ in 𝓝 0, B u ∈ Complex.slitPlane :=
    hB.eventually (Complex.isOpen_slitPlane.mem_nhds hB₀)
  have he : (fun u => (halfJacobian c x i (inverseRoot c x i u))⁻¹ *
      F (rawLocal c x i u)) =ᶠ[𝓝 (0 : ℂ)]
      (fun u => root⁻¹ * (B u)^(-3/2:ℂ) * F (lambda⁻¹*u/B u)) := by
    filter_upwards [hnear] with u hu
    have hU := Complex.slitPlane_ne_zero hu
    have hden : lambda + eta*u = lambda * B u := by
      dsimp [B,e]
      field_simp
      ring
    have hraw : rawLocal c x i u = lambda⁻¹*u/B u := by
      change u/(lambda+eta*u) = _
      rw [hden, div_eq_mul_inv, mul_inv]
      ring
    have hbase : 1-eta*rawLocal c x i u = (B u)⁻¹ := by
      rw [hraw]
      apply (mul_right_cancel₀ hU)
      rw [inv_mul_cancel₀ hU, sub_mul, one_mul, mul_assoc, div_mul_cancel₀ _ hU]
      dsimp [B,e]
      ring
    have hroot' : inverseRoot c x i u ^ 3 = (B u)^(-3/2:ℂ) := by
      unfold inverseRoot
      change ((1-eta*rawLocal c x i u)^(1/2:ℂ))^3 = _
      rw [hbase, Complex.inv_cpow _ _ (Complex.slitPlane_arg_ne_pi hu),
        ← Complex.cpow_neg, ← Complex.cpow_mul_nat]
      congr 1
      norm_num
    rw [hraw, halfJacobian, inv_div, hroot', div_eq_mul_inv, mul_comm _ root⁻¹]
  have hcoef : coefficient n (fun u => (halfJacobian c x i (inverseRoot c x i u))⁻¹ *
      F (rawLocal c x i u)) =
      coefficient n (fun u => root⁻¹ * (B u)^(-3/2:ℂ) * F (lambda⁻¹*u/B u)) := by
    unfold coefficient
    rw [he.iteratedDeriv_eq]
  rw [hcoef]
  change coefficient n (fun u => root⁻¹ * (1-e*u)^(-3/2:ℂ) * F (lambda⁻¹*u/(1-e*u))) = _
  rw [analytic_half_pullback_coefficient _ _ _ hF, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  have hp' : p ≤ n := by simpa using hp
  have hpow : root⁻¹ * lambda⁻¹ ^ n = root⁻¹ ^ (2*n+1) := by
    rw [← hroot, ← inv_pow, ← pow_mul, pow_succ, mul_comm]
  dsimp only [e]
  rw [mul_pow]
  calc
    _ = (root⁻¹ * (lambda⁻¹ ^ p * lambda⁻¹ ^ (n-p))) *
        (coefficient p F * ((-eta)^(n-p) * Ring.choose ((n:ℂ)+1/2) (n-p))) := by ring
    _ = _ := by
      rw [← pow_add, Nat.add_sub_of_le hp', hpow]

end D5.S3.VertexAlgebra.TwistedGround.OriginalFourMAnalyticPullback
