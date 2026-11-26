/- GID: D5/S3/Quantum/Analysis/RefinedBMV/Tracial/ResolventJensen
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Four-cycle comparison of an inverse arithmetic mean with the product of inverses. -/

import D5.S3.Quantum.Analysis.RefinedBMV.Tracial.LaplaceWord
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! The radial Gamma identity gives a cyclic Jensen comparison for the
fourth power of the reciprocal on a positive diagonal spectrum. -/

namespace RefinedBMV.Tracial

open Matrix MeasureTheory Set FourCopyGap Filter Topology

open private contract eigenDiagonal gapTrace gapTrace_diagonal monomial
  from D5.S3.Quantum.Analysis.RefinedBMV.SingularFourth.FourCopyGap
open private gamma_trace_weight gamma_trace_integrable
  from D5.S3.Quantum.Analysis.RefinedBMV.Tracial.LaplaceFourth
open private orthantMoment orthantMoment_eq_gaps fourRates raisedGap
  from D5.S3.Quantum.Analysis.RefinedBMV.Tracial.LaplaceWord

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem zero_gaps : gaps 0 = {(0, 0, 0, 0)} := by
  ext ⟨a, b, c, d⟩
  simp only [mem_gaps, Finset.mem_singleton, Prod.mk.injEq]
  omega

private theorem orthant_at_zero_eq_prod_inv {a b c d : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    orthantMoment 0 (fourRates a b c d) = a⁻¹ * b⁻¹ * c⁻¹ * d⁻¹ := by
  rw [orthantMoment_eq_gaps 0 ha hb hc hd]
  norm_num [zero_gaps, monomial, raisedGap]

private theorem trace_laplace_cycle_expansion (a : ι → ℝ) (B : Matrix ι ι ℂ) (s : ℝ) :
    (trace ((fourthLaplaceWeight a (fun _ ↦ 1) s * B) ^ 4)).re =
      ∑ i, ∑ j, ∑ k, ∑ l, Real.exp (-(((a i + a j + a k + a l) / 4) * s)) *
        (cycleTrace (spectralBlock id B) i j k l).re := by
  have h := congrArg Complex.re (gapTrace_diagonal id
    (fun i ↦ Real.exp (-(s * a i / 4))) B (1, 1, 1, 1))
  simp only [gapTrace, eigenDiagonal, id_eq, pow_one, monomial,
    contract, LinearMap.coe_mk, AddHom.coe_mk, Complex.re_sum, Complex.re_ofReal_mul] at h
  simp only [fourthLaplaceWeight, one_mul, pow_succ, pow_zero]
  rw [h]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦
    Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun l _ ↦ ?_
  rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  congr 2
  ring

/-- At order three the balanced Gamma integral is the cyclic contraction
of the inverse fourth power of the arithmetic spectral mean. -/
theorem fourth_laplace_gamma_eq_inverse_mean (a : ι → ℝ) (ha : ∀ i, 0 < a i)
    (B : Matrix ι ι ℂ) :
    (∫ s in Ioi (0 : ℝ), s ^ (3 : ℝ) *
      (trace ((fourthLaplaceWeight a (fun _ ↦ 1) s * B) ^ 4)).re) =
      6 * ∑ i, ∑ j, ∑ k, ∑ l, ((a i + a j + a k + a l) / 4)⁻¹ ^ (4 : ℕ) *
        (cycleTrace (spectralBlock id B) i j k l).re := by
  let q (i j k l : ι) := (a i + a j + a k + a l) / 4
  let c (i j k l : ι) := (cycleTrace (spectralBlock id B) i j k l).re
  let f (i j k l : ι) (s : ℝ) := (s ^ (3 : ℝ) * Real.exp (-(q i j k l * s))) * c i j k l
  have hq (i j k l : ι) : 0 < q i j k l :=
    div_pos (add_pos (add_pos (add_pos (ha i) (ha j)) (ha k)) (ha l)) (by norm_num)
  have hf (i j k l : ι) : IntegrableOn (f i j k l) (Ioi 0) :=
    (gamma_trace_integrable 3 (by norm_num) (hq i j k l)).mul_const (c i j k l)
  have hfun (s : ℝ) : s ^ (3 : ℝ) *
      (trace ((fourthLaplaceWeight a (fun _ ↦ 1) s * B) ^ 4)).re =
      ∑ i, ∑ j, ∑ k, ∑ l, f i j k l s := by
    rw [trace_laplace_cycle_expansion]
    simp only [Finset.mul_sum, f, q, c, mul_assoc]
  simp_rw [hfun]
  rw [MeasureTheory.integral_finsetSum _ (fun i _ ↦ integrable_finsetSum _ fun j _ ↦
    integrable_finsetSum _ fun k _ ↦ integrable_finsetSum _ fun l _ ↦ hf i j k l)]
  have hgamma : Real.Gamma 4 = 6 := by
    rw [show (4 : ℝ) = ↑(3 : ℕ) + 1 by norm_num, Real.Gamma_nat_eq_factorial]
    norm_num [Nat.factorial]
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [MeasureTheory.integral_finsetSum _ (fun j _ ↦
    integrable_finsetSum _ fun k _ ↦ integrable_finsetSum _ fun l _ ↦ hf i j k l)]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [MeasureTheory.integral_finsetSum _ (fun k _ ↦ integrable_finsetSum _ fun l _ ↦ hf i j k l)]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [MeasureTheory.integral_finsetSum _ (fun l _ ↦ hf i j k l)]
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  simp only [f]
  rw [MeasureTheory.integral_mul_const, gamma_trace_weight 3 (by norm_num) (hq i j k l),
    show (3 : ℝ) + 1 = 4 by norm_num, hgamma, one_div,
    show (4 : ℝ) = ↑(4 : ℕ) by norm_num, Real.rpow_natCast]
  change (q i j k l)⁻¹ ^ (4 : ℕ) * 6 * c i j k l = _
  dsimp only [q, c]
  ring

/-- The orthant Laplace integral at degree zero has the product of the
four inverse rates as its cyclic kernel. -/
theorem fourth_orthant_zero_eq_product_inverse (a : ι → ℝ) (ha : ∀ i, 0 < a i)
    (B : Matrix ι ι ℂ) :
    (fourthOrthantLaplaceMoment 0 a B).re =
      ∑ i, ∑ j, ∑ k, ∑ l, (a i)⁻¹ * (a j)⁻¹ * (a k)⁻¹ * (a l)⁻¹ *
        (cycleTrace (spectralBlock id B) i j k l).re := by
  simp only [fourthOrthantLaplaceMoment, contract, LinearMap.coe_mk, AddHom.coe_mk,
    Complex.re_sum, Complex.re_ofReal_mul]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦
    Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun l _ ↦ ?_
  rw [orthant_at_zero_eq_prod_inv (ha i) (ha j) (ha k) (ha l)]

/-- For positive diagonal spectral data and a Hermitian factor, the cyclic
contraction of the inverse fourth power of the arithmetic spectral mean
is bounded by the contraction of the product of the four inverse rates. -/
theorem fourth_cycle_inv_mean_le_product_inverse (a : ι → ℝ) (ha : ∀ i, 0 < a i)
    (B : Matrix ι ι ℂ) (hB : B.IsHermitian) :
    (∑ i, ∑ j, ∑ k, ∑ l, ((a i + a j + a k + a l) / 4)⁻¹ ^ (4 : ℕ) *
      (cycleTrace (spectralBlock id B) i j k l).re) ≤
      ∑ i, ∑ j, ∑ k, ∑ l, (a i)⁻¹ * (a j)⁻¹ * (a k)⁻¹ * (a l)⁻¹ *
        (cycleTrace (spectralBlock id B) i j k l).re := by
  have h := fourth_laplace_moment_le_orthant_of_word_bound 0 a ha B hB (by
    simp only [Nat.cast_zero, zero_div, neg_zero, Real.rpow_zero, Complex.ofReal_one,
      Matrix.diagonal_one, one_mul, wordMean_eq_gaps, zero_gaps, Finset.sum_singleton,
      Finset.card_singleton, Nat.cast_one, div_one, gapTrace, pow_zero]
    rw [pow_succ, pow_succ, pow_succ, pow_succ, pow_zero, one_mul])
  simp only [Nat.cast_zero, zero_add, fourth_laplace_gamma_eq_inverse_mean a ha B,
    fourth_orthant_zero_eq_product_inverse a ha B] at h
  exact (mul_le_mul_iff_right₀ (show (0 : ℝ) < 6 by norm_num)).mp h

/-- The density for the positive mixture of shifted fourth resolvent powers. -/
def resolventDensity (a b c d u : ℝ) : ℝ :=
  3 * u ^ 2 * ((a + u)⁻¹ * (b + u)⁻¹ * (c + u)⁻¹ * (d + u)⁻¹)

private theorem integrable_resolventDensity {a b c d : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    IntegrableOn (resolventDensity a b c d) (Ioi 0) := by
  let m := min (min a b) (min c d)
  have hm : 0 < m := lt_min (lt_min ha hb) (lt_min hc hd)
  have hbound : IntegrableOn (fun u : ℝ ↦ 3 * (u + m) ^ (-2 : ℝ)) (Ioi 0) :=
    (integrableOn_add_rpow_Ioi_of_lt (by norm_num) (by linarith : -m < 0)).const_mul 3
  refine hbound.mono' (by unfold resolventDensity; fun_prop) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  have hu' : 0 < u := hu
  have hmu : 0 < m + u := add_pos hm hu'
  have hma : m ≤ a := (min_le_left _ _).trans (min_le_left _ _)
  have hmb : m ≤ b := (min_le_left _ _).trans (min_le_right _ _)
  have hmc : m ≤ c := (min_le_right _ _).trans (min_le_left _ _)
  have hmd : m ≤ d := (min_le_right _ _).trans (min_le_right _ _)
  rw [Real.norm_eq_abs, abs_of_nonneg (by unfold resolventDensity; positivity)]
  calc
    resolventDensity a b c d u ≤ resolventDensity m m m m u := by
      unfold resolventDensity
      gcongr
    _ ≤ 3 * (u + m) ^ (-2 : ℝ) := by
      rw [show (-2 : ℝ) = -(2 : ℕ) by norm_num, Real.rpow_neg (by positivity),
        Real.rpow_natCast, add_comm u m]
      unfold resolventDensity
      have hsq : u ^ 2 ≤ (m + u) ^ 2 := by gcongr; linarith
      field_simp [hmu.ne']
      nlinarith only [hsq]

private theorem integral_resolventDensity_same {a : ℝ} (ha : 0 < a) :
    (∫ u in Ioi (0 : ℝ), resolventDensity a a a a u) = a⁻¹ := by
  let primitive (u : ℝ) := (u / (a + u)) ^ 3 / a
  have hderiv (u : ℝ) (hu : u ∈ Ici (0 : ℝ)) :
      HasDerivAt primitive (resolventDensity a a a a u) u := by
    have hau : a + u ≠ 0 := (add_pos_of_pos_of_nonneg ha hu).ne'
    have h := (((hasDerivAt_id u).div ((hasDerivAt_id u).const_add a) hau).pow 3).div_const a
    convert h using 1
    · rfl
    · unfold resolventDensity
      dsimp
      field_simp [ha.ne', hau]
      ring
  have hinv : Filter.Tendsto (fun u : ℝ ↦ (a + u)⁻¹) Filter.atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_left _ a tendsto_id)
  have hratio : Filter.Tendsto (fun u : ℝ ↦ u / (a + u)) Filter.atTop (𝓝 1) := by
    have h := (tendsto_const_nhds (x := (1 : ℝ))).sub (hinv.const_mul a)
    rw [mul_zero, sub_zero] at h
    apply h.congr' _
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with u hu
    field_simp [(add_pos ha hu).ne']
    ring
  have hlim : Filter.Tendsto primitive Filter.atTop (𝓝 a⁻¹) := by
    simpa only [primitive, one_pow, one_div] using (hratio.pow 3).div_const a
  rw [integral_Ioi_of_hasDerivAt_of_tendsto' hderiv
    (integrable_resolventDensity ha ha ha ha) hlim]
  simp [primitive]

/-- The ordinary resolvent kernel is a positive mixture of the shifted
inverse-fourth-power kernels. The cyclic inequality holds for arbitrary
Hermitian `B` and arbitrary positive spectral data. -/
theorem fourth_cycle_inv_mean_le_resolvent_integral (a : ι → ℝ) (ha : ∀ i, 0 < a i)
    (B : Matrix ι ι ℂ) (hB : B.IsHermitian) :
    (∑ i, ∑ j, ∑ k, ∑ l, ((a i + a j + a k + a l) / 4)⁻¹ *
      (cycleTrace (spectralBlock id B) i j k l).re) ≤
      ∑ i, ∑ j, ∑ k, ∑ l, (∫ u in Ioi (0 : ℝ),
        resolventDensity (a i) (a j) (a k) (a l) u) *
        (cycleTrace (spectralBlock id B) i j k l).re := by
  let q (i j k l : ι) := (a i + a j + a k + a l) / 4
  let c (i j k l : ι) := (cycleTrace (spectralBlock id B) i j k l).re
  have hq (i j k l : ι) : 0 < q i j k l := by
    exact div_pos (add_pos (add_pos (add_pos (ha i) (ha j)) (ha k)) (ha l)) (by norm_num)
  have h_integral (p r s t : ι → ι → ι → ι → ℝ)
      (hp : ∀ i j k l, 0 < p i j k l) (hr : ∀ i j k l, 0 < r i j k l)
      (hs : ∀ i j k l, 0 < s i j k l) (ht : ∀ i j k l, 0 < t i j k l) :
      IntegrableOn (fun u ↦ ∑ i, ∑ j, ∑ k, ∑ l,
        resolventDensity (p i j k l) (r i j k l) (s i j k l) (t i j k l) u * c i j k l)
        (Ioi 0) ∧
      (∫ u in Ioi (0 : ℝ), ∑ i, ∑ j, ∑ k, ∑ l,
        resolventDensity (p i j k l) (r i j k l) (s i j k l) (t i j k l) u * c i j k l) =
        ∑ i, ∑ j, ∑ k, ∑ l, (∫ u in Ioi (0 : ℝ),
          resolventDensity (p i j k l) (r i j k l) (s i j k l) (t i j k l) u) * c i j k l := by
    have hterm (i j k l : ι) := (integrable_resolventDensity
      (hp i j k l) (hr i j k l) (hs i j k l) (ht i j k l)).mul_const (c i j k l)
    refine ⟨integrable_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦
      integrable_finsetSum _ fun k _ ↦ integrable_finsetSum _ fun l _ ↦ hterm i j k l, ?_⟩
    rw [integral_finsetSum _ (fun i _ ↦ integrable_finsetSum _ fun j _ ↦
      integrable_finsetSum _ fun k _ ↦ integrable_finsetSum _ fun l _ ↦ hterm i j k l)]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [integral_finsetSum _ (fun j _ ↦ integrable_finsetSum _ fun k _ ↦
      integrable_finsetSum _ fun l _ ↦ hterm i j k l)]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [integral_finsetSum _ (fun k _ ↦ integrable_finsetSum _ fun l _ ↦ hterm i j k l)]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [integral_finsetSum _ (fun l _ ↦ hterm i j k l)]
    exact Finset.sum_congr rfl fun l _ ↦ integral_mul_const _ _
  have hleft := h_integral q q q q hq hq hq hq
  have hright := h_integral (fun i _ _ _ ↦ a i) (fun _ j _ _ ↦ a j)
    (fun _ _ k _ ↦ a k) (fun _ _ _ l ↦ a l)
    (fun i _ _ _ ↦ ha i) (fun _ j _ _ ↦ ha j) (fun _ _ k _ ↦ ha k) (fun _ _ _ l ↦ ha l)
  simp_rw [integral_resolventDensity_same (hq _ _ _ _)] at hleft
  rw [← hleft.2, ← hright.2]
  refine integral_mono_ae hleft.1 hright.1 ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  have hu' : 0 < u := hu
  have h := fourth_cycle_inv_mean_le_product_inverse (fun i ↦ a i + u)
    (fun i ↦ add_pos (ha i) hu') B hB
  have hq_shift (i j k l : ι) :
      (a i + u + (a j + u) + (a k + u) + (a l + u)) / 4 = q i j k l + u := by
    dsimp [q]
    ring
  simp_rw [hq_shift] at h
  have hmul := mul_le_mul_of_nonneg_left h (show 0 ≤ 3 * u ^ 2 by positivity)
  simpa only [Finset.mul_sum, resolventDensity, c, pow_succ, pow_zero, one_mul, mul_assoc]
    using hmul

private def interpolate (x y t : ℝ) : ℝ := y + (x - y) * t

private theorem interpolate_pos {x y t : ℝ} (hx : 0 < x) (hy : 0 < y)
    (ht : t ∈ Icc (0 : ℝ) 1) : 0 < interpolate x y t := by
  have heq : interpolate x y t = (1 - t) * y + t * x := by
    unfold interpolate
    ring
  rw [heq]
  rcases ht.2.eq_or_lt with he | hlt
  · simpa [he] using hx
  · exact add_pos_of_pos_of_nonneg (mul_pos (sub_pos.mpr hlt) hy) (mul_nonneg ht.1 hx.le)

private theorem integral_beta_resolvent (n : ℕ) {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    (∫ t in (0 : ℝ)..1, ((n : ℝ) + 1) * t ^ n * (interpolate x y t)⁻¹ ^ (n + 2)) =
      x⁻¹ ^ (n + 1) * y⁻¹ := by
  let P (t : ℝ) := y⁻¹ * (t / interpolate x y t) ^ (n + 1)
  have hden (t : ℝ) (ht : t ∈ uIcc (0 : ℝ) 1) : 0 < interpolate x y t :=
    interpolate_pos hx hy (by simpa only [uIcc_of_le zero_le_one] using ht)
  have hderiv (t : ℝ) (ht : t ∈ uIcc (0 : ℝ) 1) : HasDerivAt P
      (((n : ℝ) + 1) * t ^ n * (interpolate x y t)⁻¹ ^ (n + 2)) t := by
    have hI : HasDerivAt (interpolate x y) (x - y) t := by
      convert ((hasDerivAt_id t).const_mul (x - y)).const_add y using 1
      · rfl
      · ring
    have h := (((hasDerivAt_id t).div hI (hden t ht).ne').pow (n + 1)).const_mul y⁻¹
    convert h using 1
    · rfl
    · have hsub : 1 * interpolate x y t - t * (x - y) = y := by
        unfold interpolate
        ring
      have hdiv : ((id : ℝ → ℝ) / interpolate x y) t = t / interpolate x y t := rfl
      simp only [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel, id_eq, hsub, hdiv, div_pow, inv_pow,
        pow_succ _ (n + 1), pow_succ _ n]
      field_simp [(hden t ht).ne', hy.ne']
  have hc : ContinuousOn
      (fun t : ℝ ↦ ((n : ℝ) + 1) * t ^ n * (interpolate x y t)⁻¹ ^ (n + 2)) (uIcc 0 1) := by
    have hI : Continuous (interpolate x y) := by unfold interpolate; fun_prop
    exact ((continuous_const.mul (continuous_id.pow n)).continuousOn).mul
      ((hI.continuousOn.inv₀ fun t ht ↦ (hden t ht).ne').pow (n + 2))
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hc.intervalIntegrable]
  have h1 : interpolate x y 1 = x := by unfold interpolate; ring
  simp [P, h1, mul_comm]

/-- The mean over four uniform simplex weights, written as the iterated
mean over the independent Beta(1,1), Beta(2,1), and Beta(3,1) weights. -/
def fourthSimplexMean (f : ℝ → ℝ) (a b c d : ℝ) : ℝ :=
  ∫ w in (0 : ℝ)..1, ∫ v in (0 : ℝ)..1, 2 * v *
    (∫ u in (0 : ℝ)..1, 3 * u ^ 2 *
      f (interpolate (interpolate (interpolate a b w) c v) d u))

/-- The inverse-fourth-power simplex mean is the product of four
ordinary reciprocals, including repeated knots. -/
theorem fourthSimplexMean_inv_fourth {a b c d : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    fourthSimplexMean (fun x ↦ x⁻¹ ^ 4) a b c d = a⁻¹ * b⁻¹ * c⁻¹ * d⁻¹ := by
  unfold fourthSimplexMean
  calc
    _ = ∫ w in (0 : ℝ)..1, ((interpolate a b w)⁻¹ ^ 2 * c⁻¹) * d⁻¹ := by
      apply intervalIntegral.integral_congr
      intro w hw
      have hp : 0 < interpolate a b w :=
        interpolate_pos ha hb (by simpa only [uIcc_of_le zero_le_one] using hw)
      calc
        _ = ∫ v in (0 : ℝ)..1, 2 * v * (interpolate (interpolate a b w) c v)⁻¹ ^ 3 * d⁻¹ := by
          apply intervalIntegral.integral_congr
          intro v hv
          have hq : 0 < interpolate (interpolate a b w) c v :=
            interpolate_pos hp hc (by simpa only [uIcc_of_le zero_le_one] using hv)
          dsimp only
          rw [show (∫ u in (0 : ℝ)..1, 3 * u ^ 2 *
              (interpolate (interpolate (interpolate a b w) c v) d u)⁻¹ ^ 4) = _ from by
              simpa only [Nat.cast_ofNat, show (2 : ℝ) + 1 = 3 by norm_num] using
                integral_beta_resolvent 2 hq hd]
          ring
        _ = _ := by
          rw [intervalIntegral.integral_mul_const]
          congr 1
          simpa only [Nat.cast_one, one_add_one_eq_two, pow_one] using
            integral_beta_resolvent 1 hp hc
    _ = _ := by
      rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_mul_const]
      congr 2
      simpa only [Nat.cast_zero, zero_add, pow_zero, mul_one, one_mul, pow_one] using
        integral_beta_resolvent 0 ha hb

end

end RefinedBMV.Tracial
