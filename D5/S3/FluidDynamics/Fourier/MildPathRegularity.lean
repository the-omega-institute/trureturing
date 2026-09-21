/- GID: D5/S3/FluidDynamics/Fourier/MildPathRegularity
   generality: G
   mirror-B: D5/B/S3/FluidDynamics/Fourier/MildPathRegularity
   mirror-E: none(waiver:universal-analytic-estimate)
   anchors: []
   utility: none
   digest: Every spatial grade of the same mild Fourier path satisfies the strong equation on the original closed interval. -/

/-
SPDX-License-Identifier: Apache-2.0
The Volterra continuity argument adapts Euler/VolterraConvolution.lean from
https://github.com/openai/NavierStokesAndEuler/tree/8937a8f4cbc7abaab5e9e97d1cc7f5d2319d9538
using measurability of the sequence coordinates.
-/

import Mathlib
import D5.S3.FluidDynamics.Fourier.WeightedTensorConvolution

open scoped BigOperators ENNReal
open Set MeasureTheory Filter Topology
open D5.S3.FluidDynamics.Fourier.WeightedTensorConvolution
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace D5.S3.FluidDynamics.Fourier.MildPathRegularity

/-- All spatial grades of the given mild path obey the strong equation on the same closed interval. -/
theorem all_grade_regularity_of_mild_path : (∀ (ν τ : ℝ), 0 < ν → 0 < τ →
  let K := ℤ × ℤ
  let V := EuclideanSpace ℂ (Fin 2)
  let H := lp (fun _ : K => V) 2
  let ρ : K → ℝ := fun k => (k.1 : ℝ)^2 + (k.2 : ℝ)^2
  let κ : K → V := fun k => WithLp.toLp 2 (fun i => (![k.1, k.2] i : ℂ))
  let P := fun k => (ℂ ∙ κ k)ᗮ.starProjection
  let w : ℕ → K → ℝ := fun m k => (1 + ρ k) ^ ((m : ℝ) / 2)
  let dec : ℕ → H → K → V := fun m x k => (w m k)⁻¹ • x k
  let N : (K → V) → (K → V) → K → V := fun a b k =>
    Complex.I • P k (∑' l : K, (∑ j : Fin 2, κ k j * a l j) • b (k-l))
  ∀ (x₂ : ℝ → H),
  let a : ℝ → K → V := fun t k => (1 + ρ k)⁻¹ • x₂ t k
  ContinuousOn x₂ (Icc 0 τ) →
  (∀ t ∈ Icc 0 τ, a t 0 = 0 ∧
    (∀ k i, a t (-k) i = star (a t k i)) ∧
    (∀ k, ∑ j : Fin 2, κ k j * a t k j = 0)) →
  (∀ m : ℕ, Summable (fun k => ‖w m k • a 0 k‖^2)) →
  (∀ t ∈ Icc 0 τ, ∀ k,
    IntervalIntegrable (fun s => Real.exp (-ν * (t-s) * ρ k) • N (a s) (a s) k)
      volume 0 t ∧
    a t k = Real.exp (-ν * t * ρ k) • a 0 k -
      ∫ s in (0 : ℝ)..t, Real.exp (-ν * (t-s) * ρ k) • N (a s) (a s) k) →
  ∃ (U : ℕ → ℝ → H)
    (L : ℕ → H →L[ℝ] H)
    (B : ℕ → H →L[ℝ] H →L[ℝ] H),
    (∀ m t, t ∈ Icc 0 τ → ∀ k, U m t k = w m k • a t k) ∧
    (∀ m, ContinuousOn (U m) (Icc 0 τ)) ∧
    (∀ m x k, L m x k = w m k • ((-ν * ρ k) • dec (m+2) x k)) ∧
    (∀ m x y k, B m x y k = w m k • N (dec (m+2) x) (dec (m+2) y) k) ∧
    (∀ m t, t ∈ Icc 0 τ →
      HasDerivWithinAt (U m)
        (L m (U (m+2) t) - B m (U (m+2) t) (U (m+2) t))
        (Icc 0 τ) t) : Prop) := by
  classical
  intro ν τ hν hτ K V H ρ κ P w dec N x₂ a hx hgeom hinit hmild
  have hρ (k : K) : 0 ≤ ρ k := by dsimp [ρ]; positivity
  have hW (k : K) : 0 < 1 + ρ k := by positivity
  have hweight (k : K) : weight k = 1 + ρ k := by dsimp [weight, ρ]; ring
  have henergy (t : ℝ) :
      Summable (fun k : K => weight k ^ 2 * ‖a t k‖ ^ 2) ∧
      Real.sqrt (∑' k : K, weight k ^ 2 * ‖a t k‖ ^ 2) = ‖x₂ t‖ := by
    have he (k : K) : weight k ^ 2 * ‖a t k‖ ^ 2 = ‖x₂ t k‖ ^ 2 := by
      dsimp [a]
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hW k)), hweight]
      field_simp [(hW k).ne']
    simp_rw [he]
    refine ⟨?_, ?_⟩
    · simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
        (lp.hasSum_norm (by norm_num : 0 < (2 : ℝ≥0∞).toReal) (x₂ t)).summable
    · have hn : ‖x₂ t‖ ^ 2 = ∑' k : K, ‖x₂ t k‖ ^ 2 := by
        simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
          lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal) (x₂ t)
      rw [← hn, Real.sqrt_sq (norm_nonneg _)]
  have hGaussian (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
      (r : ℝ) (hr : 0 < r) (k : K) :
      (ρ k) ^ p * Real.exp (-ν * r * ρ k) ≤ (ν * r) ^ (-p) := by
    have hc : 0 < ν * r := mul_pos hν hr
    have hz : 0 ≤ ν * r * ρ k := mul_nonneg hc.le (hρ k)
    have he : ν * r * ρ k ≤ Real.exp (ν * r * ρ k) :=
      (le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp _)
    have heP := Real.rpow_le_rpow hz he hp
    have hB : (ν * r) ^ p * ((ρ k) ^ p * Real.exp (-ν * r * ρ k)) ≤ 1 := by
      calc
        _ = (ν * r * ρ k) ^ p * Real.exp (-(ν * r * ρ k)) := by
          rw [Real.mul_rpow hc.le (hρ k)]
          rw [show -ν * r * ρ k = -(ν * r * ρ k) by ring]
          ring
        _ ≤ (Real.exp (ν * r * ρ k)) ^ p * Real.exp (-(ν * r * ρ k)) :=
          mul_le_mul_of_nonneg_right heP (Real.exp_pos _).le
        _ = Real.exp (ν * r * ρ k * (p - 1)) := by
          rw [← Real.exp_mul, ← Real.exp_add]
          congr 1
          ring
        _ ≤ 1 := Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos hz (sub_nonpos.mpr hp1))
    rw [Real.rpow_neg hc.le]
    rw [← one_div]
    apply (le_div_iff₀ (Real.rpow_pos_of_pos hc p)).mpr
    simpa [mul_comm] using hB

  let c : ℝ → ℝ := fun r => (ν*r) ^ (-(1/2:ℝ)) + (ν*r) ^ (-(3/4:ℝ))
  have hc0 (r : ℝ) (hr : 0 ≤ r) : 0 ≤ c r :=
    add_nonneg (Real.rpow_nonneg (mul_nonneg hν.le hr) _)
      (Real.rpow_nonneg (mul_nonneg hν.le hr) _)
  have hMultiplier (r : ℝ) (hr : 0 < r) (k : K) :
      (1+ρ k) ^ (1/4:ℝ) * Real.sqrt (ρ k) * Real.exp (-ν*r*ρ k) ≤ c r := by
    have hWq : (1+ρ k) ^ (1/4:ℝ) ≤ 1 + (ρ k) ^ (1/4:ℝ) := by
      simpa using Real.rpow_add_le_add_rpow (by norm_num : (0:ℝ)≤1) (hρ k)
        (by norm_num : (0:ℝ)≤1/4) (by norm_num : (1/4:ℝ)≤1)
    have heq : (ρ k) ^ (1/4:ℝ) * Real.sqrt (ρ k) = (ρ k) ^ (3/4:ℝ) := by
      rcases (hρ k).eq_or_lt with hz | hz
      · rw [← hz]; norm_num
      · rw [Real.sqrt_eq_rpow, ← Real.rpow_add hz]
        norm_num
    calc
      _ ≤ (1+(ρ k)^(1/4:ℝ)) * Real.sqrt (ρ k) * Real.exp (-ν*r*ρ k) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hWq (Real.sqrt_nonneg _)) (Real.exp_pos _).le
      _ = (ρ k)^(1/2:ℝ)*Real.exp (-ν*r*ρ k) +
          (ρ k)^(3/4:ℝ)*Real.exp (-ν*r*ρ k) := by
        rw [add_mul, one_mul, heq, add_mul, Real.sqrt_eq_rpow]
      _ ≤ c r := add_le_add (hGaussian (1/2) (by norm_num) (by norm_num) r hr k)
        (hGaussian (3/4) (by norm_num) (by norm_num) r hr k)
  have hcInt : IntervalIntegrable c volume 0 τ := by
    have hpart (p : ℝ) (hp : -1 < p) :
        IntervalIntegrable (fun r : ℝ => (ν*r)^p) volume 0 τ := by
      have hi := (intervalIntegral.intervalIntegrable_rpow' (a:=0) (b:=τ) hp).const_mul (ν^p)
      apply hi.congr
      intro r hr
      rw [uIoc_of_le hτ.le] at hr
      exact (Real.mul_rpow hν.le hr.1.le).symm
    exact (hpart (-(1/2)) (by norm_num)).add (hpart (-(3/4)) (by norm_num))
  let TV := EuclideanSpace ℂ (Fin 2 × Fin 2)
  let G := lp (fun _ : K => TV) 2
  have hProduct (α : ℝ) (hα : 0 ≤ α) (aa bb : K → V)
      (haa : Summable (fun k => (weight k * weight k^α)^2 * ‖aa k‖^2))
      (hbb : Summable (fun k => (weight k * weight k^α)^2 * ‖bb k‖^2)) :
      (∀ k, Summable (fun p => ‖outer (aa p) (bb (k-p))‖)) ∧
      Summable (fun k => (weight k * weight k^α)^2 * ‖convolution aa bb k‖^2) ∧
      Real.sqrt (∑' k, (weight k * weight k^α)^2 * ‖convolution aa bb k‖^2) ≤
        (32 * (4:ℝ)^α) * Real.sqrt (∑' k, (weight k * weight k^α)^2 * ‖aa k‖^2) *
          Real.sqrt (∑' k, (weight k * weight k^α)^2 * ‖bb k‖^2) := by
    let C : ℝ := (4:ℝ)^α
    have hC : 0 ≤ C := Real.rpow_nonneg (by norm_num) α
    have hw (k : K) : 1 ≤ weight k := by rw [hweight]; linarith [hρ k]
    have hw0 (k : K) : 0 ≤ weight k := (zero_le_one.trans (hw k))
    have hWα (k p : K) : weight k^α ≤ C * (weight p^α + weight (k-p)^α) := by
      have ht : weight k ≤ 2 * (weight p + weight (k-p)) := by
        change 1 + (k.1:ℝ)^2 + (k.2:ℝ)^2 ≤ 2 * ((1+(p.1:ℝ)^2+(p.2:ℝ)^2) + (1+((k.1-p.1:ℤ):ℝ)^2+((k.2-p.2:ℤ):ℝ)^2))
        push_cast
        nlinarith [sq_nonneg ((p.1:ℝ) - ((k.1:ℝ)-(p.1:ℝ))),
          sq_nonneg ((p.2:ℝ) - ((k.2:ℝ)-(p.2:ℝ)))]
      rcases le_total (weight p) (weight (k-p)) with hp | hp
      · have ht' : weight k ≤ 4 * weight (k-p) := by linarith
        calc
          _ ≤ (4 * weight (k-p))^α := Real.rpow_le_rpow (hw0 k) ht' hα
          _ = C * weight (k-p)^α := Real.mul_rpow (by norm_num) (hw0 _)
          _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (Real.rpow_nonneg (hw0 p) α)) hC
      · have ht' : weight k ≤ 4 * weight p := by linarith
        calc
          _ ≤ (4 * weight p)^α := Real.rpow_le_rpow (hw0 k) ht' hα
          _ = C * weight p^α := Real.mul_rpow (by norm_num) (hw0 _)
          _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (Real.rpow_nonneg (hw0 (k-p)) α)) hC
    have hdown (c : ℤ × ℤ → EuclideanSpace ℂ (Fin 2)) (k : ℤ × ℤ) :
        weight k^2 * ‖c k‖^2 ≤ (weight k * weight k^α)^2 * ‖c k‖^2 := by
      have he : 1 ≤ weight k ^ α := Real.one_le_rpow (hw k) hα
      have hmul : weight k ≤ weight k * weight k^α := by nlinarith [hw0 k]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (hw0 k) hmul 2) (sq_nonneg _)
    have ha2 := haa.of_nonneg_of_le (fun k => by positivity) (hdown aa)
    have hb2 := hbb.of_nonneg_of_le (fun k => by positivity) (hdown bb)
    have hab := weighted_tensor_convolution aa bb ha2 hb2
    have houter (x y : EuclideanSpace ℂ (Fin 2)) : ‖outer x y‖ = ‖x‖ * ‖y‖ := by
      apply (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
      simp only [EuclideanSpace.norm_sq_eq, outer, mul_pow, norm_mul,
        Fintype.sum_prod_type, ← Finset.mul_sum, ← Finset.sum_mul]
    let E : ℝ → EuclideanSpace ℂ (Fin 2) := fun r => PiLp.single 2 0 (r : ℂ)
    have hE (r : ℝ) (hr : 0 ≤ r) : ‖E r‖ = r := by
      simp only [E, PiLp.norm_single, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr]
    let A0 := fun k => E ‖aa k‖
    let B0 := fun k => E ‖bb k‖
    let A5 := fun k => E (weight k^α * ‖aa k‖)
    let B5 := fun k => E (weight k^α * ‖bb k‖)
    have hA0 (k) : weight k^2 * ‖A0 k‖^2 = weight k^2 * ‖aa k‖^2 := by
      rw [hE _ (norm_nonneg _)]
    have hB0 (k) : weight k^2 * ‖B0 k‖^2 = weight k^2 * ‖bb k‖^2 := by
      rw [hE _ (norm_nonneg _)]
    have hA5 (k) : weight k^2 * ‖A5 k‖^2 = (weight k * weight k^α)^2 * ‖aa k‖^2 := by
      rw [hE _ (mul_nonneg (Real.rpow_nonneg (hw0 k) α) (norm_nonneg _))]; ring
    have hB5 (k) : weight k^2 * ‖B5 k‖^2 = (weight k * weight k^α)^2 * ‖bb k‖^2 := by
      rw [hE _ (mul_nonneg (Real.rpow_nonneg (hw0 k) α) (norm_nonneg _))]; ring
    have hA0s := ha2.congr (fun k => (hA0 k).symm)
    have hB0s := hb2.congr (fun k => (hB0 k).symm)
    have hA5s := haa.congr (fun k => (hA5 k).symm)
    have hB5s := hbb.congr (fun k => (hB5 k).symm)
    have hm1 := weighted_tensor_convolution A5 B0 hA5s hB0s
    have hm2 := weighted_tensor_convolution A0 B5 hA0s hB5s
    have positive_row (C D : ℤ × ℤ → ℝ) (hC : ∀ k, 0 ≤ C k) (hD : ∀ k, 0 ≤ D k)
        (k : ℤ × ℤ) (hs : Summable (fun p => ‖outer (E (C p)) (E (D (k-p)))‖)) :
        Summable (fun p => C p * D (k-p)) ∧
        (∑' p, C p * D (k-p)) ≤ ‖D5.S3.FluidDynamics.Fourier.WeightedTensorConvolution.convolution (fun p => E (C p)) (fun p => E (D p)) k‖ := by
      have hn (p) : ‖outer (E (C p)) (E (D (k-p)))‖ = C p * D (k-p) := by
        rw [houter, hE _ (hC p), hE _ (hD (k-p))]
      have hs' := hs.congr hn
      refine ⟨hs', ?_⟩
      have hp := (PiLp.proj 2 (𝕜 := ℂ) (fun _ : Fin 2 × Fin 2 => ℂ) (0,0)).hasSum hs.of_norm.hasSum
      have hr := Complex.ofRealCLM.hasSum hs'.hasSum
      have hc : (D5.S3.FluidDynamics.Fourier.WeightedTensorConvolution.convolution (fun p => E (C p)) (fun p => E (D p)) k) (0,0) =
          ((∑' p, C p * D (k-p) : ℝ) : ℂ) := by
        apply hp.unique
        simpa only [Function.comp_def, PiLp.proj_apply, outer, PiLp.toLp_apply,
          E, PiLp.single_eq_same, Complex.ofRealCLM_apply, Complex.ofReal_mul] using hr
      have hh := PiLp.norm_apply_le
        (D5.S3.FluidDynamics.Fourier.WeightedTensorConvolution.convolution (fun p => E (C p)) (fun p => E (D p)) k) (0,0)
      rw [hc, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (tsum_nonneg (fun p => mul_nonneg (hC p) (hD (k-p))))] at hh
      exact hh
    have hp1 (k) := positive_row (fun p => weight p^α * ‖aa p‖) (fun p => ‖bb p‖)
      (fun p => mul_nonneg (Real.rpow_nonneg (hw0 p) α) (norm_nonneg _)) (fun p => norm_nonneg _) k (hm1.1 k)
    have hp2 (k) := positive_row (fun p => ‖aa p‖) (fun p => weight p^α * ‖bb p‖)
      (fun p => norm_nonneg _) (fun p => mul_nonneg (Real.rpow_nonneg (hw0 p) α) (norm_nonneg _)) k (hm2.1 k)
    have hpoint (k : ℤ × ℤ) : (weight k * weight k^α) * ‖D5.S3.FluidDynamics.Fourier.WeightedTensorConvolution.convolution aa bb k‖ ≤
        C * (weight k * ‖D5.S3.FluidDynamics.Fourier.WeightedTensorConvolution.convolution A5 B0 k‖ + weight k * ‖D5.S3.FluidDynamics.Fourier.WeightedTensorConvolution.convolution A0 B5 k‖) := by
      have hs : Summable (fun p => ‖aa p‖ * ‖bb (k-p)‖) := (hab.1 k).congr (fun p => houter _ _)
      have hh : weight k^α * ‖D5.S3.FluidDynamics.Fourier.WeightedTensorConvolution.convolution aa bb k‖ ≤
          C * (‖D5.S3.FluidDynamics.Fourier.WeightedTensorConvolution.convolution A5 B0 k‖ + ‖D5.S3.FluidDynamics.Fourier.WeightedTensorConvolution.convolution A0 B5 k‖) := by
        calc
          _ ≤ weight k^α * ∑' p, ‖aa p‖ * ‖bb (k-p)‖ := by
            apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (hw0 k) α)
            simpa only [D5.S3.FluidDynamics.Fourier.WeightedTensorConvolution.convolution, houter] using norm_tsum_le_tsum_norm (hab.1 k)
          _ = ∑' p, weight k^α * (‖aa p‖ * ‖bb (k-p)‖) := (tsum_mul_left).symm
          _ ≤ ∑' p, C * ((weight p^α * ‖aa p‖) * ‖bb (k-p)‖ +
              ‖aa p‖ * (weight (k-p)^α * ‖bb (k-p)‖)) := by
            apply (hs.mul_left _).tsum_le_tsum _ (((hp1 k).1.add (hp2 k).1).mul_left C)
            intro p
            have h := mul_le_mul_of_nonneg_right (hWα k p)
              (mul_nonneg (norm_nonneg (aa p)) (norm_nonneg (bb (k-p))))
            nlinarith only [h]
          _ = C * ((∑' p, (weight p^α * ‖aa p‖) * ‖bb (k-p)‖) +
              ∑' p, ‖aa p‖ * (weight (k-p)^α * ‖bb (k-p)‖)) := by
            rw [tsum_mul_left, ((hp1 k).1).tsum_add (hp2 k).1]
          _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add (hp1 k).2 (hp2 k).2) (by positivity)
      have h := mul_le_mul_of_nonneg_left hh (hw0 k)
      nlinarith only [h]
    let f1 := fun k => weight k * ‖D5.S3.FluidDynamics.Fourier.WeightedTensorConvolution.convolution A5 B0 k‖
    let f2 := fun k => weight k * ‖D5.S3.FluidDynamics.Fourier.WeightedTensorConvolution.convolution A0 B5 k‖
    let g := fun k => (weight k * weight k^α) * ‖D5.S3.FluidDynamics.Fourier.WeightedTensorConvolution.convolution aa bb k‖
    have hf1 : Memℓp f1 2 := memℓp_gen (by
      simpa only [ENNReal.toReal_ofNat, Real.rpow_two, f1, norm_mul,
        Real.norm_eq_abs, sq_abs, mul_pow, norm_norm] using hm1.2.1)
    have hf2 : Memℓp f2 2 := memℓp_gen (by
      simpa only [ENNReal.toReal_ofNat, Real.rpow_two, f2, norm_mul,
        Real.norm_eq_abs, sq_abs, mul_pow, norm_norm] using hm2.2.1)
    let F1 : lp (fun _ : ℤ × ℤ => ℝ) 2 := ⟨f1, hf1⟩
    let F2 : lp (fun _ : ℤ × ℤ => ℝ) 2 := ⟨f2, hf2⟩
    let Y := (C : ℝ) • (F1 + F2)
    have hdom (k) : ‖g k‖ ≤ Y k := by
      simpa only [g, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (mul_nonneg (hw0 k) (Real.rpow_nonneg (hw0 k) α)) (norm_nonneg _)),
        Y, lp.coeFn_smul, lp.coeFn_add, F1, F2, f1, f2, Pi.smul_apply, Pi.add_apply, smul_eq_mul] using hpoint k
    have hg : Memℓp g 2 := (lp.memℓp Y).mono hdom
    let GG : lp (fun _ : ℤ × ℤ => ℝ) 2 := ⟨g, hg⟩
    have hG : ‖GG‖ ≤ C * (‖F1‖ + ‖F2‖) := by
      calc
        _ ≤ ‖Y‖ := lp.norm_mono (by positivity) (fun k => (hdom k).trans (Real.le_norm_self _))
        _ = C * ‖F1 + F2‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hC]
        _ ≤ _ := mul_le_mul_of_nonneg_left (norm_add_le _ _) (by positivity)
    have hnorm (x : lp (fun _ : ℤ × ℤ => ℝ) 2) :
        ‖x‖ = Real.sqrt (∑' k, (x k)^2) := by
      have hh : ‖x‖^2 = ∑' k, (x k)^2 := by
        simpa only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs] using
          lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal) x
      rw [← hh, Real.sqrt_sq (norm_nonneg _)]
    have hGn : ‖GG‖ = Real.sqrt (∑' k, (weight k * weight k^α)^2 * ‖D5.S3.FluidDynamics.Fourier.WeightedTensorConvolution.convolution aa bb k‖^2) := by
      rw [hnorm]
      congr 1
      apply tsum_congr
      intro k
      change ((weight k * weight k^α) * ‖D5.S3.FluidDynamics.Fourier.WeightedTensorConvolution.convolution aa bb k‖)^2 = _
      ring
    have hF1n : ‖F1‖ = Real.sqrt (∑' k, weight k^2 * ‖D5.S3.FluidDynamics.Fourier.WeightedTensorConvolution.convolution A5 B0 k‖^2) := by
      rw [hnorm]; simp only [F1, f1, mul_pow]
    have hF2n : ‖F2‖ = Real.sqrt (∑' k, weight k^2 * ‖D5.S3.FluidDynamics.Fourier.WeightedTensorConvolution.convolution A0 B5 k‖^2) := by
      rw [hnorm]; simp only [F2, f2, mul_pow]
    have hEa : Real.sqrt (∑' k, weight k^2 * ‖aa k‖^2) ≤
        Real.sqrt (∑' k, (weight k * weight k^α)^2 * ‖aa k‖^2) :=
      Real.sqrt_le_sqrt (ha2.tsum_le_tsum (hdown aa) haa)
    have hEb : Real.sqrt (∑' k, weight k^2 * ‖bb k‖^2) ≤
        Real.sqrt (∑' k, (weight k * weight k^α)^2 * ‖bb k‖^2) :=
      Real.sqrt_le_sqrt (hb2.tsum_le_tsum (hdown bb) hbb)
    have hF1 : ‖F1‖ ≤ 16 * Real.sqrt (∑' k, (weight k * weight k^α)^2 * ‖aa k‖^2) *
        Real.sqrt (∑' k, (weight k * weight k^α)^2 * ‖bb k‖^2) := by
      rw [hF1n]
      have hh := hm1.2.2
      simp only [hA5, hB0] at hh
      exact hh.trans (mul_le_mul_of_nonneg_left hEb (by positivity))
    have hF2 : ‖F2‖ ≤ 16 * Real.sqrt (∑' k, (weight k * weight k^α)^2 * ‖aa k‖^2) *
        Real.sqrt (∑' k, (weight k * weight k^α)^2 * ‖bb k‖^2) := by
      rw [hF2n]
      have hh := hm2.2.2
      simp only [hA0, hB5] at hh
      exact hh.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hEa (by positivity)) (Real.sqrt_nonneg _))
    refine ⟨hab.1, ?_, ?_⟩
    · have hh : Summable (fun k => (g k)^2) := by
        simpa only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs] using
          hg.summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
      exact hh.congr (fun k => by dsimp [g]; ring)
    · rw [← hGn]
      calc
        _ ≤ C * (‖F1‖ + ‖F2‖) := hG
        _ ≤ C * (16 * Real.sqrt (∑' k, (weight k * weight k^α)^2 * ‖aa k‖^2) *
          Real.sqrt (∑' k, (weight k * weight k^α)^2 * ‖bb k‖^2) +
          16 * Real.sqrt (∑' k, (weight k * weight k^α)^2 * ‖aa k‖^2) *
          Real.sqrt (∑' k, (weight k * weight k^α)^2 * ‖bb k‖^2)) :=
            mul_le_mul_of_nonneg_left (add_le_add hF1 hF2) hC
        _ = _ := by ring
  have hGeneralQB (α : ℝ) (hα : 0 ≤ α) :
      ∃ qb : H →L[ℝ] H →L[ℝ] G,
      (∀ x y k, qb x y k = (weight k * weight k^α) •
        convolution (fun l => (weight l * weight l^α)⁻¹ • x l)
          (fun l => (weight l * weight l^α)⁻¹ • y l) k) ∧
      (∀ x y, ‖qb x y‖ ≤ (32 * (4:ℝ)^α) * ‖x‖ * ‖y‖) := by
    let Wg : K → ℝ := fun k => weight k * weight k^α
    have hWg (k : K) : 0 < Wg k := by
      have hw : 0 < weight k := by rw [hweight]; exact hW k
      exact mul_pos hw (Real.rpow_pos_of_pos hw α)
    let d : H → K → V := fun x k => (Wg k)⁻¹ • x k
    have hdenergy (x : H) :
        Summable (fun k : K => Wg k ^ 2 * ‖d x k‖ ^ 2) ∧
        Real.sqrt (∑' k : K, Wg k ^ 2 * ‖d x k‖ ^ 2) = ‖x‖ := by
      have he (k : K) : Wg k ^ 2 * ‖d x k‖ ^ 2 = ‖x k‖ ^ 2 := by
        have hw : 0 < Wg k := hWg k
        dsimp [d]
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hw)]
        field_simp [hw.ne']
      simp_rw [he]
      refine ⟨?_, ?_⟩
      · simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
          (lp.hasSum_norm (by norm_num : 0 < (2 : ℝ≥0∞).toReal) x).summable
      · have hn : ‖x‖ ^ 2 = ∑' k : K, ‖x k‖ ^ 2 := by
          simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
            lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal) x
        rw [← hn, Real.sqrt_sq (norm_nonneg _)]
    have hp (x y : H) := hProduct α hα (d x) (d y)
      (by simpa only [Wg] using (hdenergy x).1) (by simpa only [Wg] using (hdenergy y).1)
    let Q (x y : H) : G := ⟨fun k => Wg k • D5.S3.FluidDynamics.Fourier.WeightedTensorConvolution.convolution (d x) (d y) k,
      memℓp_gen (by
        simpa only [Wg, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
          ENNReal.toReal_ofNat, Real.rpow_two] using (hp x y).2.1)⟩
    have hQnorm (x y : H) : ‖Q x y‖ ≤ (32 * (4:ℝ)^α) * ‖x‖ * ‖y‖ := by
      have hn : ‖Q x y‖ ^ 2 =
          ∑' k : K, Wg k ^ 2 * ‖D5.S3.FluidDynamics.Fourier.WeightedTensorConvolution.convolution (d x) (d y) k‖ ^ 2 := by
        simpa only [Q, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
          ENNReal.toReal_ofNat, Real.rpow_two] using
          lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal) (Q x y)
      have heq : ‖Q x y‖ = Real.sqrt
          (∑' k : K, Wg k ^ 2 * ‖D5.S3.FluidDynamics.Fourier.WeightedTensorConvolution.convolution (d x) (d y) k‖ ^ 2) := by
        rw [← hn, Real.sqrt_sq (norm_nonneg _)]
      rw [heq]
      have hb := (hp x y).2.2
      rw [(hdenergy x).2, (hdenergy y).2] at hb
      exact hb
    have hdadd (x y : H) (k : K) : d (x+y) k = d x k + d y k := by
      simp [d, smul_add]
    have hdsmul (c : ℝ) (x : H) (k : K) : d (c • x) k = c • d x k := by
      change (Wg k)⁻¹ • (c • x k) = c • ((Wg k)⁻¹ • x k)
      exact smul_comm _ _ _
    have hol (x y z : V) : outer (x+y) z = outer x z + outer y z := by
      ext ij
      change (x ij.1 + y ij.1) * z ij.2 = x ij.1 * z ij.2 + y ij.1 * z ij.2
      ring
    have hor (x y z : V) : outer x (y+z) = outer x y + outer x z := by
      ext ij
      change x ij.1 * (y ij.2 + z ij.2) = x ij.1 * y ij.2 + x ij.1 * z ij.2
      ring
    have hosl (c : ℝ) (x y : V) : outer (c • x) y = c • outer x y := by
      ext ij
      change ((c:ℂ) * x ij.1) * y ij.2 = (c:ℂ) * (x ij.1 * y ij.2)
      ring
    have hosr (c : ℝ) (x y : V) : outer x (c • y) = c • outer x y := by
      ext ij
      change x ij.1 * ((c:ℂ) * y ij.2) = (c:ℂ) * (x ij.1 * y ij.2)
      ring
    have hQal (x y z : H) : Q (x+y) z = Q x z + Q y z := by
      apply lp.ext
      funext k
      change Wg k • D5.S3.FluidDynamics.Fourier.WeightedTensorConvolution.convolution (d (x+y)) (d z) k =
        Wg k • D5.S3.FluidDynamics.Fourier.WeightedTensorConvolution.convolution (d x) (d z) k + Wg k • D5.S3.FluidDynamics.Fourier.WeightedTensorConvolution.convolution (d y) (d z) k
      rw [← smul_add]
      congr 1
      simp only [D5.S3.FluidDynamics.Fourier.WeightedTensorConvolution.convolution, hdadd, hol]
      exact ((hp x z).1 k).of_norm.tsum_add ((hp y z).1 k).of_norm
    have hQar (x y z : H) : Q x (y+z) = Q x y + Q x z := by
      apply lp.ext
      funext k
      change Wg k • D5.S3.FluidDynamics.Fourier.WeightedTensorConvolution.convolution (d x) (d (y+z)) k =
        Wg k • D5.S3.FluidDynamics.Fourier.WeightedTensorConvolution.convolution (d x) (d y) k + Wg k • D5.S3.FluidDynamics.Fourier.WeightedTensorConvolution.convolution (d x) (d z) k
      rw [← smul_add]
      congr 1
      simp only [D5.S3.FluidDynamics.Fourier.WeightedTensorConvolution.convolution, hdadd, hor]
      exact ((hp x y).1 k).of_norm.tsum_add ((hp x z).1 k).of_norm
    have hQsl (c : ℝ) (x y : H) : Q (c • x) y = c • Q x y := by
      apply lp.ext
      funext k
      change Wg k • D5.S3.FluidDynamics.Fourier.WeightedTensorConvolution.convolution (d (c • x)) (d y) k =
        c • (Wg k • D5.S3.FluidDynamics.Fourier.WeightedTensorConvolution.convolution (d x) (d y) k)
      simp only [D5.S3.FluidDynamics.Fourier.WeightedTensorConvolution.convolution, hdsmul, hosl, tsum_const_smul'', smul_comm (Wg k) c]
    have hQsr (c : ℝ) (x y : H) : Q x (c • y) = c • Q x y := by
      apply lp.ext
      funext k
      change Wg k • D5.S3.FluidDynamics.Fourier.WeightedTensorConvolution.convolution (d x) (d (c • y)) k =
        c • (Wg k • D5.S3.FluidDynamics.Fourier.WeightedTensorConvolution.convolution (d x) (d y) k)
      simp only [D5.S3.FluidDynamics.Fourier.WeightedTensorConvolution.convolution, hdsmul, hosr, tsum_const_smul'', smul_comm (Wg k) c]
    let QL : H →ₗ[ℝ] H →ₗ[ℝ] G := LinearMap.mk₂ ℝ Q hQal hQsl hQar
      (fun c x y => hQsr c x y)
    let QB : H →L[ℝ] H →L[ℝ] G := QL.mkContinuous₂ (32 * (4:ℝ)^α) hQnorm
    refine ⟨QB, ?_, hQnorm⟩
    intro x y k
    rfl
  -- Exponent zero supplies the same base tensor path used in the scalar equation.
  obtain ⟨QB, hQBcoeff, _⟩ := hGeneralQB 0 (le_refl 0)
  let q : ℝ → G := fun t => QB (x₂ t) (x₂ t)
  have hqcont : ContinuousOn q (Icc 0 τ) :=
    (QB.continuous.comp_continuousOn hx).clm_apply hx
  have hqcoeff (t : ℝ) (k : K) : q t k = (1+ρ k) • D5.S3.FluidDynamics.Fourier.WeightedTensorConvolution.convolution (a t) (a t) k := by
    change QB (x₂ t) (x₂ t) k = _
    rw [hQBcoeff]
    simp only [Real.rpow_zero, mul_one, hweight, a]
    rfl
  have hcontract (k : K) (Z : TV) :
      ‖(WithLp.toLp 2 (fun i : Fin 2 => ∑ j : Fin 2, κ k j * Z (j,i)) : V)‖ ≤
        Real.sqrt (ρ k) * ‖Z‖ := by
    let row := fun i : Fin 2 =>
      (WithLp.toLp 2 (fun j : Fin 2 => Z (j,i)) : V)
    have hrow (i) : ‖∑ j : Fin 2, κ k j * Z (j,i)‖ ≤ ‖κ k‖ * ‖row i‖ := by
      simpa [V, TV, PiLp.inner_apply, κ, row, mul_comm] using
        norm_inner_le_norm (𝕜 := ℂ) (κ k) (row i)
    have hk : ‖κ k‖ ^ 2 = ρ k := by
      simp [V, EuclideanSpace.norm_sq_eq, κ, ρ, Complex.norm_intCast, sq_abs, Fin.sum_univ_two]
    have hrows : ∑ i : Fin 2, ‖row i‖ ^ 2 = ‖Z‖ ^ 2 := by
      simp only [V, TV, EuclideanSpace.norm_sq_eq, row, PiLp.toLp_apply, Fintype.sum_prod_type]
      exact Finset.sum_comm
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
    rw [mul_pow, Real.sq_sqrt (hρ k)]
    calc
      _ = ∑ i : Fin 2, ‖∑ j : Fin 2, κ k j * Z (j,i)‖ ^ 2 :=
        EuclideanSpace.norm_sq_eq _
      _ ≤ ∑ i : Fin 2, (‖κ k‖ * ‖row i‖) ^ 2 :=
        Finset.sum_le_sum (fun i _ => pow_le_pow_left₀ (norm_nonneg _) (hrow i) 2)
      _ = _ := by simp only [mul_pow, ← Finset.mul_sum, hk, hrows]
  let Dlin (k : K) : TV →ₗ[ℂ] V :=
    { toFun := fun Z => WithLp.toLp 2 (fun i : Fin 2 => ∑ j : Fin 2, κ k j * Z (j,i))
      map_add' := by
        intro Z W
        ext i
        change (∑ j : Fin 2, κ k j * (Z (j,i) + W (j,i))) =
          (∑ j : Fin 2, κ k j * Z (j,i)) + ∑ j : Fin 2, κ k j * W (j,i)
        simp [mul_add, Finset.sum_add_distrib]
      map_smul' := by
        intro z Z
        ext i
        change (∑ j : Fin 2, κ k j * (z * Z (j,i))) =
          z * ∑ j : Fin 2, κ k j * Z (j,i)
        simp [← Finset.mul_sum, mul_left_comm] }
  let DC (k : K) : TV →L[ℂ] V := (Dlin k).mkContinuous (Real.sqrt (ρ k)) (hcontract k)
  let DCp (k : K) : TV →L[ℂ] V := Complex.I • (P k).comp (DC k)
  have hDC (k : K) (Z : TV) : ‖DCp k Z‖ ≤ Real.sqrt (ρ k) * ‖Z‖ := by
    change ‖Complex.I • P k (DC k Z)‖ ≤ _
    rw [norm_smul, Complex.norm_I, one_mul]
    exact ((ℂ ∙ κ k)ᗮ.norm_starProjection_apply_le _).trans (hcontract k Z)
  let RK (r : ℝ) (k : K) : TV →L[ℂ] V :=
    ((1+ρ k)^(1/4:ℝ) * Real.exp (-ν*r*ρ k)) • DCp k
  have hRK (r : ℝ) (hr : 0 < r) (k : K) : ‖RK r k‖ ≤ c r := by
    apply ContinuousLinearMap.opNorm_le_bound _ (hc0 r hr.le)
    intro Z
    change ‖(((1+ρ k)^(1/4:ℝ) * Real.exp (-ν*r*ρ k)) : ℝ) • DCp k Z‖ ≤ _
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (mul_pos
      (Real.rpow_pos_of_pos (hW k) _) (Real.exp_pos _))]
    calc
      _ ≤ ((1+ρ k)^(1/4:ℝ) * Real.exp (-ν*r*ρ k)) * (Real.sqrt (ρ k) * ‖Z‖) :=
        mul_le_mul_of_nonneg_left (hDC k Z) (by positivity)
      _ ≤ c r * ‖Z‖ := by
        nlinarith [mul_le_mul_of_nonneg_right (hMultiplier r hr k) (norm_nonneg Z)]
  let R : ℝ → G →L[ℂ] H := fun r => if hr : 0 < r then
    lp.mapCLM 2 (RK r) (hc0 r hr.le) (hRK r hr) else 0
  have hRcoeff (r : ℝ) (hr : 0 < r) (Z : G) (k : K) :
      R r Z k = ((1+ρ k)^(1/4:ℝ) * Real.exp (-ν*r*ρ k)) • DCp k (Z k) := by
    simp only [R, dif_pos hr]
    rfl
  have hRbound (r : ℝ) (hr : 0 < r) (Z : G) : ‖R r Z‖ ≤ c r * ‖Z‖ := by
    apply (R r).le_of_opNorm_le
    simp only [R, dif_pos hr]
    exact lp.norm_mapCLM_le 2 (RK r) (hc0 r hr.le) (hRK r hr)
  have hDConvolution (t : ℝ) (k : K) :
      DCp k (D5.S3.FluidDynamics.Fourier.WeightedTensorConvolution.convolution (a t) (a t) k) =
        N (a t) (a t) k := by
    have hs := ((weighted_tensor_convolution (a t) (a t)
      (henergy t).1 (henergy t).1).1 k).of_norm
    have hterm (l : K) : DC k (outer (a t l) (a t (k-l))) =
        (∑ j : Fin 2, κ k j * a t l j) • a t (k-l) := by
      ext i
      change (∑ j : Fin 2, κ k j * (a t l j * a t (k-l) i)) =
        (∑ j : Fin 2, κ k j * a t l j) * a t (k-l) i
      simp only [Fin.sum_univ_two]
      ring
    have he := ((DC k).hasSum hs.hasSum).tsum_eq.symm
    change Complex.I • P k (DC k _) = Complex.I • P k _
    congr 2
    simpa only [D5.S3.FluidDynamics.Fourier.WeightedTensorConvolution.convolution, Function.comp_def, hterm] using he
  let qC : C(Icc (0:ℝ) τ, G) := ⟨fun t => q t,
    continuousOn_iff_continuous_domRestrict.mp hqcont⟩
  let qe : ℝ → G := fun t => qC (projIcc 0 τ hτ.le t)
  have hqe : Continuous qe := qC.continuous.comp continuous_projIcc
  have hqeEq (t : ℝ) (ht : t ∈ Icc 0 τ) : qe t = q t := by
    dsimp [qe]
    rw [projIcc_of_mem _ ht]
    rfl
  let σ : ℕ → ℝ := fun n => 1 + (n:ℝ)/4
  have hInitial (n : ℕ) : Memℓp (fun k : K => (1+ρ k)^(σ n) • a 0 k) 2 := by
    apply memℓp_gen
    have hdom (k : K) : ‖(1+ρ k)^(σ n) • a 0 k‖^2 ≤ ‖w (n+2) k • a 0 k‖^2 := by
      apply pow_le_pow_left₀ (norm_nonneg _) _ 2
      simp only [w, norm_smul, Real.norm_eq_abs,
        abs_of_pos (Real.rpow_pos_of_pos (hW k) _)]
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      apply Real.rpow_le_rpow_of_exponent_le (by linarith [hρ k])
      dsimp [σ]
      push_cast
      nlinarith [Nat.cast_nonneg (α:=ℝ) n]
    have hs := (hinit (n+2)).of_nonneg_of_le (fun k => sq_nonneg _) hdom
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using hs
  let z : ℕ → H := fun n => ⟨fun k => (1+ρ k)^(σ n) • a 0 k, hInitial n⟩
  have hHeat (z₀ : H) : ∃ E : ℝ → H,
      Continuous E ∧ ∀ t ∈ Icc 0 τ, ∀ k,
        E t k = Real.exp (-ν*t*ρ k) • z₀ k := by
    let e : ℝ → K → ℝ := fun t k => Real.exp (-ν * max 0 t * ρ k)
    have he (t : ℝ) (k : K) : 0 < e t k ∧ e t k ≤ 1 := by
      refine ⟨Real.exp_pos _, Real.exp_le_one_iff.mpr ?_⟩
      have hm : 0 ≤ max 0 t := le_max_left _ _
      nlinarith [mul_nonneg (mul_nonneg hν.le hm) (hρ k)]
    have hnorm (t : ℝ) (k : K) : ‖e t k • z₀ k‖ ≤ ‖z₀ k‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (he t k).1]
      exact mul_le_of_le_one_left (norm_nonneg _) (he t k).2
    let E : ℝ → H := fun t => ⟨fun k => e t k • z₀ k, (lp.memℓp z₀).mono' (hnorm t)⟩
    have hEc (k : K) : Continuous (fun t => E t k) := by
      change Continuous (fun t : ℝ => Real.exp (-ν * max 0 t * ρ k) • z₀ k)
      fun_prop
    have hcont : Continuous E := by
      apply continuous_iff_continuousAt.mpr
      intro t₀
      apply tendsto_iff_norm_sub_tendsto_zero.mpr
      have hs : Summable (fun k : K => 4 * ‖z₀ k‖^2) := by
        have hz : Summable (fun k : K => ‖z₀ k‖^2) := by
          simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
            (lp.hasSum_norm (by norm_num : 0 < (2:ℝ≥0∞).toReal) z₀).summable
        exact hz.mul_left 4
      have hl (k : K) : Tendsto (fun t => ‖E t k - E t₀ k‖^2) (𝓝 t₀) (𝓝 (0:ℝ)) := by
        convert (((hEc k).sub (continuous_const : Continuous (fun _ : ℝ => E t₀ k))).norm.pow 2).tendsto t₀ using 1 <;> simp <;> rfl
      have hb (t : ℝ) (k : K) : ‖‖E t k - E t₀ k‖^2‖ ≤ 4 * ‖z₀ k‖^2 := by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        have h : ‖E t k - E t₀ k‖ ≤ 2 * ‖z₀ k‖ := by
          calc
            _ ≤ ‖E t k‖ + ‖E t₀ k‖ := norm_sub_le _ _
            _ ≤ ‖z₀ k‖ + ‖z₀ k‖ := add_le_add (hnorm t k) (hnorm t₀ k)
            _ = _ := by ring
        nlinarith [sq_nonneg ‖E t k - E t₀ k‖, norm_nonneg (z₀ k), norm_nonneg (E t k - E t₀ k)]
      have hh := tendsto_tsum_of_dominated_convergence hs hl (Filter.Eventually.of_forall hb)
      have heq (t : ℝ) : Real.sqrt (∑' k : K, ‖E t k - E t₀ k‖^2) = ‖E t - E t₀‖ := by
        have hp : ‖E t - E t₀‖^2 = ∑' k : K, ‖E t k - E t₀ k‖^2 := by
          simpa only [H, ENNReal.toReal_ofNat, Real.rpow_two, lp.coeFn_sub, Pi.sub_apply] using
            lp.norm_rpow_eq_tsum (by norm_num : 0 < (2:ℝ≥0∞).toReal) (E t - E t₀)
        rw [← hp, Real.sqrt_sq (norm_nonneg _)]
      have hh' := Real.continuous_sqrt.continuousAt.tendsto.comp hh
      simpa only [Function.comp_def, tsum_zero, Real.sqrt_zero, heq] using hh'
    refine ⟨E, hcont, ?_⟩
    intro t ht k
    change Real.exp (-ν * max 0 t * ρ k) • z₀ k = _
    rw [max_eq_right ht.1]
  choose E hEc hEf using fun n => hHeat (z n)
  have hDuhamel (s : ℝ) (q : ℝ → G) (Cq : ℝ) (hCq : 0 ≤ Cq)
      (hqcont : ContinuousOn q (Icc 0 τ))
      (hqbound : ∀ t ∈ Icc 0 τ, ‖q t‖ ≤ Cq)
      (hqcoeff : ∀ t ∈ Icc 0 τ, ∀ k,
        q t k = (1+ρ k)^s • convolution (a t) (a t) k) :
      ∃ Dn : ℝ → H, ContinuousOn Dn (Icc 0 τ) ∧
        ∀ t ∈ Icc 0 τ, ∀ k, Dn t k = (1+ρ k)^(s+1/4) •
          (∫ u in (0:ℝ)..t, Real.exp (-ν*(t-u)*ρ k) • N (a u) (a u) k) := by
    have hRliteral (r : ℝ) (hr : 0 < r) (t : ℝ) (ht : t ∈ Icc 0 τ) (k : K) :
        R r (q t) k = (1+ρ k)^(s+1/4) •
          (Real.exp (-ν*r*ρ k) • N (a t) (a t) k) := by
      rw [hRcoeff r hr, hqcoeff t ht]
      rw [show DCp k ((1+ρ k)^s • convolution (a t) (a t) k) =
        (1+ρ k)^s • DCp k (convolution (a t) (a t) k)
        from (DCp k).map_smul_of_tower ((1+ρ k)^s) _, hDConvolution,
        smul_smul, smul_smul, Real.rpow_add (hW k) s (1/4:ℝ)]
      congr 1
      ring
    let qC : C(Icc (0:ℝ) τ, G) := ⟨fun t => q t,
      continuousOn_iff_continuous_domRestrict.mp hqcont⟩
    let qe : ℝ → G := fun t => qC (projIcc 0 τ hτ.le t)
    have hqe : Continuous qe := qC.continuous.comp continuous_projIcc
    have hqeB (t : ℝ) : ‖qe t‖ ≤ Cq := hqbound _ (projIcc 0 τ hτ.le t).property
    have hqeEq (t : ℝ) (ht : t ∈ Icc 0 τ) : qe t = q t := by
      dsimp [qe]
      rw [projIcc_of_mem _ ht]
      rfl
    have hRm (t : ℝ) : StronglyMeasurable (fun r => R r (qe (t-r))) := by
      let g : ℝ → H := fun r => R r (qe (t-r))
      have hgk (k : K) : StronglyMeasurable (fun r => g r k) := by
        let v : ℝ → V := fun r =>
          ((1+ρ k)^(1/4:ℝ) * Real.exp (-ν*r*ρ k)) • DCp k (qe (t-r) k)
        have hv : Continuous v := by
          have he : Continuous (fun r : ℝ => qe (t-r) k) :=
            (lp.evalCLM ℝ (fun _ : K => TV) 2 k).continuous.comp
              (hqe.comp (continuous_const.sub continuous_id))
          exact (continuous_const.mul (Real.continuous_exp.comp (by fun_prop))).smul
            ((DCp k).continuous.comp he)
        convert hv.stronglyMeasurable.indicator (measurableSet_Ioi (a := (0:ℝ))) using 1
        funext r
        by_cases hr : 0 < r
        · simpa only [Set.indicator, mem_Ioi, hr, ite_true, v, g] using hRcoeff r hr (qe (t-r)) k
        · simp [g, R, hr, Set.indicator_of_notMem hr]
      have hf (s : Finset K) : StronglyMeasurable
          (fun r => ∑ k ∈ s, lp.single (E := fun _ : K => V) 2 k (g r k)) := by
        apply Finset.stronglyMeasurable_fun_sum
        intro k hk
        exact (lp.singleContinuousLinearMap ℝ (fun _ : K => V) 2 k).continuous.comp_stronglyMeasurable
          (hgk k)
      exact stronglyMeasurable_of_tendsto (atTop : Filter (Finset K)) hf
        (tendsto_pi_nhds.mpr (fun r => lp.hasSum_single (by norm_num) (g r)))
    let F : ℝ → ℝ → H := fun t r =>
      (Iic t).indicator (fun r => R r (qe (t-r))) r
    have hFm (t : ℝ) : AEStronglyMeasurable (F t) (volume.restrict (Ioc 0 τ)) :=
      ((hRm t).indicator measurableSet_Iic).aestronglyMeasurable
    have hFB (t r : ℝ) (hr : r ∈ Ioc 0 τ) : ‖F t r‖ ≤ c r * (Cq) := by
      dsimp [F]
      by_cases hrt : r ≤ t
      · simp only [Set.indicator, mem_Iic, hrt, ite_true]
        exact (hRbound r hr.1 _).trans (mul_le_mul_of_nonneg_left (hqeB _) (hc0 r hr.1.le))
      · simp only [Set.indicator, mem_Iic, hrt, ite_false, norm_zero]
        exact mul_nonneg (hc0 r hr.1.le) (by positivity)
    have hcI : IntegrableOn c (Ioc 0 τ) volume :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hτ.le).mp hcInt
    have hFI (t : ℝ) : Integrable (F t) (volume.restrict (Ioc 0 τ)) := by
      apply (hcI.mul_const (Cq)).mono' (hFm t)
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
      exact hFB t r hr
    have hFt (t r : ℝ) (hr : r ≠ t) : ContinuousAt (fun s => F s r) t := by
      have hc : Continuous (fun s : ℝ => R r (qe (s-r))) :=
        (R r).continuous.comp (hqe.comp (continuous_id.sub continuous_const))
      rcases lt_or_gt_of_ne hr with hrt | htr
      · apply hc.continuousAt.congr_of_eventuallyEq
        filter_upwards [Ioi_mem_nhds hrt] with s hs
        have hs' : r ≤ s := le_of_lt hs
        simp only [F, Set.indicator, mem_Iic, hs', ite_true]
      · apply (continuousAt_const (y := (0:H))).congr_of_eventuallyEq
        filter_upwards [Iio_mem_nhds htr] with s hs
        have hs' : ¬ r ≤ s := not_le.mpr hs
        simp only [F, Set.indicator, mem_Iic, hs', ite_false]
    let D : ℝ → H := fun t => ∫ r in Ioc 0 τ, F t r
    have hDcont : Continuous D := by
      apply continuous_iff_continuousAt.mpr
      intro t
      apply continuousAt_of_dominated
        (Filter.Eventually.of_forall hFm)
        (Filter.Eventually.of_forall fun s => ?_) (hcI.mul_const (Cq))
      · have hn : ∀ᵐ r : ℝ ∂volume.restrict (Ioc 0 τ), r ≠ t :=
          ae_restrict_of_ae (by simp [ae_iff, measure_singleton])
        filter_upwards [hn] with r hr
        exact hFt t r hr
      · filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
        exact hFB s r hr
    have hDcoord (t : ℝ) (ht : t ∈ Icc 0 τ) (k : K) :
        D t k = (1+ρ k)^(s+1/4) •
          (∫ s in (0:ℝ)..t, Real.exp (-ν*(t-s)*ρ k) • N (a s) (a s) k) := by
      have hEv := (lp.evalCLM ℝ (fun _ : K => V) 2 k).integral_comp_comm (hFI t)
      change (lp.evalCLM ℝ (fun _ : K => V) 2 k) (∫ r in Ioc 0 τ, F t r) = _
      rw [← hEv]
      let g : ℝ → V := fun r => (1+ρ k)^(s+1/4) •
        (Real.exp (-ν*r*ρ k) • N (a (t-r)) (a (t-r)) k)
      calc
        _ = ∫ r in Ioc 0 τ, (Iic t).indicator g r := by
          apply setIntegral_congr_fun measurableSet_Ioc
          intro r hr
          by_cases hrt : r ≤ t
          · have htr : t-r ∈ Icc 0 τ := ⟨sub_nonneg.mpr hrt,
              (sub_le_self t hr.1.le).trans ht.2⟩
            change ((Iic t).indicator (fun r => R r (qe (t-r))) r) k = _
            simp only [Set.indicator, mem_Iic, hrt, ite_true]
            rw [hqeEq _ htr]
            exact hRliteral r hr.1 (t-r) htr k
          · change ((Iic t).indicator (fun r => R r (qe (t-r))) r) k = _
            simp only [Set.indicator, mem_Iic, hrt, ite_false]
            rfl
        _ = ∫ r in (0:ℝ)..t, g r := by
          rw [← intervalIntegral.integral_of_le hτ.le]
          exact intervalIntegral.integral_indicator ht
        _ = (1+ρ k)^(s+1/4) •
            (∫ r in (0:ℝ)..t, Real.exp (-ν*r*ρ k) • N (a (t-r)) (a (t-r)) k) := by
          exact intervalIntegral.integral_smul _ _
        _ = _ := by
          congr 1
          have hs := intervalIntegral.integral_comp_sub_left
            (fun s : ℝ => Real.exp (-ν*(t-s)*ρ k) • N (a s) (a s) k) (a:=0) (b:=t) t
          simpa only [sub_sub_cancel, sub_self, sub_zero] using hs
    exact ⟨D, hDcont.continuousOn, hDcoord⟩
  have hAllFractional : ∀ n : ℕ, ∃ v : ℝ → H,
      ContinuousOn v (Icc 0 τ) ∧
      ∀ t ∈ Icc 0 τ, ∀ k, v t k = (1+ρ k)^(σ n) • a t k := by
    intro n
    induction n with
    | zero =>
      refine ⟨x₂, hx, ?_⟩
      intro t ht k
      simp only [σ, Nat.cast_zero, zero_div, add_zero, Real.rpow_one, a,
        smul_smul, mul_inv_cancel₀ (hW k).ne', one_smul]
    | succ n ih =>
      obtain ⟨v, hv, hvc⟩ := ih
      obtain ⟨Bn₀, hBn₀⟩ := isCompact_Icc.exists_bound_of_continuousOn hv
      let Bn : ℝ := max Bn₀ 0
      have hbudget_n : ∀ t ∈ Icc 0 τ, ‖v t‖ ≤ Bn :=
        fun t ht => (hBn₀ t ht).trans (le_max_left _ _)
      have hα : 0 ≤ (n:ℝ)/4 := by positivity
      obtain ⟨Qn, hQnc, hQnb⟩ := hGeneralQB ((n:ℝ)/4) hα
      have hWn (k : K) : weight k * weight k^((n:ℝ)/4) = (1+ρ k)^(σ n) := by
        rw [hweight]
        simp only [σ, Real.rpow_add (hW k), Real.rpow_one]
      have hdec_n (t : ℝ) (ht : t ∈ Icc 0 τ) (k : K) :
          (weight k * weight k^((n:ℝ)/4))⁻¹ • v t k = a t k := by
        rw [hWn, hvc t ht, smul_smul,
          inv_mul_cancel₀ (Real.rpow_pos_of_pos (hW k) _).ne', one_smul]
      let qn : ℝ → G := fun t => Qn (v t) (v t)
      have hqnc : ContinuousOn qn (Icc 0 τ) :=
        (Qn.continuous.comp_continuousOn hv).clm_apply hv
      have hqncoeff : ∀ t ∈ Icc 0 τ, ∀ k,
          qn t k = (1+ρ k)^(σ n) • convolution (a t) (a t) k := by
        intro t ht k
        change Qn (v t) (v t) k = _
        rw [hQnc]
        simp only [hdec_n t ht]
        rw [hWn]
      let Cn : ℝ := 32 * (4:ℝ)^((n:ℝ)/4)
      have hCn : 0 ≤ Cn := by dsimp [Cn]; positivity
      have hqnb : ∀ t ∈ Icc 0 τ, ‖qn t‖ ≤ Cn * Bn^2 := by
        intro t ht
        calc
          _ ≤ Cn * ‖v t‖ * ‖v t‖ := hQnb _ _
          _ = Cn * ‖v t‖^2 := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (norm_nonneg _) (hbudget_n t ht) 2) hCn
      have hNextDuhamel : ∃ Dn : ℝ → H,
          ContinuousOn Dn (Icc 0 τ) ∧
          ∀ t ∈ Icc 0 τ, ∀ k,
            Dn t k = (1+ρ k)^(σ (n+1)) •
              (∫ s in (0:ℝ)..t, Real.exp (-ν*(t-s)*ρ k) • N (a s) (a s) k) := by
        have he : σ (n+1) = σ n + 1/4 := by dsimp [σ]; push_cast; ring
        rw [he]
        exact hDuhamel (σ n) qn (Cn * Bn^2) (mul_nonneg hCn (sq_nonneg _))
          hqnc hqnb hqncoeff
      obtain ⟨Dn, hDn, hDnc⟩ := hNextDuhamel
      refine ⟨fun t => E (n+1) t - Dn t, ((hEc (n+1)).continuousOn.sub hDn), ?_⟩
      intro t ht k
      change E (n+1) t k - Dn t k = _
      rw [hEf (n+1) t ht, hDnc t ht]
      change Real.exp (-ν*t*ρ k) • ((1+ρ k)^(σ (n+1)) • a 0 k) - _ = _
      rw [smul_comm (Real.exp (-ν*t*ρ k)) ((1+ρ k)^(σ (n+1))), ← smul_sub,
        ← (hmild t ht k).2]
  choose vg hvg hvgc using hAllFractional
  have hInv (k : K) : ‖(1+ρ k)⁻¹‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hW k))]
    exact (inv_le_one₀ (hW k)).mpr (by linarith [hρ k])
  let down : H →L[ℝ] H := lp.mapCLM 2
    (fun k => (1+ρ k)⁻¹ • ContinuousLinearMap.id ℝ V) (by norm_num : (0:ℝ) ≤ 1)
    (fun k => by
      apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
      intro x
      change ‖(1+ρ k)⁻¹ • x‖ ≤ 1 * ‖x‖
      rw [norm_smul, one_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (hInv k))
  have hdownc (x : H) (k : K) : down x k = (1+ρ k)⁻¹ • x k := rfl
  let U : ℕ → ℝ → H := fun m t => down (vg (2*m) t)
  have hUc (m : ℕ) : ContinuousOn (U m) (Icc 0 τ) := down.continuous.comp_continuousOn (hvg _)
  have hUcoeff (m : ℕ) (t : ℝ) (ht : t ∈ Icc 0 τ) (k : K) : U m t k = w m k • a t k := by
    change down (vg (2*m) t) k = _
    rw [hdownc, hvgc _ t ht, smul_smul]
    have he : σ (2*m) = 1 + (m:ℝ)/2 := by dsimp [σ]; push_cast; ring
    rw [he, Real.rpow_add (hW k), Real.rpow_one]
    rw [← mul_assoc, inv_mul_cancel₀ (hW k).ne', one_mul]
  have hwshift (m : ℕ) (k : K) : w (m+2) k = (1+ρ k) * w m k := by
    dsimp [w]
    have he : ((m+2:ℕ):ℝ)/2 = 1 + (m:ℝ)/2 := by push_cast; ring
    rw [he, Real.rpow_add (hW k), Real.rpow_one]
  have hwp (m : ℕ) (k : K) : 0 < w m k := Real.rpow_pos_of_pos (hW k) _
  have hdecU (m : ℕ) (t : ℝ) (ht : t ∈ Icc 0 τ) (k : K) : dec m (U m t) k = a t k := by
    dsimp [dec]
    rw [hUcoeff m t ht k, smul_smul, inv_mul_cancel₀ (hwp m k).ne', one_smul]
  let lm : K → V →L[ℝ] V := fun k => ((-ν*ρ k)/(1+ρ k)) • ContinuousLinearMap.id ℝ V
  have hlm (k : K) : ‖lm k‖ ≤ ν := by
    apply ContinuousLinearMap.opNorm_le_bound _ hν.le
    intro x
    change ‖((-ν*ρ k)/(1+ρ k)) • x‖ ≤ ν * ‖x‖
    rw [norm_smul, Real.norm_eq_abs]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    rw [abs_of_nonpos (by apply div_nonpos_of_nonpos_of_nonneg <;> nlinarith [hρ k])]
    rw [← neg_div, div_le_iff₀ (hW k)]
    nlinarith only [hν]
  let LL : H →L[ℝ] H := lp.mapCLM 2 lm hν.le hlm
  let L : ℕ → H →L[ℝ] H := fun _ => LL
  have hLc (m : ℕ) (x : H) (k : K) : L m x k = w m k • ((-ν*ρ k) • dec (m+2) x k) := by
    change ((-ν*ρ k)/(1+ρ k)) • x k = _
    dsimp [dec]
    rw [smul_smul, smul_smul, hwshift]
    congr 1
    field_simp [(hW k).ne', (hwp m k).ne']
  let tm : K → TV →L[ℝ] V := fun k => (1+ρ k)⁻¹ • (DCp k).restrictScalars ℝ
  have htm (k : K) : ‖tm k‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    intro x
    change ‖(1+ρ k)⁻¹ • DCp k x‖ ≤ 1 * ‖x‖
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hW k)), one_mul]
    calc
      _ ≤ (1+ρ k)⁻¹ * (Real.sqrt (ρ k) * ‖x‖) :=
        mul_le_mul_of_nonneg_left (hDC k x) (inv_nonneg.mpr (hW k).le)
      _ ≤ _ := by
        have hs : Real.sqrt (ρ k) ≤ 1+ρ k := by
          nlinarith [Real.sq_sqrt (hρ k), Real.sqrt_nonneg (ρ k)]
        have hi : (1+ρ k)⁻¹ * Real.sqrt (ρ k) ≤ 1 := by
          apply (inv_mul_le_iff₀ (hW k)).mpr
          simpa using hs
        nlinarith [mul_le_mul_of_nonneg_right hi (norm_nonneg x)]
  let TT : G →L[ℝ] H := lp.mapCLM 2 tm (by norm_num : (0:ℝ) ≤ 1) htm
  have hTTc (x : G) (k : K) : TT x k = (1+ρ k)⁻¹ • DCp k (x k) := rfl
  choose Qm hQmc hQmb using fun m : ℕ => hGeneralQB ((m:ℝ)/2) (by positivity)
  let B : ℕ → H →L[ℝ] H →L[ℝ] H := fun m =>
    ((ContinuousLinearMap.compL ℝ H G H) TT).comp (Qm m)
  have hBc (m : ℕ) (x y : H) (k : K) :
      B m x y k = w m k • N (dec (m+2) x) (dec (m+2) y) k := by
    have hwm (l : K) : weight l * weight l^((m:ℝ)/2) = w (m+2) l := by
      rw [hweight, hwshift]
    change TT (Qm m x y) k = _
    rw [hTTc, hQmc]
    simp only [hwm]
    change (1+ρ k)⁻¹ • DCp k (w (m+2) k • convolution (dec (m+2) x) (dec (m+2) y) k) = _
    rw [(DCp k).map_smul_of_tower, smul_smul, hwshift, ← mul_assoc,
      inv_mul_cancel₀ (hW k).ne', one_mul]
    congr 1
    have hdx (z : H) : Summable (fun l => weight l^2 * ‖dec (m+2) z l‖^2) := by
      have hs : Summable (fun l => (weight l * weight l^((m:ℝ)/2))^2 * ‖dec (m+2) z l‖^2) := by
        simp only [hwm]
        have he (l : K) : w (m+2) l^2 * ‖dec (m+2) z l‖^2 = ‖z l‖^2 := by
          dsimp [dec]
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hwp _ _))]
          field_simp [(hwp (m+2) l).ne']
        simp only [he]
        simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using (lp.hasSum_norm (by norm_num) z).summable
      apply hs.of_nonneg_of_le (fun l => by positivity)
      intro l
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      have hw1 : 1 ≤ weight l := by rw [hweight]; linarith [hρ l]
      have hp1 : 1 ≤ weight l^((m:ℝ)/2) := Real.one_le_rpow hw1 (by positivity)
      exact pow_le_pow_left₀ (by linarith : 0 ≤ weight l)
        (le_mul_of_one_le_right (by linarith) hp1) 2
    have hs := ((weighted_tensor_convolution _ _ (hdx x) (hdx y)).1 k).of_norm
    have hterm (l : K) : DC k (outer (dec (m+2) x l) (dec (m+2) y (k-l))) =
        (∑ j : Fin 2, κ k j * dec (m+2) x l j) • dec (m+2) y (k-l) := by
      ext i
      change (∑ j : Fin 2, κ k j * (dec (m+2) x l j * dec (m+2) y (k-l) i)) =
        (∑ j : Fin 2, κ k j * dec (m+2) x l j) * dec (m+2) y (k-l) i
      simp only [Fin.sum_univ_two]
      ring
    have he := ((DC k).hasSum hs.hasSum).tsum_eq.symm
    change Complex.I • P k (DC k _) = Complex.I • P k _
    congr 2
    simpa only [D5.S3.FluidDynamics.Fourier.WeightedTensorConvolution.convolution, Function.comp_def, hterm] using he
  let Fn : ℕ → ℝ → H := fun m t => L m (U (m+2) t) - B m (U (m+2) t) (U (m+2) t)
  have hFc (m : ℕ) : ContinuousOn (Fn m) (Icc 0 τ) :=
    ((L m).continuous.comp_continuousOn (hUc _)).sub
      (((B m).continuous.comp_continuousOn (hUc _)).clm_apply (hUc _))
  let FC (m : ℕ) : C(Icc (0:ℝ) τ, H) :=
    ⟨fun t => Fn m t, continuousOn_iff_continuous_domRestrict.mp (hFc m)⟩
  let Fe : ℕ → ℝ → H := fun m t => FC m (projIcc 0 τ hτ.le t)
  have hFe (m : ℕ) : Continuous (Fe m) := (FC m).continuous.comp continuous_projIcc
  have hFeq (m : ℕ) (t : ℝ) (ht : t ∈ Icc 0 τ) : Fe m t = Fn m t := by
    dsimp [Fe]
    rw [projIcc_of_mem _ ht]
    rfl
  have hFcoeff (m : ℕ) (t : ℝ) (ht : t ∈ Icc 0 τ) (k : K) :
      Fe m t k = w m k • ((-ν*ρ k) • a t k - N (a t) (a t) k) := by
    rw [hFeq m t ht]
    change L m (U (m+2) t) k - B m (U (m+2) t) (U (m+2) t) k = _
    rw [hLc m, hBc m]
    have hdu : dec (m+2) (U (m+2) t) = a t := funext (hdecU (m+2) t ht)
    rw [hdu, smul_sub]
  have hScalar (k : K) : ∃ y : ℝ → V,
      (∀ t ∈ Icc 0 τ, y t = a t k) ∧
      ∀ t ∈ Icc 0 τ, HasDerivAt y ((-ν*ρ k) • a t k - N (a t) (a t) k) t := by
    let nk : ℝ → V := fun t => (1+ρ k)⁻¹ • DCp k (qe t k)
    have hnk : Continuous nk := by
      exact (continuous_const : Continuous (fun _ : ℝ => (1+ρ k)⁻¹)).smul
        ((DCp k).continuous.comp ((lp.evalCLM ℝ (fun _ : K => TV) 2 k).continuous.comp hqe))
    have hnke (t : ℝ) (ht : t ∈ Icc 0 τ) : nk t = N (a t) (a t) k := by
      dsimp [nk]
      rw [hqeEq t ht, hqcoeff, (DCp k).map_smul_of_tower, hDConvolution,
        smul_smul, inv_mul_cancel₀ (hW k).ne', one_smul]
    let lam : ℝ := -ν * ρ k
    let ff : ℝ → V := fun t => Real.exp (-lam*t) • nk t
    have hff : Continuous ff := (Real.continuous_exp.comp (by fun_prop)).smul hnk
    let J : ℝ → V := fun t => ∫ u in (0:ℝ)..t, ff u
    have hJ (t : ℝ) : HasDerivAt J (ff t) t :=
      intervalIntegral.integral_hasDerivAt_right (hff.intervalIntegrable _ _)
        hff.aestronglyMeasurable.stronglyMeasurableAtFilter hff.continuousAt
    let y : ℝ → V := fun t => Real.exp (lam*t) • (a 0 k - J t)
    have hy (t : ℝ) : HasDerivAt y (lam • y t - nk t) t := by
      have hd := (((hasDerivAt_id t).const_mul lam).exp).smul
        ((hasDerivAt_const t (a 0 k)).sub (hJ t))
      have he : Real.exp (lam*t) * Real.exp (-lam*t) = 1 := by
        rw [← Real.exp_add]
        convert Real.exp_zero using 1 <;> ring
      apply hd.congr_deriv
      dsimp [y, ff]
      simp only [mul_one, zero_sub, smul_neg, smul_smul, he, one_smul] <;> module
    have hye (t : ℝ) (ht : t ∈ Icc 0 τ) : y t = a t k := by
      have hi : Real.exp (lam*t) • J t =
          ∫ u in (0:ℝ)..t, Real.exp (-ν*(t-u)*ρ k) • N (a u) (a u) k := by
        dsimp [J]
        rw [← intervalIntegral.integral_smul]
        apply intervalIntegral.integral_congr
        intro u hu
        have hu' : u ∈ Icc 0 τ := by
          rw [uIcc_of_le ht.1] at hu
          exact ⟨hu.1, hu.2.trans ht.2⟩
        dsimp [ff]
        rw [hnke u hu', smul_smul, ← Real.exp_add]
        congr 2
        dsimp [lam]
        ring
      dsimp [y]
      rw [smul_sub, hi]
      have he : lam*t = -ν*t*ρ k := by dsimp [lam]; ring
      rw [he]
      exact (hmild t ht k).2.symm
    refine ⟨y, hye, ?_⟩
    intro t ht
    simpa only [hye t ht, hnke t ht, lam] using hy t
  choose yy hyy hdy using hScalar
  let Z : ℕ → ℝ → H := fun m t => U m 0 + ∫ u in (0:ℝ)..t, Fe m u
  have hZd (m : ℕ) (t : ℝ) : HasDerivAt (Z m) (Fe m t) t := by
    have hd := (hasDerivAt_const t (U m 0)).add
      (intervalIntegral.integral_hasDerivAt_right ((hFe m).intervalIntegrable 0 t)
        (hFe m).aestronglyMeasurable.stronglyMeasurableAtFilter (hFe m).continuousAt)
    simp only [zero_add] at hd
    exact ⟨⟨hd.isLittleOTVS.exists_eventuallyLE_mul⟩⟩
  have hZU (m : ℕ) (t : ℝ) (ht : t ∈ Icc 0 τ) : Z m t = U m t := by
    apply lp.ext
    funext k
    have hder : ∀ u ∈ uIcc (0:ℝ) t,
        HasDerivAt (fun s => w m k • yy k s) (Fe m u k) u := by
      intro u hu
      have hu' : u ∈ Icc 0 τ := by
        rw [uIcc_of_le ht.1] at hu
        exact ⟨hu.1, hu.2.trans ht.2⟩
      rw [hFcoeff m u hu']
      exact (hdy k u hu').const_smul (w m k)
    have hEval : Continuous (fun u => Fe m u k) :=
      (lp.evalCLM ℝ (fun _ : K => V) 2 k).continuous.comp (hFe m)
    have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt hder (hEval.intervalIntegrable 0 t)
    have hc := (lp.evalCLM ℝ (fun _ : K => V) 2 k).intervalIntegral_comp_comm (μ := volume)
      ((hFe m).intervalIntegrable 0 t)
    change U m 0 k + (lp.evalCLM ℝ (fun _ : K => V) 2 k) (∫ u in (0:ℝ)..t, Fe m u) = _
    rw [← hc]
    change U m 0 k + (∫ u in (0:ℝ)..t, Fe m u k) = _
    rw [hi, hyy k t ht, hyy k 0 ⟨le_rfl, hτ.le⟩,
      hUcoeff m 0 ⟨le_rfl, hτ.le⟩, hUcoeff m t ht]
    abel
  refine ⟨U, L, B, hUcoeff, hUc, hLc, hBc, ?_⟩
  intro m t ht
  have hd := (hZd m t).hasDerivWithinAt (s := Icc 0 τ)
  rw [hFeq m t ht] at hd
  exact hd.congr_of_mem (fun s hs => (hZU m s hs).symm) ht

end D5.S3.FluidDynamics.Fourier.MildPathRegularity
