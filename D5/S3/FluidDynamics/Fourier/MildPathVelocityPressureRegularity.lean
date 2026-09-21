/- GID: D5/S3/FluidDynamics/Fourier/MildPathVelocityPressureRegularity
   generality: G
   mirror-B: D5/B/S3/FluidDynamics/Fourier/MildPathVelocityPressureRegularity
   mirror-E: none(waiver:universal-analytic-estimate)
   anchors: []
   utility: none
   digest: The original mild Fourier path has jointly smooth velocity and pressure reconstructions on the full closed interval. -/

/-
SPDX-License-Identifier: Apache-2.0
The velocity and pressure maps use the original coefficient path, full lattice, and
closed interval. The pressure coefficient is represented with its zero branch and
negative Fourier multiplier.
-/

import Mathlib
import D5.S3.FluidDynamics.Fourier.WeightedTensorConvolution
import D5.S3.FluidDynamics.Fourier.MildPathRegularity
import D5.S3.FluidDynamics.Fourier.JointFourierSynthesis
open scoped BigOperators ENNReal ContDiff
open Set MeasureTheory Filter Topology
open D5.S3.FluidDynamics.Fourier.WeightedTensorConvolution
open D5.S3.FluidDynamics.Fourier.JointFourierSynthesis
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace D5.S3.FluidDynamics.Fourier.MildPathVelocityPressureRegularity

theorem mild_path_velocity_pressure_contdiff : (∀ (ν τ : ℝ), 0 < ν → 0 < τ →
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
  let character : K → (Fin 2 → ℝ) → ℂ := fun k x =>
    Complex.exp (Complex.I * ((k.1 : ℝ) * x 0 + (k.2 : ℝ) * x 1))
  let pc : ℝ → K → ℂ := fun t k => if k = 0 then 0 else
    -(∑ i : Fin 2, ∑ j : Fin 2, κ k i * κ k j *
      ∑' l : K, a t l i * a t (k-l) j) / (ρ k : ℂ)
  let u : ℝ × (Fin 2 → ℝ) → (Fin 2 → ℝ) := fun z i =>
    (∑' k : K, character k z.2 * a z.1 k i).re
  let p : ℝ × (Fin 2 → ℝ) → ℝ := fun z =>
    (∑' k : K, character k z.2 * pc z.1 k).re
  ContDiffOn ℝ ∞ u ((Icc 0 τ) ×ˢ (Set.univ : Set (Fin 2 → ℝ))) ∧
  ContDiffOn ℝ ∞ p ((Icc 0 τ) ×ˢ (Set.univ : Set (Fin 2 → ℝ))) : Prop) := by
  classical
  intro ν τ hν hτ K V H ρ κ P w dec N x₂ a hx hgeom hinit hmild
  intro character pc u p
  obtain ⟨U, L, B, hUc, hUcont, hLc, hBc, hUd⟩ :=
    D5.S3.FluidDynamics.Fourier.MildPathRegularity.all_grade_regularity_of_mild_path
      ν τ hν hτ x₂ hx hgeom hinit hmild
  have hCoeff : (∀ n : ℕ,
  let K := ℤ × ℤ
  let V := EuclideanSpace ℂ (Fin 2)
  let H := lp (fun _ : K => V) 2
  let ρ : K → ℝ := fun k => (k.1 : ℝ)^2 + (k.2 : ℝ)^2
  let κ : K → Fin 2 → ℂ := fun k i => (![k.1, k.2] i : ℂ)
  let W : K → ℝ := fun k => (1 + ρ k) ^ (((n+2 : ℕ) : ℝ) / 2)
  let dec : H → K → V := fun a k => (W k)⁻¹ • a k
  let pc : H → H → K → ℂ := fun a b k => if k = 0 then 0 else
    -(∑ i : Fin 2, ∑ j : Fin 2, κ k i * κ k j *
      ∑' l : K, dec a l i * dec b (k-l) j) / (ρ k : ℂ)
  ∃ B : H →L[ℝ] H →L[ℝ] H, ∀ a b k,
    B a b k = W k • (WithLp.toLp 2 (![pc a b k, 0]) : V) : Prop) := by
    classical
    intro n K V H ρ κ W dec pc
    let TV := EuclideanSpace ℂ (Fin 2 × Fin 2)
    let G := lp (fun _ : K => TV) 2
    have hρ (k : K) : 0 ≤ ρ k := by dsimp [ρ]; positivity
    have hW (k : K) : 0 < 1 + ρ k := by positivity
    have hweight (k : K) : weight k = 1 + ρ k := by dsimp [weight, ρ]; ring
    have hWmatch (k : K) : weight k * weight k ^ ((n:ℝ)/2) = W k := by
      dsimp [W]
      rw [hweight]
      have he : ((n+2:ℕ):ℝ)/2 = 1 + (n:ℝ)/2 := by push_cast; ring
      rw [he, Real.rpow_add (hW k), Real.rpow_one]
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
        (∀ x y, ‖qb x y‖ ≤ (32 * (4:ℝ)^α) * ‖x‖ * ‖y‖) ∧
        (∀ (x y : H) (k : K), Summable (fun l => ‖outer
          ((weight l * weight l^α)⁻¹ • x l)
          ((weight (k-l) * weight (k-l)^α)⁻¹ • y (k-l))‖)) := by
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
      refine ⟨QB, ?_, hQnorm, fun x y k => (hp x y).1 k⟩
      intro x y k
      rfl
    obtain ⟨Q, hQc, hQb, hQs⟩ := hGeneralQB ((n:ℝ)/2) (by positivity)
    have hQc' (a b : H) (k : K) : Q a b k = W k • convolution (dec a) (dec b) k := by
      simpa only [hWmatch] using hQc a b k
    have hQs' (a b : H) (k : K) :
        Summable (fun l => outer (dec a l) (dec b (k-l))) := by
      simpa only [hWmatch] using (hQs a b k).of_norm
    have hρpos (k : K) (hk : k ≠ 0) : 0 < ρ k := by
      have hn : (k.1 : ℝ) ≠ 0 ∨ (k.2 : ℝ) ≠ 0 := by
        by_contra h
        push Not at h
        apply hk
        apply Prod.ext
        · exact_mod_cast h.1
        · exact_mod_cast h.2
      rcases hn with h | h
      · have hh := sq_pos_of_ne_zero h
        dsimp [ρ]
        nlinarith [sq_nonneg (k.2 : ℝ)]
      · have hh := sq_pos_of_ne_zero h
        dsimp [ρ]
        nlinarith [sq_nonneg (k.1 : ℝ)]
    have hκsq (k : K) (i : Fin 2) : ‖κ k i‖ ^ 2 ≤ ρ k := by
      fin_cases i <;> simp only [κ, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Complex.norm_intCast, sq_abs] <;>
        dsimp [ρ] <;> nlinarith [sq_nonneg (k.1:ℝ), sq_nonneg (k.2:ℝ)]
    have hcoef (k : K) (hk : k ≠ 0) (i j : Fin 2) :
        ‖-(κ k i * κ k j) / (ρ k : ℂ)‖ ≤ 1 := by
      rw [norm_div, norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (hρpos k hk), div_le_one (hρpos k hk)]
      have hi := hκsq k i
      have hj := hκsq k j
      nlinarith [sq_nonneg (‖κ k i‖ - ‖κ k j‖)]
    let m : K → TV →L[ℂ] ℂ := fun k => if k = 0 then 0 else
      ∑ i : Fin 2, ∑ j : Fin 2, (-(κ k i * κ k j) / (ρ k : ℂ)) •
        PiLp.proj 2 (𝕜 := ℂ) (fun _ : Fin 2 × Fin 2 => ℂ) (i,j)
    have hm (k : K) (Z : TV) :
        m k Z = if k = 0 then 0 else
          -(∑ i : Fin 2, ∑ j : Fin 2, κ k i * κ k j * Z (i,j)) / (ρ k : ℂ) := by
      by_cases hk : k = 0
      · simp [m, hk]
      · simp only [m, if_neg hk, sum_apply, smul_apply]
        change (∑ i : Fin 2, ∑ j : Fin 2,
          (-(κ k i * κ k j) / (ρ k : ℂ)) * Z (i,j)) = _
        simp only [Fin.sum_univ_two]
        ring
    have hmn (k : K) (Z : TV) : ‖m k Z‖ ≤ 4 * ‖Z‖ := by
      by_cases hk : k = 0
      · rw [hm, if_pos hk, norm_zero]
        positivity
      · have ht (i j : Fin 2) :
            ‖(-(κ k i * κ k j) / (ρ k : ℂ)) * Z (i,j)‖ ≤ ‖Z‖ := by
          rw [norm_mul]
          exact (mul_le_mul_of_nonneg_right (hcoef k hk i j) (norm_nonneg _)).trans
            (by simpa using PiLp.norm_apply_le Z (i,j))
        change ‖(if k = 0 then (0 : TV →L[ℂ] ℂ) else _) Z‖ ≤ _
        simp only [if_neg hk, sum_apply, smul_apply, PiLp.proj_apply, smul_eq_mul]
        calc
          _ ≤ ∑ i : Fin 2, ∑ j : Fin 2,
              ‖(-(κ k i * κ k j) / (ρ k : ℂ)) * Z (i,j)‖ :=
            (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i _ => norm_sum_le _ _))
          _ ≤ ∑ i : Fin 2, ∑ j : Fin 2, ‖Z‖ :=
            Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => ht i j))
          _ = _ := by simp; ring
    let e : V := PiLp.single 2 0 (1 : ℂ)
    let emb : ℂ →L[ℂ] V := (ContinuousLinearMap.id ℂ ℂ).smulRight e
    have hemb (c : ℂ) : emb c = (WithLp.toLp 2 (![c, 0]) : V) := by
      ext i
      change c * (PiLp.single 2 (0:Fin 2) (1:ℂ) : EuclideanSpace ℂ (Fin 2)) i = (![c,0] i)
      fin_cases i <;> simp [PiLp.single_apply]
    have hembn (c : ℂ) : ‖emb c‖ = ‖c‖ := by
      change ‖c • (PiLp.single 2 (0:Fin 2) (1:ℂ) : EuclideanSpace ℂ (Fin 2))‖ = _
      rw [norm_smul, PiLp.norm_single, norm_one, mul_one]
    let M : K → TV →L[ℝ] V := fun k => (emb.comp (m k)).restrictScalars ℝ
    have hM (k : K) : ‖M k‖ ≤ 4 := by
      apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
      intro Z
      change ‖emb (m k Z)‖ ≤ _
      rw [hembn]
      exact hmn k Z
    let MM : G →L[ℝ] H := lp.mapCLM 2 M (by norm_num : (0:ℝ) ≤ 4) hM
    let B : H →L[ℝ] H →L[ℝ] H := ((ContinuousLinearMap.compL ℝ H G H) MM).comp Q
    have hconv (a b : H) (k : K) (i j : Fin 2) :
        convolution (dec a) (dec b) k (i,j) =
          ∑' l : K, dec a l i * dec b (k-l) j := by
      have hs := (PiLp.proj 2 (𝕜 := ℂ) (fun _ : Fin 2 × Fin 2 => ℂ) (i,j)).hasSum
        (hQs' a b k).hasSum
      exact hs.tsum_eq.symm
    refine ⟨B, ?_⟩
    intro a b k
    change M k (Q a b k) = _
    rw [hQc', (M k).map_smul]
    congr 1
    change emb (m k (convolution (dec a) (dec b) k)) = _
    rw [hemb, hm]
    simp only [hconv]
    rfl
  have hSummability : (∀ n : ℕ,
  let K := ℤ × ℤ
  let V := EuclideanSpace ℂ (Fin 2)
  let H := lp (fun _ : K => V) 2
  let ρ : K → ℝ := fun k => (k.1 : ℝ)^2 + (k.2 : ℝ)^2
  let dec : H → K → V := fun a k =>
    ((1 + ρ k) ^ (((n+2 : ℕ) : ℝ) / 2))⁻¹ • a k
  let character : K → (Fin 2 → ℝ) → ℂ := fun k x =>
    Complex.exp (Complex.I * ((k.1 : ℝ) * x 0 + (k.2 : ℝ) * x 1))
  ∀ (a : H) (x : Fin 2 → ℝ), Summable (fun k : K => character k x • dec a k) : Prop) := by
    intro n
    let K := ℤ × ℤ
    let V := EuclideanSpace ℂ (Fin 2)
    let H := lp (fun _ : K => V) 2
    let X := Fin 2 → ℝ
    let ρ : K → ℝ := fun k => (k.1 : ℝ)^2 + (k.2 : ℝ)^2
    let w : K → ℝ := fun k => ((1 + ρ k) ^ (((n+2 : ℕ) : ℝ) / 2))⁻¹
    let character : K → X → ℂ := fun k x =>
      Complex.exp (Complex.I * ((k.1 : ℝ) * x 0 + (k.2 : ℝ) * x 1))
    have hwpos (k : K) : 0 < w k := by
      dsimp [w, ρ]
      positivity
    have hW (k : K) : 0 < 1 + ρ k := by dsimp [ρ]; positivity
    have hW1 (k : K) : 1 ≤ 1 + ρ k := by
      dsimp [ρ]
      nlinarith [sq_nonneg (k.1:ℝ), sq_nonneg (k.2:ℝ)]
    have hwle (k : K) : w k ≤ (1 + ρ k)⁻¹ := by
      dsimp [w]
      apply inv_anti₀ (hW k)
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le (hW1 k) (show (1:ℝ) ≤ ((n+2:ℕ):ℝ)/2 by push_cast; have := Nat.cast_nonneg (α := ℝ) n; linarith)
    let g : ℤ → ℝ := fun z => (1 + (z:ℝ)^2)⁻¹
    have hg : Summable g := by
      have hp := (Real.summable_one_div_int_pow (p := 2)).mpr (by norm_num)
      have hh := (hasSum_ite_eq (0:ℤ) (1:ℝ)).summable.add hp
      apply hh.of_nonneg_of_le (fun _ => by dsimp [g]; positivity)
      intro z
      by_cases hz : z = 0
      · simp [g, hz]
      · simp only [if_neg hz, zero_add, one_div]
        exact inv_anti₀ (sq_pos_of_ne_zero (by exact_mod_cast hz)) (by linarith)
    have hsquare : Summable (fun k : K => w k ^ 2) := by
      have hh := hg.mul_of_nonneg hg (fun z => by dsimp [g]; positivity)
        (fun z => by dsimp [g]; positivity)
      apply hh.of_nonneg_of_le (fun _ => sq_nonneg _)
      intro k
      apply (pow_le_pow_left₀ (hwpos k).le (hwle k) 2).trans
      dsimp [g]
      rw [inv_pow, ← mul_inv_rev]
      apply inv_anti₀ (by positivity)
      dsimp [ρ]
      nlinarith [sq_nonneg (k.1:ℝ), sq_nonneg (k.2:ℝ),
        sq_nonneg ((k.1:ℝ)^2), sq_nonneg ((k.2:ℝ)^2),
        mul_nonneg (sq_nonneg (k.1:ℝ)) (sq_nonneg (k.2:ℝ))]
    have hmodeNorm (a : H) (x : X) (k : K) :
        ‖character k x • (w k • a k)‖ = ‖a k‖ * w k := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, abs_of_pos (hwpos k)]
      have hc : ‖character k x‖ = 1 := by simp [character, Complex.norm_exp]
      rw [hc, one_mul, mul_comm]
    have hfull (a : H) (x : X) : Summable (fun k : K => character k x • (w k • a k)) := by
      have ha : Summable (fun k : K => ‖a k‖ ^ (2:ℝ)) := by
        simpa using (lp.memℓp a).summable (by norm_num : 0 < (2:ℝ≥0∞).toReal)
      have hc := Real.summable_and_inner_le_Lp_mul_Lq_tsum_of_nonneg
        Real.HolderConjugate.two_two (fun k => norm_nonneg (a k)) (fun k => (hwpos k).le)
        ha (by simpa only [Real.rpow_two] using hsquare)
      exact Summable.of_norm (hc.1.congr (fun k => (hmodeNorm a x k).symm))
    exact hfull
  have hwp (m : ℕ) (k : K) : 0 < w m k := by
    dsimp [w, ρ]
    positivity
  have hdecode (m : ℕ) (t : ℝ) (ht : t ∈ Icc 0 τ) (k : K) :
      dec m (U m t) k = a t k := by
    change (w m k)⁻¹ • U m t k = _
    rw [hUc m t ht k, smul_smul, inv_mul_cancel₀ (hwp m k).ne', one_smul]
  have hUD : UniqueDiffOn ℝ (Icc 0 τ) := uniqueDiffOn_Icc hτ
  have hreg (n : ℕ) : ∀ m : ℕ, ContDiffOn ℝ n (U m) (Icc 0 τ) := by
    induction n with
    | zero =>
      intro m
      exact contDiffOn_zero.mpr (hUcont m)
    | succ n ih =>
      intro m
      rw [Nat.cast_add, Nat.cast_one, contDiffOn_succ_iff_derivWithin hUD]
      refine ⟨fun t ht => (hUd m t ht).differentiableWithinAt, by simp, ?_⟩
      have hF : ContDiffOn ℝ n
          (fun t => L m (U (m+2) t) - B m (U (m+2) t) (U (m+2) t))
          (Icc 0 τ) :=
        ((L m).contDiff.comp_contDiffOn (ih (m+2))).sub
          (((B m).contDiff.comp_contDiffOn (ih (m+2))).clm_apply (ih (m+2)))
      apply hF.congr
      intro t ht
      exact (hUd m t ht).derivWithin (hUD t ht)
  have htime (m : ℕ) : ContDiffOn ℝ ∞ (U m) (Icc 0 τ) :=
    contDiffOn_infty.mpr (fun n => hreg n m)
  let X := Fin 2 → ℝ
  let S := (Icc 0 τ) ×ˢ (Set.univ : Set X)
  have htimeprod (n : ℕ) : ContDiffOn ℝ n
      (fun z : ℝ × X => (U (n+2) z.1, z.2)) S :=
    (((contDiffOn_infty.mp (htime (n+2))) n).comp contDiffOn_fst (fun z hz => hz.1)).prodMk
      contDiffOn_snd
  constructor
  · apply contDiffOn_infty.mpr
    intro n
    have hv := (joint_contdiff_fourier_synthesis n).comp_contDiffOn (htimeprod n)
    apply contDiffOn_pi.mpr
    intro i
    let ev : V →L[ℂ] ℂ := PiLp.proj 2 (𝕜 := ℂ) (fun _ : Fin 2 => ℂ) i
    have hfinal := Complex.reCLM.contDiff.comp_contDiffOn
      ((ev.restrictScalars ℝ).contDiff.comp_contDiffOn hv)
    apply hfinal.congr
    intro z hz
    have hs : Summable (fun k : K => character k z.2 • dec (n+2) (U (n+2) z.1) k) :=
      hSummability n (U (n+2) z.1) z.2
    have he (k : K) :
        ev (character k z.2 • dec (n+2) (U (n+2) z.1) k) =
          character k z.2 * a z.1 k i := by
      rw [map_smul, hdecode (n+2) z.1 hz.1 k]
      rfl
    have hh := ev.hasSum hs.hasSum
    have hh' : HasSum (fun k : K => character k z.2 * a z.1 k i)
        (ev (∑' k : K, character k z.2 • dec (n+2) (U (n+2) z.1) k)) := by
      simpa only [Function.comp_def, he] using hh
    exact congrArg Complex.re hh'.tsum_eq
  · apply contDiffOn_infty.mpr
    intro n
    obtain ⟨Q, hQc⟩ := hCoeff n
    have hQpath (t : ℝ) (ht : t ∈ Icc 0 τ) (k : K) :
        Q (U (n+2) t) (U (n+2) t) k =
          w (n+2) k • (WithLp.toLp 2 (![pc t k, 0]) : V) := by
      have h := hQc (U (n+2) t) (U (n+2) t) k
      have hd : (fun l => dec (n+2) (U (n+2) t) l) = a t :=
        funext (hdecode (n+2) t ht)
      change Q (U (n+2) t) (U (n+2) t) k =
        w (n+2) k • (WithLp.toLp 2
          (![if k = 0 then 0 else
            -(∑ i : Fin 2, ∑ j : Fin 2, κ k i * κ k j *
              ∑' l : K, dec (n+2) (U (n+2) t) l i *
                dec (n+2) (U (n+2) t) (k-l) j) / (ρ k : ℂ), 0]) : V) at h
      rw [show dec (n+2) (U (n+2) t) = a t from hd] at h
      exact h
    have hQdecode (t : ℝ) (ht : t ∈ Icc 0 τ) (k : K) :
        dec (n+2) (Q (U (n+2) t) (U (n+2) t)) k =
          (WithLp.toLp 2 (![pc t k, 0]) : V) := by
      change (w (n+2) k)⁻¹ • Q (U (n+2) t) (U (n+2) t) k = _
      rw [hQpath t ht k, smul_smul, inv_mul_cancel₀ (hwp (n+2) k).ne', one_smul]
    have hqtime := (Q.contDiff.comp_contDiffOn (htimeprod n).fst).clm_apply (htimeprod n).fst
    have hsnd : ContDiffOn ℝ n (fun z : ℝ × X => z.2) S := contDiffOn_snd
    have hqprod := hqtime.prodMk hsnd
    have hsynth : ContDiff ℝ n
        (fun z : H × X => ∑' k : K, character k z.2 • dec (n+2) z.1 k) :=
      joint_contdiff_fourier_synthesis n
    have hpv := hsynth.comp_contDiffOn hqprod
    let ev : V →L[ℂ] ℂ := PiLp.proj 2 (𝕜 := ℂ) (fun _ : Fin 2 => ℂ) 0
    have hfinal := Complex.reCLM.contDiff.comp_contDiffOn
      ((ev.restrictScalars ℝ).contDiff.comp_contDiffOn hpv)
    apply hfinal.congr
    intro z hz
    have hs : Summable (fun k : K => character k z.2 •
        dec (n+2) (Q (U (n+2) z.1) (U (n+2) z.1)) k) :=
      hSummability n (Q (U (n+2) z.1) (U (n+2) z.1)) z.2
    have he (k : K) :
        ev (character k z.2 • dec (n+2) (Q (U (n+2) z.1) (U (n+2) z.1)) k) =
          character k z.2 * pc z.1 k := by
      rw [map_smul, hQdecode z.1 hz.1 k]
      rfl
    have hh := ev.hasSum hs.hasSum
    have hh' : HasSum (fun k : K => character k z.2 * pc z.1 k)
        (ev (∑' k : K, character k z.2 •
          dec (n+2) (Q (U (n+2) z.1) (U (n+2) z.1)) k)) := by
      simpa only [Function.comp_def, he] using hh
    exact congrArg Complex.re hh'.tsum_eq

end D5.S3.FluidDynamics.Fourier.MildPathVelocityPressureRegularity
