/- GID: D5/S3/Fourier/Asymptotics/CyclicGrowingCoupledFit
   generality: G
   mirror-B: D5/B/S3/Fourier/Asymptotics/CyclicGrowingCoupledFit
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Joint front and fixed rear moments admit an eventually invertible scaled fit. -/

import D5.S3.Fourier.Asymptotics.CyclicGrowingFrontFit
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc

open Finset Matrix Filter
open scoped Topology

namespace D5.S3.Fourier.Asymptotics.CyclicGrowingCoupledFit

noncomputable section

set_option autoImplicit false

def rearWeight (h r : ℝ) : ℝ := (1 + Real.cos (r * h)) / 2

def rearMoment (h r : ℝ) : ℝ := r ^ 2 * Real.sinc (r * h) ^ 2

/-- The two unscaled rear features converge at each fixed offset. -/
theorem rearFeatures_tendsto {h : ℕ → ℝ} (hh : Tendsto h atTop (𝓝 0)) (r : ℝ) :
    Tendsto (fun n => rearWeight (h n) r) atTop (𝓝 1) ∧
      Tendsto (fun n => rearMoment (h n) r) atTop (𝓝 (r ^ 2)) := by
  let w := fun n => rearWeight (h n) r
  let x := fun n => rearMoment (h n) r
  have ha : Tendsto (fun n => r * h n) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hh (a := r)
  have hc : Tendsto (fun n => Real.cos (r * h n)) atTop (𝓝 1) := by
    rw [← Real.cos_zero]
    exact Real.continuous_cos.continuousAt.tendsto.comp ha
  have hw : Tendsto w atTop (𝓝 1) := by
    simpa [w, rearWeight] using (tendsto_const_nhds.add hc (a := 1)).div_const (2 : ℝ)
  have hsin : Tendsto (fun n => Real.sinc (r * h n)) atTop (𝓝 1) := by
    rw [← Real.sinc_zero]
    exact Real.continuous_sinc.continuousAt.tendsto.comp ha
  have hx : Tendsto x atTop (𝓝 (r^2)) := by
    simpa [x, rearMoment] using (hsin.pow 2).const_mul (r^2)
  exact ⟨hw, hx⟩

/-- The absolute rear cosine deficit with its quadratic window scaling. -/
theorem rearDeficit_scaled_tendsto {h : ℕ → ℝ}
    (hu : Tendsto (fun n : ℕ => (n : ℝ) * h n) atTop (𝓝 0)) (r : ℝ) :
    Tendsto (fun n : ℕ => (n : ℝ)^2 * (1 - rearWeight (h n) r)) atTop (𝓝 0) := by
  have hb : Tendsto (fun n : ℕ => (r^2/4)*((n : ℝ)*h n)^2) atTop (𝓝 0) := by
    simpa using (hu.pow 2).const_mul (r^2/4)
  apply squeeze_zero _ _ hb
  · intro n
    apply mul_nonneg (sq_nonneg _)
    unfold rearWeight
    linarith [Real.cos_le_one (r*h n)]
  · intro n
    have hle : 1 - rearWeight (h n) r ≤ (r*h n)^2/4 := by
      unfold rearWeight
      linarith [Real.one_sub_sq_div_two_le_cos (x := r*h n)]
    calc
      _ ≤ (n : ℝ)^2*((r*h n)^2/4) :=
        mul_le_mul_of_nonneg_left hle (sq_nonneg _)
      _ = _ := by ring

def rearMatrix (n h r : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  let w := rearWeight h r
  let f := 1 - w
  let x := rearMoment h r
  !![f^2 / n, f * x / n^3, f * w / n^3;
    x * f / n^3, x^2 / n^5, x * w / n^5;
    n^2 * w^2 * f, w^2 * x, w^3]

private theorem rearMatrix_tendsto {h : ℕ → ℝ} (hh : Tendsto h atTop (𝓝 0))
    (hu : Tendsto (fun n : ℕ => (n : ℝ) * h n) atTop (𝓝 0)) (r : ℝ) :
    Tendsto (fun n : ℕ => rearMatrix n (h n) r) atTop
      (𝓝 !![0, 0, 0; 0, 0, 0; 0, r^2, 1]) := by
  let w := fun n => rearWeight (h n) r
  let f := fun n => 1 - w n
  let x := fun n => rearMoment (h n) r
  obtain ⟨hw, hx⟩ := rearFeatures_tendsto hh r
  have hf : Tendsto f atTop (𝓝 0) := by
    simpa only [sub_self] using tendsto_const_nhds.sub hw (a := (1 : ℝ))
  have hn : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hInv : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hn
  have hA : Tendsto (fun n : ℕ => (n : ℝ)^2 * w n^2 * f n) atTop (𝓝 0) := by
    have ht := (rearDeficit_scaled_tendsto hu r).mul (hw.pow 2)
    apply (show Tendsto (fun n : ℕ => ((n : ℝ)^2 * f n) * w n^2) atTop (𝓝 0)
      by simpa only [zero_mul] using ht).congr
    intro n
    ring
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  fin_cases i <;> fin_cases j
  · change Tendsto (fun n : ℕ => f n^2 / (n : ℝ)) atTop (𝓝 0)
    simpa only [div_eq_mul_inv, zero_pow (by decide : 2 ≠ 0), zero_mul] using
      (hf.pow 2).mul hInv
  · change Tendsto (fun n : ℕ => f n * x n / (n : ℝ)^3) atTop (𝓝 0)
    simpa only [div_eq_mul_inv, inv_pow, zero_mul] using (hf.mul hx).mul (hInv.pow 3)
  · change Tendsto (fun n : ℕ => f n * w n / (n : ℝ)^3) atTop (𝓝 0)
    simpa only [div_eq_mul_inv, inv_pow, zero_mul] using (hf.mul hw).mul (hInv.pow 3)
  · change Tendsto (fun n : ℕ => x n * f n / (n : ℝ)^3) atTop (𝓝 0)
    simpa only [div_eq_mul_inv, inv_pow, mul_zero, zero_mul] using
      (hx.mul hf).mul (hInv.pow 3)
  · change Tendsto (fun n : ℕ => x n^2 / (n : ℝ)^5) atTop (𝓝 0)
    simpa only [div_eq_mul_inv, inv_pow, zero_pow (by decide : 5 ≠ 0), mul_zero] using
      (hx.pow 2).mul (hInv.pow 5)
  · change Tendsto (fun n : ℕ => x n * w n / (n : ℝ)^5) atTop (𝓝 0)
    simpa only [div_eq_mul_inv, inv_pow, zero_pow (by decide : 5 ≠ 0), mul_zero] using
      (hx.mul hw).mul (hInv.pow 5)
  · exact hA
  · change Tendsto (fun n => w n^2 * x n) atTop (𝓝 (r^2))
    simpa only [one_pow, one_mul] using (hw.pow 2).mul hx
  · change Tendsto (fun n => w n^3) atTop (𝓝 1)
    simpa only [one_pow] using hw.pow 3

open D5.S3.Fourier.Asymptotics.LatticeSquareMomentActivation
open D5.S3.Fourier.Asymptotics.CyclicGrowingFrontFit

theorem front_site_bounds (n : ℕ) (hn : 0 < n) (u : ℝ) {j : ℤ}
    (hj : j ∈ latticeInterval n) (i : Fin 2) :
    let x := (j : ℝ) / n
    let w := (1 - Real.cos (x * u)) / 2
    (0 ≤ w ∧ w ≤ u ^ 2 / 4) ∧
      (0 ≤ frontFeatures u x i ∧ frontFeatures u x i ≤ 1) := by
  intro x w
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hx : x ^ 2 ≤ 1 := by
    dsimp only [x]
    rw [div_pow, div_le_iff₀ (sq_pos_of_pos hnR), one_mul]
    exact (sq_le_iff_mem j n).mpr hj
  have hxu : (x * u) ^ 2 ≤ u ^ 2 := by
    rw [mul_pow]
    simpa using mul_le_mul_of_nonneg_right hx (sq_nonneg u)
  have hw : 0 ≤ w ∧ w ≤ u ^ 2 / 4 := by
    dsimp only [w]
    exact ⟨by linarith [Real.cos_le_one (x * u)],
      by linarith [Real.one_sub_sq_div_two_le_cos (x := x * u)]⟩
  have hxAbs : |x| ≤ 1 := (sq_le_sq₀ (abs_nonneg x) zero_le_one).mp
    (by simpa only [sq_abs, one_pow] using hx)
  exact ⟨hw, frontFeatures_bounds hxAbs i⟩

/-- Bounds for the mixed entries of the three scaled rows of the front matrix. -/
theorem front_mixed_block (n : ℕ) (hn : 0 < n) (u : ℝ) (i : Fin 2) :
    let w := fun j : ℤ => (1 - Real.cos ((j : ℝ) / n * u)) / 2
    let f := fun j : ℤ => frontFeatures u ((j : ℝ) / n) i
    ((∑ j ∈ latticeInterval n, f j * w j) / (n : ℝ) ^ 3 ≤ 3 * u ^ 2 / (4 * (n : ℝ) ^ 2)) ∧
    ((n : ℝ) ^ 2 * (∑ j ∈ latticeInterval n, w j ^ 2 * f j) ≤ 3 * (n : ℝ) ^ 3 * u ^ 4 / 16) ∧
    ((∑ j ∈ latticeInterval n, w j ^ 3) ≤ 3 * (n : ℝ) * u ^ 6 / 64) := by
  intro w f
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hnOne : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hcard : ((latticeInterval n).card : ℝ) ≤ 3 * n := by
    rw [card_latticeInterval]
    linarith
  have hsum {a : ℤ → ℝ} {B : ℝ} (hB : 0 ≤ B)
      (hpoint : ∀ j ∈ latticeInterval n, a j ≤ B) :
      (∑ j ∈ latticeInterval n, a j) ≤ 3 * n * B := by
    calc
      _ ≤ ∑ _j ∈ latticeInterval n, B := sum_le_sum hpoint
      _ = ((latticeInterval n).card : ℝ) * B := by rw [sum_const, nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right hcard hB
  have hbound {j : ℤ} (hj : j ∈ latticeInterval n) :
      (0 ≤ w j ∧ w j ≤ u ^ 2 / 4) ∧ (0 ≤ f j ∧ f j ≤ 1) :=
    front_site_bounds n hn u hj i
  refine ⟨?_, ?_, ?_⟩
  · apply (div_le_iff₀ (pow_pos hnR _)).mpr
    calc
      _ ≤ 3 * (n : ℝ) * (u ^ 2 / 4) := by
        apply hsum (by positivity)
        intro j hj
        obtain ⟨⟨hw0, hw⟩, ⟨_, hf⟩⟩ := hbound hj
        simpa using mul_le_mul hf hw hw0 zero_le_one
      _ = _ := by field_simp [hnR.ne']
  · calc
      _ ≤ (n : ℝ) ^ 2 * (3 * n * (u ^ 2 / 4) ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
        apply hsum (sq_nonneg _)
        intro j hj
        obtain ⟨⟨hw0, hw⟩, ⟨hf0, hf⟩⟩ := hbound hj
        have hp := pow_le_pow_left₀ hw0 hw 2
        simpa using mul_le_mul hp hf hf0 (sq_nonneg _)
      _ = _ := by ring
  · calc
      _ ≤ 3 * (n : ℝ) * (u ^ 2 / 4) ^ 3 := by
        apply hsum (by positivity)
        intro j hj
        obtain ⟨⟨hw0, hw⟩, _⟩ := hbound hj
        exact pow_le_pow_left₀ hw0 hw 3
      _ = _ := by ring

def frontMatrix (n : ℕ) (u : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  let w := fun j : ℤ => (1 - Real.cos ((j : ℝ) / n * u)) / 2
  let f := fun i j => frontFeatures u ((j : ℝ) / n) i
  let upper := fun i => (∑ j ∈ latticeInterval n, f i j * w j) / (n : ℝ)^3
  let lower := fun i => (n : ℝ)^2 * (∑ j ∈ latticeInterval n, w j^2 * f i j)
  !![frontGram n u 0 0, frontGram n u 0 1, upper 0;
    frontGram n u 1 0, frontGram n u 1 1, upper 1;
    lower 0, lower 1, ∑ j ∈ latticeInterval n, w j^3]

private theorem frontMatrix_tendsto {u : ℕ → ℝ}
    (hu : Tendsto u atTop (𝓝 0))
    (hscale : Tendsto (fun n : ℕ => (n : ℝ)^3 * (u n)^4) atTop (𝓝 0)) :
    Tendsto (fun n => frontMatrix n (u n)) atTop
      (𝓝 !![(2 : ℝ), 2/3, 0; 2/3, 2/5, 0; 0, 0, 0]) := by
  let w := fun (n : ℕ) (j : ℤ) => (1 - Real.cos ((j : ℝ) / (n : ℝ) * u n)) / 2
  let f := fun (n : ℕ) (i : Fin 2) (j : ℤ) => frontFeatures (u n) ((j : ℝ) / (n : ℝ)) i
  have hgram (i j : Fin 2) :=
    tendsto_pi_nhds.1 (tendsto_pi_nhds.1 (frontGram_tendsto hu) i) j
  have hnonneg (n : ℕ) (j : ℤ) : 0 ≤ w n j := by
    dsimp only [w]
    linarith [Real.cos_le_one ((j : ℝ) / (n : ℝ) * u n)]
  have hupper (i : Fin 2) :
      Tendsto (fun n => (∑ j ∈ latticeInterval n, f n i j * w n j) / (n : ℝ)^3)
        atTop (𝓝 0) := by
    have ht : Tendsto (fun n => 3 * (u n)^2 / 4) atTop (𝓝 0) := by
      simpa using ((hu.pow 2).const_mul (3 : ℝ)).div_const 4
    apply squeeze_zero' _ _ ht
    · filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
      apply div_nonneg _ (by positivity)
      refine sum_nonneg fun j hj => mul_nonneg ?_ (hnonneg n j)
      exact (front_site_bounds n hn (u n) hj i).2.1
    · filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
      have hone : (1 : ℝ) ≤ n := by exact_mod_cast hn
      refine (front_mixed_block n hn (u n) i).1.trans ?_
      exact div_le_div_of_nonneg_left (by positivity) (by norm_num) (by nlinarith)
  have hlower (i : Fin 2) :
      Tendsto (fun n : ℕ => (n : ℝ)^2 * (∑ j ∈ latticeInterval n, w n j^2 * f n i j))
        atTop (𝓝 0) := by
    have ht : Tendsto (fun n : ℕ => 3 * (n : ℝ)^3 * (u n)^4 / 16) atTop (𝓝 0) := by
      have h := hscale.const_mul (3 / 16 : ℝ)
      convert h using 1
      · funext n; ring
      · simp
    apply squeeze_zero' _ _ ht
    · filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
      apply mul_nonneg (sq_nonneg _) (sum_nonneg ?_)
      intro j hj
      exact mul_nonneg (sq_nonneg _) (front_site_bounds n hn (u n) hj i).2.1
    · filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
      exact (front_mixed_block n hn (u n) i).2.1
  have hlast : Tendsto (fun n => ∑ j ∈ latticeInterval n, w n j^3) atTop (𝓝 0) := by
    have ht : Tendsto (fun n : ℕ => 3 * (n : ℝ)^3 * (u n)^4 / 64) atTop (𝓝 0) := by
      have h := hscale.const_mul (3 / 64 : ℝ)
      convert h using 1
      · funext n; ring
      · simp
    apply squeeze_zero' (Eventually.of_forall fun n => sum_nonneg
      fun j _ => pow_nonneg (hnonneg n j) _) _ ht
    filter_upwards [eventually_ge_atTop (1 : ℕ),
      (hu.pow 2).eventually_le_const (show (0 : ℝ) ^ 2 < 1 by norm_num)] with n hn hu1
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hnC : (n : ℝ) ≤ (n : ℝ)^3 := le_self_pow₀ hnR (by decide : 3 ≠ 0)
    refine (front_mixed_block n hn (u n) 0).2.2.trans ?_
    apply div_le_div_of_nonneg_right _ (by norm_num)
    have hpow : (u n)^6 ≤ (u n)^4 := by
      rw [show (6 : ℕ) = 4 + 2 by decide, pow_add]
      exact mul_le_of_le_one_right (by positivity) hu1
    gcongr
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  fin_cases i <;> fin_cases j
  · exact hgram 0 0
  · exact hgram 0 1
  · exact hupper 0
  · exact hgram 1 0
  · exact hgram 1 1
  · exact hupper 1
  · exact hlower 0
  · exact hlower 1
  · exact hlast

def coupledMomentMatrix (S : Finset ℝ) (n : ℕ) (h : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  frontMatrix n ((n : ℝ) * h) + ∑ r ∈ S, rearMatrix n h r

theorem mesh_limits {h : ℕ → ℝ}
    (hscale : Tendsto (fun n : ℕ => (n : ℝ)^3 * ((n : ℝ) * h n)^4) atTop (𝓝 0)) :
    Tendsto h atTop (𝓝 0) ∧ Tendsto (fun n : ℕ => (n : ℝ) * h n) atTop (𝓝 0) := by
  have hfour : Tendsto (fun n : ℕ => ((n : ℝ) * h n)^4) atTop (𝓝 0) := by
    refine squeeze_zero' (Eventually.of_forall fun _ => by positivity) ?_ hscale
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hpow : (1 : ℝ) ≤ (n : ℝ)^3 := one_le_pow₀ hnR
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hpow
      (show 0 ≤ ((n : ℝ) * h n)^4 by positivity)
  have hs : Tendsto (fun n : ℕ => ((n : ℝ) * h n)^2) atTop (𝓝 0) := by
    have ht := Real.continuous_sqrt.continuousAt.tendsto.comp hfour
    change Tendsto (fun n : ℕ => Real.sqrt (((n : ℝ) * h n)^4)) atTop
      (𝓝 (Real.sqrt 0)) at ht
    simpa only [show (4 : ℕ) = 2 * 2 by decide, pow_mul, Real.sqrt_sq (sq_nonneg _),
      Real.sqrt_zero] using ht
  have hu : Tendsto (fun n : ℕ => (n : ℝ) * h n) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have ht := Real.continuous_sqrt.continuousAt.tendsto.comp hs
    change Tendsto (fun n : ℕ => Real.sqrt (((n : ℝ) * h n)^2)) atTop
      (𝓝 (Real.sqrt 0)) at ht
    simpa only [Real.sqrt_sq_eq_abs, Real.sqrt_zero, Real.norm_eq_abs] using ht
  refine ⟨?_, hu⟩
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_
    (tendsto_zero_iff_norm_tendsto_zero.mp hu)
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Nat.cast_nonneg n : 0 ≤ (n : ℝ))]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hnR (abs_nonneg (h n))

/-- The limiting coupled moment matrix on a growing front and a fixed rear support. -/
theorem coupledMatrix_tendsto {h : ℕ → ℝ}
    (hscale : Tendsto (fun n : ℕ => (n : ℝ)^3 * ((n : ℝ) * h n)^4) atTop (𝓝 0))
    (S : Finset ℝ) :
    let readout := fun state : (Finset ℝ × ℕ) × ℝ =>
      coupledMomentMatrix state.1.1 state.1.2 state.2
    Tendsto (fun n : ℕ => readout ((S, n), h n)) atTop (𝓝 !![(2 : ℝ), 2/3, 0; 2/3, 2/5, 0; 0, ∑ r ∈ S, r^2, (S.card : ℝ)]) := by
  obtain ⟨hh, hu⟩ := mesh_limits hscale
  dsimp only [coupledMomentMatrix]
  have hr := tendsto_finsetSum S (fun r _ => rearMatrix_tendsto hh hu r)
  have hf := frontMatrix_tendsto hu hscale
  convert hf.add hr using 2
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.add_apply, Matrix.sum_apply]

theorem coupledLimit_det (S : Finset ℝ) :
    (!![(2 : ℝ), 2/3, 0; 2/3, 2/5, 0; 0, ∑ r ∈ S, r^2, (S.card : ℝ)]).det =
      16 * (S.card : ℝ) / 45 := by
  rw [Matrix.det_fin_three]
  simp
  ring

def coefficientRow (n F X W : ℝ) : Fin 3 → ℝ := ![F / n, X / n, W / n^3]
def momentRow (n F X W : ℝ) : Fin 3 → ℝ := ![F, X, n^3 * W^2]

private theorem frontMatrix_outer (n : ℕ) (hn : 0 < n) (u : ℝ) :
    frontMatrix n u = ∑ j ∈ latticeInterval n,
      let F := frontFeatures u ((j : ℝ) / n) 0
      let X := frontFeatures u ((j : ℝ) / n) 1
      let W := 1 - F
      vecMulVec (momentRow n F X W) (coefficientRow n F X W) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hw (j : ℤ) : 1 - frontFeatures u ((j : ℝ) / n) 0 =
      (1 - Real.cos ((j : ℝ) / n * u)) / 2 := by
    change 1 - (1 + _) / 2 = _
    ring
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [frontMatrix, frontGram, Matrix.sum_apply, momentRow, coefficientRow, hw]
  all_goals
    try rw [sum_div]
    try rw [mul_sum]
    apply sum_congr rfl
    intro j hj
    field_simp [hn0]

theorem rearMatrix_outer {n : ℝ} (hn : n ≠ 0) (h r : ℝ) :
    let F := 1 - rearWeight h r
    let X := rearMoment h r / n^2
    let W := rearWeight h r
    rearMatrix n h r = vecMulVec (momentRow n F X W) (coefficientRow n F X W) := by
  intro F X W
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rearMatrix, vecMulVec_apply, momentRow, coefficientRow, F, X, W] <;>
    field_simp [hn]

theorem coupledMatrix_eventually_det_ne_zero {h : ℕ → ℝ}
    (hscale : Tendsto (fun n : ℕ => (n : ℝ)^3 * ((n : ℝ) * h n)^4) atTop (𝓝 0))
    {S : Finset ℝ} (hS : S.Nonempty) :
    ∀ᶠ n : ℕ in atTop,
      (frontMatrix n ((n : ℝ) * h n) + ∑ r ∈ S, rearMatrix n (h n) r).det ≠ 0 := by
  have hdet := continuous_id.matrix_det.continuousAt.tendsto.comp
    (coupledMatrix_tendsto hscale S)
  have hne :
      (!![(2 : ℝ), 2/3, 0; 2/3, 2/5, 0; 0, ∑ r ∈ S, r^2, (S.card : ℝ)]).det ≠ 0 := by
    rw [coupledLimit_det]
    have : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
    positivity
  exact hdet.eventually_ne hne

private theorem sum_outer_mulVec {ι : Type*} (s : Finset ι)
    (a b : ι → Fin 3 → ℝ) (v : Fin 3 → ℝ) :
    (∑ j ∈ s, vecMulVec (a j) (b j)) *ᵥ v =
      ∑ j ∈ s, (b j ⬝ᵥ v) • a j := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [sum_insert hi, sum_insert hi, add_mulVec, ih, vecMulVec_mulVec]
    congr 1
    ext k
    simp [mul_comm]

/-- The three scaled moments of the fitted coefficient vector. -/
def coupledMoments (S : Finset ℝ) (n : ℕ) (h : ℝ) (v : Fin 3 → ℝ) : Fin 3 → ℝ :=
  let u := (n : ℝ) * h
  let fw := fun j : ℤ => 1 - frontFeatures u ((j : ℝ) / n) 0
  let ff := fun j : ℤ => frontFeatures u ((j : ℝ) / n) 0
  let fx := fun j : ℤ => frontFeatures u ((j : ℝ) / n) 1
  let rw := fun r : ℝ => rearWeight (h) r
  let rf := fun r : ℝ => 1 - rw r
  let rx := fun r : ℝ => rearMoment (h) r / (n : ℝ)^2
  (∑ j ∈ latticeInterval n, (coefficientRow n (ff j) (fx j) (fw j) ⬝ᵥ v) •
    momentRow n (ff j) (fx j) (fw j)) +
  (∑ r ∈ S, (coefficientRow n (rf r) (rx r) (rw r) ⬝ᵥ v) •
    momentRow n (rf r) (rx r) (rw r))

/-- The assembled matrix represents the same weighted moments at each site. -/
theorem coupledMomentMatrix_mulVec (S : Finset ℝ) (n : ℕ) (hn : 0 < n)
    (h : ℝ) (v : Fin 3 → ℝ) :
    coupledMomentMatrix S n h *ᵥ v = coupledMoments S n h v := by
  classical
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  unfold coupledMomentMatrix coupledMoments
  dsimp only
  rw [add_mulVec, frontMatrix_outer n hn, sum_outer_mulVec]
  congr 1
  have hrear : (∑ r ∈ S, rearMatrix n h r) =
      ∑ r ∈ S, vecMulVec
        (momentRow n (1 - rearWeight h r) (rearMoment h r / (n : ℝ)^2)
          (rearWeight h r))
        (coefficientRow n (1 - rearWeight h r) (rearMoment h r / (n : ℝ)^2)
          (rearWeight h r)) :=
    sum_congr rfl fun r _ => rearMatrix_outer hn0 h r
  rw [hrear, sum_outer_mulVec]

/-- For every prescribed three-moment right side, the joint finite fit exists uniquely eventually. -/
theorem coupledFit_eventually {h : ℕ → ℝ}
    (hscale : Tendsto (fun n : ℕ => (n : ℝ)^3 * ((n : ℝ) * h n)^4) atTop (𝓝 0))
    {S : Finset ℝ} (hS : S.Nonempty) (rhs : ℕ → Fin 3 → ℝ) :
    let readout := fun state : ((Finset ℝ × ℕ) × ℝ) × (Fin 3 → ℝ) =>
      coupledMoments state.1.1.1 state.1.1.2 state.1.2 state.2
    ∀ᶠ n : ℕ in atTop, ∃! v : Fin 3 → ℝ, readout (((S, n), h n), v) = rhs n := by
  classical
  dsimp only
  filter_upwards [eventually_ge_atTop (1 : ℕ),
    coupledMatrix_eventually_det_ne_zero hscale hS] with n hn hdet
  let M := coupledMomentMatrix S n (h n)
  have hpos : 0 < n := hn
  have hM (v : Fin 3 → ℝ) : M *ᵥ v = coupledMoments S n (h n) v :=
    coupledMomentMatrix_mulVec S n hpos (h n) v
  have hinv : IsUnit M.det := isUnit_iff_ne_zero.mpr hdet
  refine ⟨M⁻¹ *ᵥ rhs n, ?_, ?_⟩
  · change _ = rhs n
    exact (hM (M⁻¹ *ᵥ rhs n)).symm.trans (by
      rw [mulVec_mulVec, mul_nonsing_inv _ hinv, one_mulVec])
  · intro v hv
    have hv' : M *ᵥ v = rhs n := (hM v).trans hv
    rw [← hv', mulVec_mulVec, nonsing_inv_mul _ hinv, one_mulVec]

end

end D5.S3.Fourier.Asymptotics.CyclicGrowingCoupledFit
