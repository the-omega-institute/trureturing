/- GID: D5/S3/Fourier/Asymptotics/MovingFejerGaussianPrincipal
   generality: G
   mirror-B: D5/B/S3/Fourier/Asymptotics/MovingFejerGaussianPrincipal
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The moving central Fejer integral has the Gaussian principal coefficient. -/

import D5.S3.Fourier.Asymptotics.FinitePairGaussianLimit
import D5.S3.Analytic.Fourier.AngularFejerKernel
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

open Finset Filter Set MeasureTheory
open scoped Topology
open D5.S3.Fourier.Asymptotics.FinitePairGaussianLimit
open D5.S3.Fourier.Concentration.FiniteTailMomentMissingWindow
open D5.S3.Analytic.Fourier.AngularFejerKernel
noncomputable section

namespace D5.S3.Fourier.Asymptotics.MovingFejerGaussianPrincipal

/-- The normalized Fejer moment restricted to a growing fourth-moment window. -/
theorem central_fejer_gaussian_limit {J : ℕ → Type*} [∀ n,Fintype (J n)] (g w : ∀ n,J n → ℝ)
    (hw : ∀ᶠ n in atTop, ∀ i j, 0≤w n i*w n j) (hW : ∀ᶠ n in atTop, ∑ j,w n j=1)
    (hM : ∀ᶠ n in atTop, 0<pairMoment (g n) (w n) 2)
    (ρ A : ℕ → ℝ) (hρ : Tendsto ρ atTop (𝓝 0)) (hA : Tendsto A atTop atTop)
    (C : ℝ) (hC : C < 6)
    (hwin : ∀ᶠ n in atTop, A n^2*pairMoment (g n) (w n) 4 ≤ C*(n:ℝ)*pairMoment (g n) (w n) 2^2) :
    let kernel := fun z : ℝ => Real.sinc z^2
    Tendsto (fun n => (1/(2*Real.pi))*(∫ u in -(A n)..A n,
      kernel (ρ n*u/2) * ‖complexScore (g n) (w n)
        (u/Real.sqrt ((n:ℝ)*pairMoment (g n) (w n) 2/2))‖^(2*n)))
      atTop (𝓝 (1/(2*Real.sqrt Real.pi))) := by
  intro kernel
  have hR : Tendsto (fun n => pairMoment (g n) (w n) 4 /
      ((n:ℝ)*pairMoment (g n) (w n) 2^2)) atTop (𝓝 0) := by
    have hUpper : Tendsto (fun n => C * (A n)⁻¹ ^ 2) atTop (𝓝 0) := by
      simpa using ((tendsto_inv_atTop_zero.comp hA).pow 2).const_mul C
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hUpper ?_ ?_
    · filter_upwards [hw] with n hwn
      apply div_nonneg _ (by positivity)
      unfold pairMoment
      exact sum_nonneg fun i _ => sum_nonneg fun j _ =>
        mul_nonneg (hwn i j) (by positivity)
    · filter_upwards [hwin,hM,eventually_gt_atTop (0:ℕ),hA.eventually_gt_atTop 0] with n hn hMn hn0 hAn
      have hd : 0 < (n:ℝ)*pairMoment (g n) (w n) 2^2 := by positivity
      have ha : 0 < A n ^ 2 := by positivity
      rw [inv_pow, ← div_eq_mul_inv]
      apply (div_le_div_iff₀ hd ha).2
      nlinarith only [hn]
  let b := 1-C/6
  have hb : 0 < b := by dsimp [b]; linarith
  let s := fun n : ℕ => Real.sqrt ((n:ℝ)*pairMoment (g n) (w n) 2/2)
  let P := fun n u => ‖complexScore (g n) (w n) (u/s n)‖^(2*n)
  let q := fun n u => Real.sinc (ρ n*u/2)^2
  let F := fun n : ℕ => (Ioc (-(A n)) (A n)).indicator (fun u => q n u*P n u)
  have hcont (n : ℕ) : Continuous (fun u => q n u*P n u) := by
    apply Continuous.mul
    · dsimp [q]
      exact (Real.continuous_sinc.comp (by fun_prop)).pow 2
    · dsimp [P]
      exact ((complexScore_continuous (g n) (w n)).comp (by fun_prop)).norm.pow _
  have hlim := tendsto_integral_filter_of_dominated_convergence (μ := volume)
    (F := F) (f := fun u : ℝ => Real.exp (-u^2))
    (fun u : ℝ => Real.exp (-b*u^2))
    (Eventually.of_forall fun n => ((hcont n).aestronglyMeasurable.indicator measurableSet_Ioc))
    (by
      filter_upwards [hw,hW,hM,hwin,eventually_gt_atTop (0:ℕ),hA.eventually_ge_atTop 0] with n hwn hWn hMn hwinN hn hAn
      exact ae_of_all _ fun u => by
        dsimp [F]
        by_cases hu : u ∈ Ioc (-(A n)) (A n)
        · rw [indicator_of_mem hu,abs_of_nonneg (by dsimp [q,P]; positivity)]
          have h4 : 0≤pairMoment (g n) (w n) 4 := by
            unfold pairMoment
            exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => mul_nonneg (hwn i j) (by positivity)
          have habs : |u| ≤ A n := abs_le.mpr ⟨hu.1.le,hu.2⟩
          have hsq := (sq_le_sq₀ (abs_nonneg u) hAn).mpr habs
          rw [sq_abs] at hsq
          have huwin := (mul_le_mul_of_nonneg_right hsq h4).trans hwinN
          let m := pairMoment (g n) (w n) 2
          let t := u/s n
          let Q := ‖complexScore (g n) (w n) t‖^2
          have hn' : 0 < (n:ℝ) := by exact_mod_cast hn
          have hm : 0 < m := hMn
          have hs : 0 < s n := Real.sqrt_pos.mpr (by positivity)
          have hs2 : (s n)^2 = (n:ℝ)*m/2 := by
            dsimp [s,m]
            exact Real.sq_sqrt (by positivity)
          have hu2 : t^2*((n:ℝ)*m/2) = u^2 := by
            dsimp [t]
            rw [← hs2,div_pow]
            field_simp
          have htwin : t^2*pairMoment (g n) (w n) 4 ≤ 2*C*m := by
            apply (mul_le_mul_iff_of_pos_right (by positivity : 0 < (n:ℝ)*m/2)).mp
            calc
              t^2*pairMoment (g n) (w n) 4*((n:ℝ)*m/2) =
                  u^2*pairMoment (g n) (w n) 4 := by rw [mul_right_comm,hu2]
              _ ≤ C*(n:ℝ)*m^2 := huwin
              _ = 2*C*m*((n:ℝ)*m/2) := by ring
          have hq0 := (score_quartic (g n) (w n) hwn t).2
          rw [hWn,one_pow] at hq0
          change Q-(1-m*t^2/2) ≤ pairMoment (g n) (w n) 4*t^4/24 at hq0
          have he := mul_le_mul_of_nonneg_right htwin (by positivity : 0 ≤ t^2/24)
          have herror : pairMoment (g n) (w n) 4*t^4/24 ≤ 2*C*m*(t^2/24) := by
            convert he using 1
            ring
          have hQ : Q ≤ 1-b*m*t^2/2 := by
            dsimp [b]
            linarith only [hq0,herror]
          have huEq : m*t^2/2 = u^2/(n:ℝ) := by
            apply (mul_left_cancel₀ hn'.ne' : (n:ℝ)*_ = (n:ℝ)*_ → _)
            calc
              (n:ℝ)*(m*t^2/2) = t^2*((n:ℝ)*m/2) := by ring
              _ = u^2 := hu2
              _ = (n:ℝ)*(u^2/(n:ℝ)) := by field_simp
          have hQ' : Q ≤ 1+(-b*u^2)/(n:ℝ) := by
            convert hQ using 1
            rw [show b*m*t^2/2 = b*(m*t^2/2) by ring,huEq]
            ring
          have hE := hQ'.trans (by simpa only [add_comm] using Real.add_one_le_exp ((-b*u^2)/(n:ℝ)))
          have hpow := pow_le_pow_left₀ (by dsimp [Q]; positivity) hE n
          rw [← Real.exp_nat_mul] at hpow
          have harg : (n:ℝ)*((-b*u^2)/(n:ℝ)) = -b*u^2 := by field_simp
          rw [harg] at hpow
          have hp : P n u ≤ Real.exp (-b*u^2) := by
            simpa [P,Q,t,pow_mul] using hpow
          have hq : q n u ≤ 1 := by
            dsimp [q]
            have he := (sq_le_sq₀ (abs_nonneg _) zero_le_one).mpr (Real.abs_sinc_le_one (ρ n*u/2))
            simpa only [sq_abs,one_pow] using he
          exact (mul_le_of_le_one_left (by dsimp [P]; positivity) hq).trans hp
        · rw [indicator_of_notMem hu,abs_zero]
          exact Real.exp_nonneg _)
    (by simpa [neg_mul] using (integrable_exp_neg_mul_sq (b := b) hb))
    (ae_of_all _ fun u => by
      have hP := score_gaussian_limit g w hw hW hM hR u
      have hsinc : Tendsto (fun n => ρ n*u/2) atTop (𝓝 0) := by
        simpa using (hρ.mul_const u).div_const 2
      have hq : Tendsto (fun n => q n u) atTop (𝓝 1) := by
        have h := ((Real.continuous_sinc.continuousAt.tendsto.comp hsinc).pow 2)
        simpa [q,Function.comp_def,Real.sinc_zero] using h
      have h := hq.mul hP
      rw [one_mul] at h
      apply h.congr'
      filter_upwards [hA.eventually_gt_atTop |u|] with n hn
      have hu : u ∈ Ioc (-(A n)) (A n) := ⟨by linarith [(abs_le.mp (le_refl |u|)).1], (le_abs_self u).trans hn.le⟩
      simp [F,hu,P,s])
  have hG : (∫ u : ℝ, Real.exp (-u^2)) = Real.sqrt Real.pi := by simpa using integral_gaussian 1
  rw [hG] at hlim
  have h := hlim.const_mul (1/(2*Real.pi))
  rw [show 1/(2*Real.pi)*Real.sqrt Real.pi = 1/(2*Real.sqrt Real.pi) by
    field_simp; nlinarith [Real.sq_sqrt Real.pi_pos.le]] at h
  apply h.congr'
  filter_upwards [hA.eventually_ge_atTop 0] with n hn
  dsimp [F]
  rw [integral_indicator measurableSet_Ioc,intervalIntegral.integral_of_le (by linarith : -(A n)≤A n)]

#print axioms central_fejer_gaussian_limit

end D5.S3.Fourier.Asymptotics.MovingFejerGaussianPrincipal
