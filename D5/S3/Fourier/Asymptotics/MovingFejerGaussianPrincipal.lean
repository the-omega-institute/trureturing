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

/-- The quartic estimate controls the power even with a point-dependent cutoff coefficient. -/
private theorem score_power_cutoff {J : Type*} [Fintype J] (g w : J → ℝ)
    (hw : ∀ i j, 0≤w i*w j) (hW : ∑ j,w j=1) (n : ℕ) (hn : 0<n)
    (hM : 0<pairMoment g w 2) (u C : ℝ)
    (hwin : u^2*pairMoment g w 4 ≤ C*(n:ℝ)*pairMoment g w 2^2) :
    ‖complexScore g w (u/Real.sqrt ((n:ℝ)*pairMoment g w 2/2))‖^(2*n) ≤
      Real.exp (-(1-C/6)*u^2) := by
  let s := Real.sqrt ((n:ℝ)*pairMoment g w 2/2)
  let b := 1-C/6
  let m := pairMoment g w 2
  let t := u/s
  let Q := ‖complexScore g w t‖^2
  have hn' : 0 < (n:ℝ) := by exact_mod_cast hn
  have hm : 0 < m := hM
  have hs : 0 < s := Real.sqrt_pos.mpr (by positivity)
  have hs2 : (s)^2 = (n:ℝ)*m/2 := by
    dsimp [s,m]
    exact Real.sq_sqrt (by positivity)
  have hu2 : t^2*((n:ℝ)*m/2) = u^2 := by
    dsimp [t]
    rw [← hs2,div_pow]
    field_simp
  have htwin : t^2*pairMoment g w 4 ≤ 2*C*m := by
    apply (mul_le_mul_iff_of_pos_right (by positivity : 0 < (n:ℝ)*m/2)).mp
    calc
      t^2*pairMoment g w 4*((n:ℝ)*m/2) =
          u^2*pairMoment g w 4 := by rw [mul_right_comm,hu2]
      _ ≤ C*(n:ℝ)*m^2 := hwin
      _ = 2*C*m*((n:ℝ)*m/2) := by ring
  have hq0 := (score_quartic g w hw t).2
  rw [hW,one_pow] at hq0
  change Q-(1-m*t^2/2) ≤ pairMoment g w 4*t^4/24 at hq0
  have he := mul_le_mul_of_nonneg_right htwin (by positivity : 0 ≤ t^2/24)
  have herror : pairMoment g w 4*t^4/24 ≤ 2*C*m*(t^2/24) := by
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
  rw [pow_mul]
  exact hpow

/-- The normalized Fejer moment restricted to a strict fourth-moment window. -/
private theorem central_fejer_gaussian_limit_lt {J : ℕ → Type*} [∀ n,Fintype (J n)] (g w : ∀ n,J n → ℝ)
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
          have hp := score_power_cutoff (g n) (w n) hwn hWn n hn hMn u C huwin
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

/-- A fixed exponential boundary-layer estimate on the outer half-window. -/
private theorem outer_half_bound (f : ℝ → ℝ) (hf : Continuous f) (a : ℝ) (ha : 0<a)
    (hb : ∀ u ∈ Icc (a/2) a, f u ≤ Real.exp (-(a/4)*(a-u))) :
    (∫ u in a/2..a, f u) ≤ 4/a := by
  have hle : a/2 ≤ a := by linarith
  let e := fun u : ℝ => Real.exp (-(a/4)*(a-u))
  have he : Continuous e := by dsimp [e]; fun_prop
  apply (intervalIntegral.integral_mono_on hle (hf.intervalIntegrable _ _)
    (he.intervalIntegrable _ _) hb).trans
  have hchange := intervalIntegral.integral_comp_sub_left (fun v : ℝ => Real.exp (-(a/4)*v)) a
    (a := a/2) (b := a)
  change (∫ u in a/2..a, e u) = _ at hchange
  rw [sub_self,show a-a/2 = a/2 by ring] at hchange
  rw [hchange]
  have hscale := intervalIntegral.smul_integral_comp_mul_left (f := Real.exp) (a := 0) (b := a/2) (c := -(a/4))
  rw [smul_eq_mul,mul_zero,integral_exp,Real.exp_zero] at hscale
  have hpos := Real.exp_nonneg (-(a/4)*(a/2))
  by_contra! hn
  have hh := mul_lt_mul_of_pos_left hn (show 0<a/4 by linarith)
  have heq : a/4*(4/a) = 1 := by field_simp
  linarith only [hh,hscale,hpos,heq]


/-- The normalized Fejer moment on a growing window, including the quartic cutoff endpoint. -/
theorem central_fejer_gaussian_limit {J : ℕ → Type*} [∀ n,Fintype (J n)] (g w : ∀ n,J n → ℝ)
    (hw : ∀ᶠ n in atTop, ∀ i j, 0≤w n i*w n j) (hW : ∀ᶠ n in atTop, ∑ j,w n j=1)
    (hM : ∀ᶠ n in atTop, 0<pairMoment (g n) (w n) 2)
    (ρ A : ℕ → ℝ) (hρ : Tendsto ρ atTop (𝓝 0)) (hA : Tendsto A atTop atTop)
    (hwin : ∀ᶠ n in atTop, A n^2*pairMoment (g n) (w n) 4 ≤ 6*(n:ℝ)*pairMoment (g n) (w n) 2^2) :
    let kernel := fun z : ℝ => Real.sinc z^2
    Tendsto (fun n => (1/(2*Real.pi))*(∫ u in -(A n)..A n,
      kernel (ρ n*u/2) * ‖complexScore (g n) (w n)
        (u/Real.sqrt ((n:ℝ)*pairMoment (g n) (w n) 2/2))‖^(2*n)))
      atTop (𝓝 (1/(2*Real.sqrt Real.pi))) := by
  intro kernel
  let B := fun n => A n/2
  let s := fun n : ℕ => Real.sqrt ((n:ℝ)*pairMoment (g n) (w n) 2/2)
  let f := fun n u => Real.sinc (ρ n*u/2)^2 * ‖complexScore (g n) (w n) (u/s n)‖^(2*n)
  have hB : Tendsto B atTop atTop := by
    simpa [B,div_eq_mul_inv] using hA.atTop_mul_const (by norm_num : 0<(2:ℝ)⁻¹)
  have hBwin : ∀ᶠ n in atTop, B n^2*pairMoment (g n) (w n) 4 ≤
      3*(n:ℝ)*pairMoment (g n) (w n) 2^2 := by
    filter_upwards [hwin] with n hn
    dsimp [B]
    nlinarith only [hn,show 0≤(n:ℝ)*pairMoment (g n) (w n) 2^2 by positivity]
  have hinner := central_fejer_gaussian_limit_lt g w hw hW hM ρ B hρ hB 3 (by norm_num) hBwin
  have hf (n : ℕ) : Continuous (f n) := by
    dsimp [f]
    apply Continuous.mul
    · exact (Real.continuous_sinc.comp (by fun_prop)).pow 2
    · exact ((complexScore_continuous (g n) (w n)).comp (by fun_prop)).norm.pow _
  have hfn (n : ℕ) (u : ℝ) : 0 ≤ f n u := by dsimp [f]; positivity
  have hpoint : ∀ᶠ n in atTop, ∀ u ∈ Icc (B n) (A n),
      f n u ≤ Real.exp (-(A n/4)*(A n-u)) ∧
      f n (-u) ≤ Real.exp (-(A n/4)*(A n-u)) := by
    filter_upwards [hw,hW,hM,hwin,eventually_gt_atTop (0:ℕ),hA.eventually_gt_atTop 0] with n hwn hWn hMn hwinN hn hAn
    intro u hu
    have hu0 : 0 ≤ u := le_trans (by dsimp [B]; positivity) hu.1
    have hhalf : A n/2 ≤ u := hu.1
    have hden : 0 < (A n)^2 := by positivity
    let c := 6*(u/(A n))^2
    have hcut : u^2*pairMoment (g n) (w n) 4 ≤ c*(n:ℝ)*pairMoment (g n) (w n) 2^2 := by
      apply (mul_le_mul_iff_of_pos_right hden).mp
      have hb := mul_le_mul_of_nonneg_left hwinN (sq_nonneg u)
      calc
        u^2*pairMoment (g n) (w n) 4*A n^2 = u^2*(A n^2*pairMoment (g n) (w n) 4) := by ring
        _ ≤ u^2*(6*(n:ℝ)*pairMoment (g n) (w n) 2^2) := hb
        _ = c*(n:ℝ)*pairMoment (g n) (w n) 2^2*A n^2 := by
          dsimp [c]; field_simp
    have hcutneg : (-u)^2*pairMoment (g n) (w n) 4 ≤ c*(n:ℝ)*pairMoment (g n) (w n) 2^2 := by
      simpa only [neg_sq] using hcut
    have hratio : 1-u^2/A n^2 ≥ (A n-u)/A n := by
      apply sub_nonneg.mp
      have hmul := mul_nonneg hu0 (sub_nonneg.mpr hu.2)
      have he : 1-u^2/A n^2-(A n-u)/A n = u*(A n-u)/A n^2 := by
        field_simp; ring
      rw [he]
      exact div_nonneg hmul (sq_nonneg _)
    have hsqhalf : (A n/2)^2 ≤ u^2 := (sq_le_sq₀ (by positivity) hu0).mpr hhalf
    have hexp : -(1-c/6)*u^2 ≤ -(A n/4)*(A n-u) := by
      have he : 1-c/6 = 1-u^2/A n^2 := by dsimp [c]; rw [div_pow]; ring
      rw [he]
      have hd : 0≤(A n-u)/A n := div_nonneg (sub_nonneg.mpr hu.2) hAn.le
      have hh := mul_le_mul_of_nonneg_right hratio (sq_nonneg u)
      have hh2 := mul_le_mul_of_nonneg_left hsqhalf hd
      have hh3 : (A n-u)/A n*(A n/2)^2 = A n/4*(A n-u) := by
        field_simp; ring
      rw [hh3] at hh2
      linarith
    have hpos := score_power_cutoff (g n) (w n) hwn hWn n hn hMn u c hcut
    have hneg := score_power_cutoff (g n) (w n) hwn hWn n hn hMn (-u) c hcutneg
    rw [neg_sq] at hneg
    have hq (v : ℝ) : Real.sinc (ρ n*v/2)^2 ≤ 1 := by
      have he := (sq_le_sq₀ (abs_nonneg _) zero_le_one).mpr (Real.abs_sinc_le_one (ρ n*v/2))
      simpa only [sq_abs,one_pow] using he
    have hbound (v : ℝ) (hp : ‖complexScore (g n) (w n) (v/s n)‖^(2*n) ≤
        Real.exp (-(1-c/6)*u^2)) : f n v ≤ Real.exp (-(A n/4)*(A n-u)) := by
      dsimp [f]
      exact ((mul_le_of_le_one_left (by positivity) (hq v)).trans hp).trans (Real.exp_le_exp.mpr hexp)
    exact ⟨hbound u hpos,hbound (-u) hneg⟩
  let T := fun n => (∫ u in B n..A n,f n u) + (∫ u in -(A n)..-(B n),f n u)
  have hTbounds : ∀ᶠ n in atTop, 0≤T n ∧ T n ≤ 8/A n := by
    filter_upwards [hpoint,hA.eventually_gt_atTop 0] with n hn ha
    have hle : B n ≤ A n := by dsimp [B]; linarith
    have hp := outer_half_bound (f n) (hf n) (A n) ha (fun u hu => (hn u hu).1)
    have hm := outer_half_bound (fun u => f n (-u)) ((hf n).comp continuous_neg)
      (A n) ha (fun u hu => (hn u hu).2)
    rw [intervalIntegral.integral_comp_neg] at hm
    change (∫ u in B n..A n, f n u) ≤ _ at hp
    change (∫ u in -(A n)..-(B n), f n u) ≤ _ at hm
    dsimp [T]
    constructor
    · exact add_nonneg (intervalIntegral.integral_nonneg hle (fun u _ => hfn n u))
        (intervalIntegral.integral_nonneg (by linarith) (fun u _ => hfn n u))
    · exact (add_le_add hp hm).trans_eq (by ring)
  have hT : Tendsto T atTop (𝓝 0) := by
    apply squeeze_zero' (hTbounds.mono fun _ h => h.1) (hTbounds.mono fun _ h => h.2)
    simpa [div_eq_mul_inv] using (tendsto_inv_atTop_zero.comp hA).const_mul 8
  have hh := hinner.add (hT.const_mul (1/(2*Real.pi)))
  rw [mul_zero,add_zero] at hh
  apply hh.congr'
  filter_upwards [] with n
  change 1/(2*Real.pi)*(∫ u in -(B n)..B n,f n u) + 1/(2*Real.pi)*T n =
    1/(2*Real.pi)*(∫ u in -(A n)..A n,f n u)
  dsimp [T]
  have hleft := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    ((hf n).intervalIntegrable (-(A n)) (-(B n))) ((hf n).intervalIntegrable (-(B n)) (B n))
  have hright := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    ((hf n).intervalIntegrable (-(A n)) (B n)) ((hf n).intervalIntegrable (B n) (A n))
  have hwhole : (∫ u in -(A n)..A n,f n u) =
      (∫ u in -(A n)..-(B n),f n u)+(∫ u in -(B n)..B n,f n u)+(∫ u in B n..A n,f n u) := by
    rw [hleft,hright]
  rw [hwhole]
  ring

#print axioms central_fejer_gaussian_limit

end D5.S3.Fourier.Asymptotics.MovingFejerGaussianPrincipal
