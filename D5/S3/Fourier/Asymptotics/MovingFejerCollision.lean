/- GID: D5/S3/Fourier/Asymptotics/MovingFejerCollision
   generality: G
   mirror-B: D5/B/S3/Fourier/Asymptotics/MovingFejerCollision
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A simultaneous resolution and variance window gives a uniform collision lower coefficient for varying real spectra. -/

import D5.S3.Fourier.Concentration.FejerCollisionVariance

/-! A growing variance-scaled window can remain small on the collision-resolution scale. -/

open Filter MeasureTheory Finset Set
open scoped Topology
open D5.S3.Fourier.Asymptotics.ClippedGaussianMinorant
open D5.S3.Fourier.Concentration.FejerCollisionVariance
open D5.S3.Fourier.Concentration.FiniteSincCollisionMoment
open D5.S3.Analytic.Fourier.AngularFejerKernel

noncomputable section

namespace D5.S3.Fourier.Asymptotics.MovingFejerCollision

/-- The two window requirements are compatible exactly when resolution is small
relative to the root variance scale. -/
theorem exists_fejer_window_iff (V η : ℕ → ℝ) (hV : ∀ᶠ n in atTop, 0 < V n)
    (hη : ∀ᶠ n in atTop, 0 < η n) :
    let scaleReadout := fun z : ℕ × ℝ => Real.sqrt ((z.1:ℝ)*z.2)
    let scale := fun n => scaleReadout (n,V n)
    Tendsto (fun n => η n/scale n) atTop (𝓝 0) ↔
      ∃ A : ℕ → ℝ, (∀ᶠ n in atTop, 0 < A n) ∧
        Tendsto (fun n => A n*scale n) atTop atTop ∧
        Tendsto (fun n => η n*A n) atTop (𝓝 0) := by
  intro scaleReadout scale
  have hs : ∀ᶠ n in atTop, 0 < scale n := by
    filter_upwards [eventually_ge_atTop (1:ℕ),hV] with n hn hv
    exact Real.sqrt_pos.mpr (mul_pos (Nat.cast_pos.mpr hn) hv)
  constructor
  · intro hr
    let r := fun n => η n/scale n
    have hrpos : ∀ᶠ n in atTop, 0 < r n := by
      filter_upwards [hs,hη] with n hs' hη'
      exact div_pos hη' hs'
    let A := fun n => (scale n*Real.sqrt (r n))⁻¹
    have hsqrt : Tendsto (fun n => Real.sqrt (r n)) atTop (𝓝 0) := by
      simpa only [Function.comp_def,Real.sqrt_zero] using
        (Real.continuous_sqrt.continuousAt.tendsto.comp hr)
    have hsqrtpos : ∀ᶠ n in atTop, 0 < Real.sqrt (r n) :=
      hrpos.mono fun n hn => Real.sqrt_pos.mpr hn
    have hinv : Tendsto (fun n => (Real.sqrt (r n))⁻¹) atTop atTop :=
      tendsto_inv_nhdsGT_zero.comp (tendsto_nhdsWithin_iff.mpr ⟨hsqrt,hsqrtpos⟩)
    refine ⟨A,?_,hinv.congr' ?_,hsqrt.congr' ?_⟩
    · filter_upwards [hs,hsqrtpos] with n hn hq
      exact inv_pos.mpr (mul_pos hn hq)
    · filter_upwards [hs,hsqrtpos] with n hn hq
      dsimp [A]
      field_simp
    · filter_upwards [hs,hrpos,hsqrtpos] with n hn hr' hq
      have he : η n = scale n*r n := by
        dsimp [r]
        field_simp
      dsimp [A]
      rw [he]
      field_simp
      nlinarith [Real.sq_sqrt hr'.le]
  · rintro ⟨A,hA,hR,hsmall⟩
    have hi := tendsto_inv_atTop_zero.comp hR
    have h := hsmall.mul hi
    simp only [zero_mul] at h
    refine h.congr' ?_
    filter_upwards [hs,hA] with n hn ha
    dsimp [Function.comp_def]
    field_simp

/-- The threshold in the small-resolution regime is uniform over all finite
frequency families and all moment budgets at the prescribed scales. -/
theorem moving_fejer_uniform_lower (V η : ℕ → ℝ) (hV : ∀ᶠ n in atTop, 0 < V n)
    (hη : ∀ᶠ n in atTop, 0 < η n) :
    let scaleReadout := fun z : ℕ × ℝ => Real.sqrt ((z.1:ℝ)*z.2)
    let scale := fun n => scaleReadout (n,V n)
    Tendsto (fun n => η n/scale n) atTop (𝓝 0) →
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      ∀ {J : Type*} [Fintype J] [DecidableEq J] (g w : J → ℝ),
        (∀ j, 0 ≤ w j) → ∀ a : ℝ,
        (∑ j,w j*(g j-a)^2 ≤ V n*∑ j,w j) →
        (1/(2*Real.sqrt Real.pi)-ε)*η n*(∑ j,w j)^(2*n) ≤
          scale n*tailCollisionMass g w n (η n) := by
  intro scaleReadout scale hr ε hε
  obtain ⟨A,hA,hR,hsmall⟩ := (exists_fejer_window_iff V η hV hη).mp hr
  let c := 1/(2*Real.pi)-ε/(2*Real.sqrt Real.pi)
  let q := fun x : ℝ => (1/(2*Real.pi))*Real.sinc (x/2)^2
  have hq : Continuous q := by unfold q; fun_prop
  have hc : c < q 0 := by
    simp only [c,q,zero_div,Real.sinc_zero,one_pow,mul_one]
    linarith [div_pos hε (show 0 < 2*Real.sqrt Real.pi by positivity)]
  obtain ⟨δ,hδ,hnear⟩ := Metric.eventually_nhds_iff.mp
    (hq.continuousAt.tendsto.eventually_const_lt hc)
  let I := fun n : ℕ => scale n*
    (∫ t in -(A n)..A n, (max 0 (1-V n*t^2/2))^(2*n))
  have hI : Tendsto I atTop (𝓝 (Real.sqrt Real.pi)) := by
    have h := (clipped_gaussian_full_limit_iff V A hV).mpr hR
    rw [show (∫ u : ℝ, Real.exp (-u^2)) = Real.sqrt Real.pi by
      simpa using integral_gaussian 1] at h
    exact h
  have hcoef : c*Real.sqrt Real.pi = 1/(2*Real.sqrt Real.pi)-ε/2 := by
    dsimp [c]
    field_simp
    nlinarith [Real.sq_sqrt Real.pi_pos.le]
  have hlim : Tendsto (fun n => c*I n) atTop
      (𝓝 (1/(2*Real.sqrt Real.pi)-ε/2)) := by
    rw [← hcoef]
    exact hI.const_mul c
  filter_upwards [hlim.eventually_const_lt
    (show 1/(2*Real.sqrt Real.pi)-ε < 1/(2*Real.sqrt Real.pi)-ε/2 by linarith),
    hsmall.eventually_lt_const hδ,hη,hA] with n hn hnδ hηn hAn
  intro J _ _ g w hw a hm
  let W := ∑ j,w j
  have hkernel (t : ℝ) (ht : t ∈ Icc (-(A n)) (A n)) : c*η n ≤ K (η n) t := by
    have hdist : dist (η n*t) 0 < δ := by
      rw [Real.dist_eq,sub_zero,abs_mul,abs_of_pos hηn]
      exact (mul_le_mul_of_nonneg_left (abs_le.mpr ht) hηn.le).trans_lt hnδ
    have hsmall := mul_le_mul_of_nonneg_right (hnear hdist).le hηn.le
    convert hsmall using 1
    simp only [q,K]
    ring
  have hci : Continuous (fun t : ℝ => c*η n*(max 0 (1-V n*t^2/2))^(2*n)) := by fun_prop
  have hki : Continuous (fun t : ℝ => K (η n) t*(max 0 (1-V n*t^2/2))^(2*n)) :=
    (K_continuous _).mul (by fun_prop)
  have hint : c*η n*(∫ t in -(A n)..A n, (max 0 (1-V n*t^2/2))^(2*n)) ≤
      ∫ t in -(A n)..A n, K (η n) t*(max 0 (1-V n*t^2/2))^(2*n) := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_mono_on (by linarith) (hci.intervalIntegrable _ _)
      (hki.intervalIntegrable _ _) (fun t ht =>
        mul_le_mul_of_nonneg_right (hkernel t ht) (pow_nonneg (le_max_left _ _) _))
  have hW : 0 ≤ W := sum_nonneg fun j _ => hw j
  have hs : 0 ≤ scale n := Real.sqrt_nonneg _
  change (1/(2*Real.sqrt Real.pi)-ε)*η n*W^(2*n) ≤
    scale n*tailCollisionMass g w n (η n)
  calc
    _ ≤ (c*I n)*η n*W^(2*n) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hn.le hηn.le) (pow_nonneg hW _)
    _ = scale n*(W^(2*n)*(c*η n*(∫ t in -(A n)..A n, (max 0 (1-V n*t^2/2))^(2*n)))) := by
      dsimp [I]
      ring
    _ ≤ scale n*(W^(2*n)*(∫ t in -(A n)..A n, K (η n) t*(max 0 (1-V n*t^2/2))^(2*n))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hint (pow_nonneg hW _)) hs
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (fejer_collision_variance_lower g w hw a (V n) n hηn hAn.le hm) hs

#print axioms exists_fejer_window_iff
#print axioms moving_fejer_uniform_lower

end D5.S3.Fourier.Asymptotics.MovingFejerCollision
