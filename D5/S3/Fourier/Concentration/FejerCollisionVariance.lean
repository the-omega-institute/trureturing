/- GID: D5/S3/Fourier/Concentration/FejerCollisionVariance
   generality: G
   mirror-B: D5/B/S3/Fourier/Concentration/FejerCollisionVariance
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Positive angular Fejer smoothing gives a clipped Gaussian collision lower bound for arbitrary real frequency sums. -/

import D5.S3.Analytic.Fourier.AngularFejerKernel
import D5.S3.Fourier.Concentration.LatticeConvolutionVariance
import D5.S3.Fourier.Asymptotics.ClippedGaussianMinorant

/-! The compact frequency support of the Fejer kernel retains the near-collision band. -/

open MeasureTheory Finset Filter Set
open scoped Topology
open D5.S3.Fourier.Concentration.FiniteTailMomentMissingWindow
open D5.S3.Fourier.Concentration.FiniteSincCollisionMoment
open D5.S3.Fourier.Concentration.LatticeConvolutionVariance
open D5.S3.Fourier.Asymptotics.ClippedGaussianMinorant

noncomputable section

namespace D5.S3.Fourier.Concentration.FejerCollisionVariance

open D5.S3.Analytic.Fourier.AngularFejerKernel

private theorem kernel_cos_integrable {η : ℝ} (hη : 0 < η) (d : ℝ) :
    Integrable (fun t => K η t * Real.cos (d*t)) := by
  apply (fejer_law hη).2.1.mul_bdd (c := 1) (by fun_prop)
  exact ae_of_all _ fun t => by simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one (d*t)

private theorem kernel_cos_integral {η : ℝ} (hη : 0 < η) (d : ℝ) :
    (∫ t : ℝ, K η t * Real.cos (d*t)) = phi η d := by
  have h := cosine_convolution (fejer_law hη).2.1 (fejer_law hη).2.2.2.1 d 0
  have he (t : ℝ) : Real.cos (d*t)*K η (0-t) = K η t*Real.cos (d*t) := by
    rw [zero_sub, mul_comm]
    congr 1
    simp only [K,mul_neg,neg_div,Real.sinc_neg]
  simp only [he,mul_zero,Real.cos_zero,mul_one] at h
  exact h

private theorem kernel_pair_integrable {I : Type*} (s : Finset I) (x c : I → ℝ)
    {η : ℝ} (hη : 0 < η) :
    Integrable (fun t => K η t * pairCosineScore s x c t) := by
  simp_rw [pairCosineScore,mul_sum]
  refine integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => ?_
  have h := (kernel_cos_integrable hη (x i-x j)).const_mul (c i*c j)
  convert h using 1
  ext t
  ring

private theorem kernel_pair_integral {I : Type*} (s : Finset I) (x c : I → ℝ)
    {η : ℝ} (hη : 0 < η) :
    (∫ t : ℝ, K η t * pairCosineScore s x c t) =
      ∑ i ∈ s, ∑ j ∈ s, c i*c j*phi η (x i-x j) := by
  have he (t : ℝ) : K η t * pairCosineScore s x c t =
      ∑ i ∈ s, ∑ j ∈ s, (c i*c j)*(K η t*Real.cos ((x i-x j)*t)) := by
    simp only [pairCosineScore,mul_sum]
    apply sum_congr rfl
    intro i hi
    apply sum_congr rfl
    intro j hj
    ring
  simp_rw [he]
  rw [integral_finsetSum]
  · apply sum_congr rfl
    intro i hi
    rw [integral_finsetSum]
    · apply sum_congr rfl
      intro j hj
      rw [integral_const_mul,kernel_cos_integral hη]
    · intro j hj
      exact (kernel_cos_integrable hη _).const_mul _
  · intro i hi
    exact integrable_finsetSum _ fun j _ => (kernel_cos_integrable hη _).const_mul _

private theorem phi_le_indicator {η : ℝ} (hη : 0 < η) (d : ℝ) :
    phi η d ≤ if |d| ≤ η then 1 else 0 := by
  split_ifs with hd
  · unfold phi
    exact max_le zero_le_one (sub_le_self _ (div_nonneg (abs_nonneg _) hη.le))
  · rw [phi_eq_zero hη (le_of_not_ge hd)]

/-- The exact Fejer-weighted moment equals the compact triangular band sum.
For nonnegative original weights it is bounded by the closed near-collision mass. -/
theorem fejer_collision_comparison {J : Type*} [Fintype J] [DecidableEq J]
    (g w : J → ℝ) (p : ℕ) {η : ℝ} (hη : 0 < η) :
    let kernel := fun z : ℝ × ℝ => K z.1 z.2
    let s := piAntidiag univ p
    let x := monomialFrequency g
    let c := monomialWeight w
    let M := ∫ t : ℝ, kernel (η,t) * ‖complexScore g w t‖^(2*p)
    M = (∑ m ∈ s, ∑ n ∈ s, c m*c n*phi η (x m-x n)) ∧
      ((∀ j, 0 ≤ w j) → M ≤ tailCollisionMass g w p η) := by
  intro kernel s x c M
  have hidentity : M = ∑ m ∈ s, ∑ n ∈ s, c m*c n*phi η (x m-x n) := by
    dsimp [M,s,x,c]
    simp_rw [moment_eq_pair]
    exact kernel_pair_integral _ _ _ hη
  refine ⟨hidentity,?_⟩
  intro hw
  rw [hidentity]
  unfold tailCollisionMass nearCollisionMass
  apply sum_le_sum
  intro m hm
  apply sum_le_sum
  intro n hn
  have hmn : 0 ≤ c m*c n := mul_nonneg (monomialWeight_nonneg w hw m)
    (monomialWeight_nonneg w hw n)
  have h := mul_le_mul_of_nonneg_left (phi_le_indicator hη (x m-x n)) hmn
  simpa only [mul_ite,mul_one,mul_zero] using h

/-- Retain the variance minorant on any symmetric observation window. -/
theorem fejer_collision_variance_lower {J : Type*} [Fintype J] [DecidableEq J]
    (g w : J → ℝ) (hw : ∀ j, 0 ≤ w j) (a V : ℝ) (p : ℕ)
    {η : ℝ} (hη : 0 < η) {A : ℝ} (hA : 0 ≤ A)
    (hm : ∑ j, w j*(g j-a)^2 ≤ V*∑ j,w j) :
    let kernel := fun z : ℝ × ℝ => K z.1 z.2
    let W := ∑ j,w j
    W^(2*p)*(∫ t in -A..A, kernel (η,t)*(max 0 (1-V*t^2/2))^(2*p)) ≤
      tailCollisionMass g w p η := by
  intro kernel W
  have hk := (fejer_law hη).1
  have hpoint (t : ℝ) : W^(2*p)*(K η t*(max 0 (1-V*t^2/2))^(2*p)) ≤
      K η t*‖complexScore g w t‖^(2*p) := by
    have hs := (score_variance_lower g w hw a V t hm).1
    have hpow : W^(2*p)*(max 0 (1-V*t^2/2))^(2*p) ≤ ‖complexScore g w t‖^(2*p) := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (mul_nonneg (sum_nonneg fun j _ => hw j) (le_max_left _ _)) hs _
    calc
      _ = K η t * (W^(2*p)*(max 0 (1-V*t^2/2))^(2*p)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hpow (hk t)
  have hc : Continuous (fun t => W^(2*p)*(K η t*(max 0 (1-V*t^2/2))^(2*p))) :=
    continuous_const.mul ((K_continuous η).mul (by fun_prop))
  have hs : Continuous (fun t => K η t*‖complexScore g w t‖^(2*p)) :=
    (K_continuous η).mul ((complexScore_continuous g w).norm.pow _)
  have hwhole : Integrable (fun t => K η t*‖complexScore g w t‖^(2*p)) := by
    simp_rw [moment_eq_pair]
    exact kernel_pair_integrable _ _ _ hη
  calc
    _ = ∫ t in -A..A, W^(2*p)*(K η t*(max 0 (1-V*t^2/2))^(2*p)) :=
      (intervalIntegral.integral_const_mul _ _).symm
    _ ≤ ∫ t in -A..A, K η t*‖complexScore g w t‖^(2*p) :=
      intervalIntegral.integral_mono_on (by linarith) (hc.intervalIntegrable _ _)
        (hs.intervalIntegrable _ _) (fun t _ => hpoint t)
    _ ≤ ∫ t : ℝ, K η t*‖complexScore g w t‖^(2*p) := by
      rw [intervalIntegral.integral_of_le (by linarith : -A ≤ A)]
      exact setIntegral_le_integral hwhole (ae_of_all _ fun t =>
        mul_nonneg (hk t) (pow_nonneg (norm_nonneg _) _))
    _ ≤ _ := (fejer_collision_comparison g w p hη).2 hw


/-- A fixed positive collision radius gives an asymptotic lower coefficient for
arbitrary real frequencies. -/
theorem fejer_collision_asymptotic_lower {J : Type*} [Fintype J] [DecidableEq J]
    (g w : J → ℝ) (hw : ∀ j, 0 ≤ w j) (a V : ℝ) (hV : 0 < V)
    {η : ℝ} (hη : 0 < η) (hm : ∑ j, w j*(g j-a)^2 ≤ V*∑ j,w j)
    (ε : ℝ) (hε : 0 < ε) :
    let scaleReadout := fun z : ℕ × ℝ => Real.sqrt ((z.1:ℝ)*z.2)
    ∀ᶠ p : ℕ in atTop,
      (η/(2*Real.sqrt Real.pi)-ε)*(∑ j,w j)^(2*p) ≤
        scaleReadout (p,V)*tailCollisionMass g w p η := by
  intro scaleReadout
  let W := ∑ j,w j
  let c := η/(2*Real.pi) - ε/(2*Real.sqrt Real.pi)
  have hπ := Real.sqrt_pos.mpr Real.pi_pos
  have hc : c < K η 0 := by
    simp only [c,K,mul_zero,zero_div,Real.sinc_zero,one_pow,mul_one]
    linarith [div_pos hε (show 0 < 2*Real.sqrt Real.pi by positivity)]
  have hlocal : ∀ᶠ t in 𝓝 (0:ℝ), c < K η t :=
    ((K_continuous η).continuousAt.tendsto).eventually_const_lt hc
  obtain ⟨δ,hδ,hnear⟩ := Metric.eventually_nhds_iff.mp hlocal
  let A := δ/2
  have hA : 0 < A := by dsimp [A]; positivity
  have hkernel (t : ℝ) (ht : t ∈ Icc (-A) A) : c ≤ K η t := by
    apply (hnear ?_).le
    rw [Real.dist_eq,sub_zero]
    exact (abs_le.mpr ht).trans_lt (by dsimp [A]; linarith)
  let scale := fun p : ℕ => Real.sqrt ((p:ℝ)*V)
  let I := fun p : ℕ =>
    scale p * (∫ t in -A..A, (max 0 (1-V*t^2/2))^(2*p))
  have hR : Tendsto (fun p : ℕ => A*scale p) atTop atTop :=
    (Real.tendsto_sqrt_atTop.comp
      ((tendsto_natCast_atTop_atTop (R := ℝ)).atTop_mul_const hV)).const_mul_atTop hA
  have hI : Tendsto I atTop (𝓝 (Real.sqrt Real.pi)) := by
    have h := (clipped_gaussian_full_limit_iff (fun _ => V) (fun _ => A)
      (Eventually.of_forall fun _ => hV)).mpr hR
    rw [show (∫ u : ℝ, Real.exp (-u^2)) = Real.sqrt Real.pi by
      simpa using integral_gaussian 1] at h
    exact h
  have hcoef : c*Real.sqrt Real.pi = η/(2*Real.sqrt Real.pi)-ε/2 := by
    dsimp [c]
    field_simp
    nlinarith [Real.sq_sqrt Real.pi_pos.le]
  have hlim : Tendsto (fun p => c*I p) atTop
      (𝓝 (η/(2*Real.sqrt Real.pi)-ε/2)) := by
    rw [← hcoef]
    exact hI.const_mul c
  filter_upwards [hlim.eventually_const_lt
    (show η/(2*Real.sqrt Real.pi)-ε < η/(2*Real.sqrt Real.pi)-ε/2 by linarith)] with p hp
  have hci : Continuous (fun t : ℝ => c*(max 0 (1-V*t^2/2))^(2*p)) := by fun_prop
  have hki : Continuous (fun t : ℝ => K η t*(max 0 (1-V*t^2/2))^(2*p)) :=
    (K_continuous η).mul (by fun_prop)
  have hint : c*(∫ t in -A..A, (max 0 (1-V*t^2/2))^(2*p)) ≤
      ∫ t in -A..A, K η t*(max 0 (1-V*t^2/2))^(2*p) := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_mono_on (by linarith) (hci.intervalIntegrable _ _)
      (hki.intervalIntegrable _ _) (fun t ht =>
        mul_le_mul_of_nonneg_right (hkernel t ht) (pow_nonneg (le_max_left _ _) _))
  have hW : 0 ≤ W := sum_nonneg fun j _ => hw j
  have hs : 0 ≤ scale p := Real.sqrt_nonneg _
  change (η/(2*Real.sqrt Real.pi)-ε)*W^(2*p) ≤ scale p*tailCollisionMass g w p η
  calc
    _ ≤ (c*I p)*W^(2*p) := mul_le_mul_of_nonneg_right hp.le (pow_nonneg hW _)
    _ = scale p*(W^(2*p)*(c*(∫ t in -A..A, (max 0 (1-V*t^2/2))^(2*p)))) := by
      dsimp [I]
      ring
    _ ≤ scale p*(W^(2*p)*(∫ t in -A..A, K η t*(max 0 (1-V*t^2/2))^(2*p))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hint (pow_nonneg hW _)) hs
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (fejer_collision_variance_lower g w hw a V p hη hA.le hm) hs

#print axioms fejer_collision_comparison
#print axioms fejer_collision_variance_lower
#print axioms fejer_collision_asymptotic_lower

end D5.S3.Fourier.Concentration.FejerCollisionVariance
