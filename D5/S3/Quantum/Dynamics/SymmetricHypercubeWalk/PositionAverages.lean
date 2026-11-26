/- GID: D5/S3/Quantum/Dynamics/SymmetricHypercubeWalk/PositionAverages
   generality: I
   mirror-B: D5/B/S3/Quantum/Dynamics/SymmetricHypercubeWalk/PositionAverages
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The normalized position Cesàro laws and their finite Walsh coefficients. -/

import D5.S3.Quantum.Dynamics.SymmetricHypercubeWalk.Walk

/-! Position masses and their Cesàro limits, followed by the Walsh observable. -/

section

open Filter
open scoped BigOperators Matrix Topology Interval

set_option autoImplicit false

namespace HypercubeWalsh

variable {d : ℕ} (K : Kernel (Cube d))

noncomputable def continuousMass (t : ℝ) (x : Cube d) : ℝ := ‖continuousState K t x‖ ^ 2

noncomputable def discreteMass (n : ℕ) (x : Cube d) : ℝ :=
  ∑ y, discreteState K n y x ^ 2

theorem discreteMass_eq_complex (n : ℕ) (x : Cube d) :
    discreteMass K n x = ∑ y, ‖discreteComplexState K n y x‖ ^ 2 := by
  simp [discreteMass, discreteComplexState_eq_ofReal, Complex.norm_real, Real.norm_eq_abs, sq_abs]

noncomputable def positionExpansion (f : Cube d → Cube d → ℝ) (x : Cube d) : ℝ :=
  ((2 : ℝ) ^ d)⁻¹ * ∑ a, ∑ b, (basis a x * basis b x) * f a b

noncomputable def continuousCoinPair (a b : Cube d) (t : ℝ) : ℂ :=
  continuousPair (eigen K a) (eigen K b) t

noncomputable def discreteCoinPair (a b : Cube d) (n : ℕ) : ℝ :=
  K.discretePair (characterBit a) (characterBit b) n

private theorem continuousMass_fourier (t : ℝ) (x : Cube d) :
    continuousMass K t x =
      positionExpansion (fun a b => (continuousCoinPair K a b t).re) x := by
  let f : Cube d → ℂ := fun a => (basis a x : ℂ) * continuousBlock (eigen K a) t
  have hnorm (z : ℂ) : ‖z‖ ^ 2 = ((starRingEnd ℂ) z * z).re := by
    rw [mul_comm, Complex.mul_conj, Complex.ofReal_re, Complex.sq_norm]
  rw [continuousMass, continuousState_fourier, hnorm]
  change ((starRingEnd ℂ) ((scale d : ℂ) * ∑ a, f a) * ((scale d : ℂ) * ∑ b, f b)).re = _
  rw [map_mul, Complex.conj_ofReal, mul_mul_mul_comm, ← Complex.ofReal_mul, ← pow_two, scale_sq,
    Complex.re_ofReal_mul, map_sum, Finset.sum_mul_sum]
  unfold positionExpansion
  congr 1
  simp only [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  change ((starRingEnd ℂ) (f a) * f b).re = _
  simp only [f, map_mul, Complex.conj_ofReal]
  rw [mul_mul_mul_comm, ← Complex.ofReal_mul, Complex.re_ofReal_mul]
  rfl

private theorem discreteMass_fourier (n : ℕ) (x : Cube d) :
    discreteMass K n x = positionExpansion (fun a b => discreteCoinPair K a b n) x := by
  simp only [discreteMass, discreteState_fourier, mul_pow, scale_sq]
  rw [← Finset.mul_sum]
  simp only [pow_two, Finset.sum_mul_sum]
  unfold positionExpansion
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  simp only [discreteCoinPair, Kernel.discretePair, dotProduct, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  ring

noncomputable def continuousRealMean (f : ℝ → ℝ) (T : ℝ) : ℝ :=
  T⁻¹ * ∫ t in (0 : ℝ)..T, f t

private theorem continuousCoinPair_continuous (a b : Cube d) :
    Continuous (continuousCoinPair K a b) := by
  change Continuous (fun t => continuousPair (eigen K a) (eigen K b) t)
  simp only [continuousPair_eq, phase]
  fun_prop

private theorem continuousRealMean_pair (a b : Cube d) (T : ℝ) :
    continuousRealMean (fun t => (continuousCoinPair K a b t).re) T =
      (continuousMean (continuousCoinPair K a b) T).re := by
  have h := Complex.reCLM.intervalIntegral_comp_comm
    ((continuousCoinPair_continuous K a b).intervalIntegrable (μ := MeasureTheory.volume) 0 T)
  change (∫ t in (0 : ℝ)..T, (continuousCoinPair K a b t).re) = _ at h
  unfold continuousRealMean continuousMean
  rw [h, Complex.real_smul, Complex.re_ofReal_mul]
  rfl

private theorem discreteMean_positionExpansion (f : Cube d → Cube d → ℕ → ℝ)
    (T : ℕ) (x : Cube d) :
    discreteMean (fun n => positionExpansion (fun a b => f a b n) x) T =
      positionExpansion (fun a b => discreteMean (f a b) T) x := by
  unfold discreteMean positionExpansion
  rw [← Finset.mul_sum, mul_left_comm ((T : ℝ)⁻¹)]
  congr 1
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro n _
  ring

private theorem continuousRealMean_positionExpansion (f : Cube d → Cube d → ℝ → ℝ)
    (hf : ∀ a b, Continuous (f a b)) (T : ℝ) (x : Cube d) :
    continuousRealMean (fun t => positionExpansion (fun a b => f a b t) x) T =
      positionExpansion (fun a b => continuousRealMean (f a b) T) x := by
  unfold continuousRealMean positionExpansion
  rw [intervalIntegral.integral_const_mul, mul_left_comm (T⁻¹)]
  congr 1
  have hi (a b : Cube d) : Continuous (fun t => basis a x * basis b x * f a b t) :=
    (hf a b).const_mul _
  have hj (a : Cube d) : Continuous (fun t => ∑ b, basis a x * basis b x * f a b t) :=
    continuous_finsetSum _ (fun b _ => hi a b)
  rw [intervalIntegral.integral_finsetSum (fun a _ => (hj a).intervalIntegrable 0 T),
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [intervalIntegral.integral_finsetSum (fun b _ => (hi a b).intervalIntegrable 0 T),
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [intervalIntegral.integral_const_mul]
  ring

private theorem tendsto_positionExpansion {I : Type*} {l : Filter I}
    {f : Cube d → Cube d → I → ℝ} {g : Cube d → Cube d → ℝ}
    (h : ∀ a b, Tendsto (f a b) l (𝓝 (g a b))) (x : Cube d) :
    Tendsto (fun t => positionExpansion (fun a b => f a b t) x) l
      (𝓝 (positionExpansion g x)) := by
  apply Tendsto.const_mul
  apply tendsto_finsetSum
  intro a _
  apply tendsto_finsetSum
  intro b _
  exact (h a b).const_mul _

noncomputable def continuousAverage (x : Cube d) : ℝ :=
  positionExpansion (fun a b => K.continuousLimit (characterBit a) (characterBit b)) x

noncomputable def discreteAverage (x : Cube d) : ℝ :=
  positionExpansion (fun a b => K.discreteLimit (characterBit a) (characterBit b)) x

theorem tendsto_continuousAverage (x : Cube d) :
    Tendsto (continuousRealMean (fun t => continuousMass K t x)) atTop
      (𝓝 (continuousAverage K x)) := by
  have hf (a b : Cube d) :
      Tendsto (continuousRealMean (fun t => (continuousCoinPair K a b t).re)) atTop
        (𝓝 (K.continuousLimit (characterBit a) (characterBit b))) := by
    have h := (Complex.continuous_re.tendsto _).comp
      (tendsto_continuousPair (eigen K a) (eigen K b))
    change Tendsto (fun T : ℝ => (continuousMean (continuousCoinPair K a b) T).re) atTop _ at h
    simp_rw [← continuousRealMean_pair] at h
    by_cases he : K.eigenvalue (characterBit a) = K.eigenvalue (characterBit b) <;>
      simpa [Kernel.continuousLimit, eigen, he] using h
  have he (T : ℝ) : continuousRealMean (fun t => continuousMass K t x) T =
      positionExpansion
        (fun a b => continuousRealMean (fun t => (continuousCoinPair K a b t).re) T) x := by
    simp only [continuousMass_fourier]
    exact continuousRealMean_positionExpansion _ (fun a b =>
      Complex.continuous_re.comp (continuousCoinPair_continuous K a b)) T x
  simpa only [← he, continuousAverage] using tendsto_positionExpansion hf x

theorem tendsto_discreteAverage (x : Cube d) :
    Tendsto (discreteMean (fun n => discreteMass K n x)) atTop
      (𝓝 (discreteAverage K x)) := by
  have he (T : ℕ) : discreteMean (fun n => discreteMass K n x) T =
      positionExpansion (fun a b => discreteMean (discreteCoinPair K a b) T) x := by
    simp only [discreteMass_fourier]
    exact discreteMean_positionExpansion _ T x
  have hf (a b : Cube d) : Tendsto (discreteMean (discreteCoinPair K a b)) atTop
      (𝓝 (K.discreteLimit (characterBit a) (characterBit b))) :=
    K.tendsto_discretePair (characterBit a) (characterBit b)
  simpa only [← he, discreteAverage] using tendsto_positionExpansion hf x

noncomputable def walshCoefficient (p : Cube d → ℝ) (c : Cube d) : ℝ :=
  ∑ x, character c x * p x

private theorem walshCoefficient_positionExpansion (f : Cube d → Cube d → ℝ) (c : Cube d) :
    walshCoefficient (positionExpansion f) c =
      ((2 : ℝ) ^ d)⁻¹ * ∑ a, f a (xor a c) := by
  unfold walshCoefficient positionExpansion
  have hp (x : Cube d) :
      character c x * (((2 : ℝ) ^ d)⁻¹ * ∑ a, ∑ b, (basis a x * basis b x) * f a b) =
        ((2 : ℝ) ^ d)⁻¹ * ∑ a, ∑ b, basis a x * basis b x * f a b * character c x := by
    rw [mul_left_comm, mul_comm (character c x)]
    simp only [Finset.sum_mul]
  simp only [hp, ← Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]
  have h (b : Cube d) :
      (∑ x, basis a x * basis b x * f a b * character c x) =
        if xor a c = b then f a b else 0 := by
    calc
      _ = (∑ x, basis (xor a c) x * basis b x) * f a b := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro x _
        rw [← basis_character_mul]
        ring
      _ = _ := by rw [basis_orthonormal]; split <;> simp
  simp_rw [h]
  simp

theorem continuousWalsh_eq (c : Cube d) :
    walshCoefficient (continuousAverage K) c =
      ((2 : ℝ) ^ d)⁻¹ * ∑ a, if eigen K a = eigen K (xor a c) then 1 else 0 := by
  unfold continuousAverage
  rw [walshCoefficient_positionExpansion]
  rfl

theorem finite_walsh_gap (c : Cube d) :
    walshCoefficient (continuousAverage K) c - walshCoefficient (discreteAverage K) c =
      ((2 : ℝ) ^ d)⁻¹ * ∑ a, gap K a c := by
  unfold continuousAverage discreteAverage
  rw [walshCoefficient_positionExpansion,
    walshCoefficient_positionExpansion, ← mul_sub, ← Finset.sum_sub_distrib]
  simp only [K.pair_limit_sub, pairGap_eq]

theorem continuousAverage_nonneg (x : Cube d) : 0 ≤ continuousAverage K x := by
  apply ge_of_tendsto (tendsto_continuousAverage K x)
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
  apply mul_nonneg (inv_nonneg.2 hT)
  exact intervalIntegral.integral_nonneg hT (fun t _ => sq_nonneg ‖continuousState K t x‖)

theorem discreteAverage_nonneg (x : Cube d) : 0 ≤ discreteAverage K x := by
  apply ge_of_tendsto (tendsto_discreteAverage K x)
  apply Filter.Eventually.of_forall
  intro T
  exact mul_nonneg (by positivity)
    (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)

theorem continuousAverage_total : ∑ x, continuousAverage K x = 1 := by
  have h := continuousWalsh_eq K origin
  simpa [walshCoefficient, cube_card, inv_mul_cancel₀ (by positivity : (2 : ℝ) ^ d ≠ 0)] using h

theorem discreteAverage_total : ∑ x, discreteAverage K x = 1 := by
  have hgap (a : Cube d) : gap K a origin = 0 := by
    have he : eigen K origin = 1 := by simp [eigen_eq, K.total]
    simp [gap, he]
  have h := finite_walsh_gap K origin
  simp [walshCoefficient, hgap, continuousAverage_total K] at h
  linarith

private theorem continuousMass_continuous (x : Cube d) :
    Continuous (fun t => continuousMass K t x) := by
  simp_rw [continuousMass_fourier, positionExpansion]
  apply Continuous.const_mul
  apply continuous_finsetSum
  intro a _
  apply continuous_finsetSum
  intro b _
  exact (Complex.continuous_re.comp (continuousCoinPair_continuous K a b)).const_mul _

theorem tendsto_continuousWalsh (c : Cube d) :
    Tendsto (continuousRealMean (fun t => walshCoefficient (continuousMass K t) c)) atTop
      (𝓝 (walshCoefficient (continuousAverage K) c)) := by
  have he (T : ℝ) :
      continuousRealMean (fun t => walshCoefficient (continuousMass K t) c) T =
        ∑ x, character c x * continuousRealMean (fun t => continuousMass K t x) T := by
    unfold walshCoefficient continuousRealMean
    rw [intervalIntegral.integral_finsetSum (fun x _ =>
      ((continuousMass_continuous K x).const_mul (character c x)).intervalIntegrable 0 T),
    Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    rw [intervalIntegral.integral_const_mul, mul_left_comm]
  have hlim : Tendsto (fun T : ℝ =>
      ∑ x, character c x * continuousRealMean (fun t => continuousMass K t x) T)
      atTop (𝓝 (walshCoefficient (continuousAverage K) c)) :=
    tendsto_finsetSum _ (fun x _ => (tendsto_continuousAverage K x).const_mul _)
  exact hlim.congr (fun T => (he T).symm)

theorem tendsto_discreteWalsh (c : Cube d) :
    Tendsto (discreteMean (fun n => walshCoefficient (discreteMass K n) c)) atTop
      (𝓝 (walshCoefficient (discreteAverage K) c)) := by
  have he (T : ℕ) :
      discreteMean (fun n => walshCoefficient (discreteMass K n) c) T =
        ∑ x, character c x * discreteMean (fun n => discreteMass K n x) T := by
    unfold walshCoefficient discreteMean
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring
  have hlim : Tendsto (fun T : ℕ =>
      ∑ x, character c x * discreteMean (fun n => discreteMass K n x) T)
      atTop (𝓝 (walshCoefficient (discreteAverage K) c)) :=
    tendsto_finsetSum _ (fun x _ => (tendsto_discreteAverage K x).const_mul _)
  exact hlim.congr (fun T => (he T).symm)

theorem tendsto_finite_walsh_gap (c : Cube d) :
    Tendsto (fun T : ℝ × ℕ =>
      continuousRealMean (fun t => walshCoefficient (continuousMass K t) c) T.1 -
        discreteMean (fun n => walshCoefficient (discreteMass K n) c) T.2)
      ((atTop : Filter ℝ) ×ˢ (atTop : Filter ℕ))
      (𝓝 (((2 : ℝ) ^ d)⁻¹ * ∑ a, gap K a c)) := by
  rw [← finite_walsh_gap]
  exact ((tendsto_continuousWalsh K c).comp tendsto_fst).sub
    ((tendsto_discreteWalsh K c).comp tendsto_snd)

theorem finite_walsh_gap_mem_Icc (c : Cube d) :
    walshCoefficient (continuousAverage K) c - walshCoefficient (discreteAverage K) c ∈
      Set.Icc (0 : ℝ) 1 := by
  rw [finite_walsh_gap]
  have h (a : Cube d) : gap K a c ∈ Set.Icc (0 : ℝ) 1 := by
    rw [← pairGap_eq]
    exact K.pairGap_mem_Icc _ _
  constructor
  · exact mul_nonneg (by positivity) (Finset.sum_nonneg (fun a _ => (h a).1))
  · calc
      _ ≤ ((2 : ℝ) ^ d)⁻¹ * ∑ _ : Cube d, (1 : ℝ) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun a _ => (h a).2) (by positivity)
      _ = 1 := by simp

end HypercubeWalsh

end
