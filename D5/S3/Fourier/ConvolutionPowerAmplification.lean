/- GID: D5/S3/Fourier/ConvolutionPowerAmplification
   generality: I
   mirror-B: D5/B/S3/Fourier/ConvolutionPowerAmplification
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Transform convolution powers and isolate a dominant double-centered packet. -/

/- Library-search audit trail (2026-09-01):
   * D5 searches for convolution powers, Fourier-Laplace powers, double-centered
     packets, and dominant complex powers found no equivalent declaration.
     `fourierLaplace_convolutionSquare_complex` treats only `g star involution g`;
     `leading_spectral_moment_recovery` treats nonnegative real spectral sums.
   * Pinned Mathlib has no iterated-convolution wrapper for this setting. The
     proof applies `integral_convolution` and
     `tendsto_pow_atTop_nhds_zero_of_norm_lt_one` directly.
   * The successor index is deliberate: `n + 1` means exactly `n + 1`
     convolution factors, without inventing a compactly supported identity at
     the zero-fold case.
-/

import D5.S3.Fourier.FourierLaplaceEntire
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic

namespace D5.S3.Fourier.ConvolutionPowerAmplification

open Filter MeasureTheory Topology
open D5.S3.Weil.Convention D5.S3.Weil.FourierLaplace D5.S3.Weil.TestFunctions
open scoped ComplexConjugate Convolution Pointwise

noncomputable section

private theorem twisted_integrable (g : WeilTestFunction) (z : ℂ) :
    Integrable (fun x : ℝ => fourierKernel z x * g x) := by
  have hkernel : Continuous (fun x : ℝ => fourierKernel z x) := by
    unfold fourierKernel
    fun_prop
  exact (hkernel.mul g.continuous).integrable_of_hasCompactSupport
    g.hasCompactSupport.mul_left

private theorem fourierKernel_add (z : ℂ) (x y : ℝ) :
    fourierKernel z (x + y) = fourierKernel z x * fourierKernel z y := by
  simp only [fourierKernel]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The complex Fourier-Laplace transform converts convolution into
multiplication. This is the general two-input form behind the existing
convolution-square specialization. -/
theorem fourierLaplace_convolve_complex (f g : WeilTestFunction) (z : ℂ) :
    fourierLaplace (convolve f g) z = fourierLaplace f z * fourierLaplace g z := by
  let F : ℝ → ℂ := fun x => fourierKernel z x * f x
  let G : ℝ → ℂ := fun x => fourierKernel z x * g x
  have hF : Integrable F := by
    simpa [F] using twisted_integrable f z
  have hG : Integrable G := by
    simpa [G] using twisted_integrable g z
  have hconvolution (x : ℝ) :
      (F ⋆[complexMul, volume] G) x = fourierKernel z x * convolve f g x := by
    rw [convolution_def]
    change (∫ t : ℝ,
      (fourierKernel z t * f t) * (fourierKernel z (x - t) * g (x - t))) =
        fourierKernel z x * (∫ t : ℝ, f t * g (x - t))
    rw [← integral_const_mul (fourierKernel z x)]
    apply integral_congr_ae
    filter_upwards with t
    calc
      (fourierKernel z t * f t) * (fourierKernel z (x - t) * g (x - t)) =
          (fourierKernel z t * fourierKernel z (x - t)) *
            (f t * g (x - t)) := by ring
      _ = fourierKernel z x * (f t * g (x - t)) := by
        rw [← fourierKernel_add z t (x - t)]
        congr 2
        ring
  calc
    fourierLaplace (convolve f g) z =
        ∫ x : ℝ, fourierKernel z x * convolve f g x := rfl
    _ = ∫ x : ℝ, (F ⋆[complexMul, volume] G) x := by
      apply integral_congr_ae
      filter_upwards with x
      exact (hconvolution x).symm
    _ = complexMul (∫ x : ℝ, F x) (∫ x : ℝ, G x) :=
      integral_convolution (L := complexMul) (ν := volume) (μ := volume) hF hG
    _ = fourierLaplace f z * fourierLaplace g z := rfl

/-- `convolutionSuccPower g n` contains exactly `n + 1` copies of `g`. -/
noncomputable def convolutionSuccPower (g : WeilTestFunction) : ℕ → WeilTestFunction
  | 0 => g
  | n + 1 => convolve (convolutionSuccPower g n) g

/-- The Fourier-Laplace transform of an `(n + 1)`-fold convolution is the
`(n + 1)`st power of the original transform. -/
theorem fourierLaplace_convolutionSuccPower (g : WeilTestFunction) (n : ℕ) (z : ℂ) :
    fourierLaplace (convolutionSuccPower g n) z = fourierLaplace g z ^ (n + 1) := by
  induction n with
  | zero => simp [convolutionSuccPower]
  | succ n ih =>
      simp only [convolutionSuccPower, fourierLaplace_convolve_complex, ih]
      simp [pow_succ]

/-- Radius-one support grows at most additively under repeated convolution. -/
theorem convolutionSuccPower_tsupport_subset
    (g : WeilTestFunction) (n : ℕ)
    (hsupport : tsupport (g : ℝ → ℂ) ⊆ Set.Ioo (-1) 1) :
    tsupport (convolutionSuccPower g n : ℝ → ℂ) ⊆
      Set.Ioo (-(n + 1 : ℝ)) (n + 1 : ℝ) := by
  induction n with
  | zero => simpa [convolutionSuccPower] using hsupport
  | succ n ih =>
      change tsupport (convolve (convolutionSuccPower g n) g : ℝ → ℂ) ⊆ _
      have hclosed :
          IsClosed (tsupport (convolutionSuccPower g n : ℝ → ℂ) +
            tsupport (g : ℝ → ℂ)) :=
        ((convolutionSuccPower g n).hasCompactSupport.isCompact.add
          g.hasCompactSupport.isCompact).isClosed
      refine (closure_minimal ((support_convolution_subset complexMul).trans ?_)
        hclosed).trans ?_
      · rintro x ⟨a, ha, b, hb, rfl⟩
        exact ⟨a, subset_tsupport _ ha, b, subset_tsupport _ hb, rfl⟩
      · rintro x ⟨a, ha, b, hb, rfl⟩
        have ha' := ih ha
        have hb' := hsupport hb
        simp only [Set.mem_Ioo] at ha' hb' ⊢
        push_cast
        constructor <;> linarith

/-- Real-valued inputs have a real-valued convolution. -/
theorem convolve_conj_eq_self
    (f g : WeilTestFunction)
    (hf : ∀ x, conj (f x) = f x) (hg : ∀ x, conj (g x) = g x) (x : ℝ) :
    conj (convolve f g x) = convolve f g x := by
  rw [convolve_apply, ← integral_conj]
  apply integral_congr_ae
  filter_upwards with y
  rw [map_mul, hf y, hg (x - y)]

/-- Repeated convolution preserves real-valuedness. -/
theorem convolutionSuccPower_conj_eq_self
    (g : WeilTestFunction) (hreal : ∀ x, conj (g x) = g x) (n : ℕ) :
    ∀ x, conj (convolutionSuccPower g n x) = convolutionSuccPower g n x := by
  induction n with
  | zero => exact hreal
  | succ n ih =>
      exact convolve_conj_eq_self (convolutionSuccPower g n) g ih hreal

/-- The compactly supported inverse packet `2 cos(t x) * g^(*(n+1))`. -/
noncomputable def doubleCenteredInverse
    (g : WeilTestFunction) (t : ℝ) (n : ℕ) : WeilTestFunction where
  toFun x := ((2 * Real.cos (t * x) : ℝ) : ℂ) * convolutionSuccPower g n x
  contDiff' := by
    apply ContDiff.mul
    · apply Complex.ofRealCLM.contDiff.comp
      exact contDiff_const.mul
        (Real.contDiff_cos.comp (contDiff_const.mul contDiff_id))
    · exact (convolutionSuccPower g n).contDiff
  hasCompactSupport' := by
    exact (convolutionSuccPower g n).hasCompactSupport.mul_left
  even' x := by
    rw [show t * -x = -(t * x) by ring, Real.cos_neg,
      (convolutionSuccPower g n).even]

@[simp]
theorem doubleCenteredInverse_apply
    (g : WeilTestFunction) (t : ℝ) (n : ℕ) (x : ℝ) :
    doubleCenteredInverse g t n x =
      ((2 * Real.cos (t * x) : ℝ) : ℂ) * convolutionSuccPower g n x :=
  rfl

private theorem fourierKernel_mul_two_cos (z : ℂ) (t x : ℝ) :
    fourierKernel z x * ((2 * Real.cos (t * x) : ℝ) : ℂ) =
      fourierKernel (z - (t : ℂ)) x + fourierKernel (z + (t : ℂ)) x := by
  simp only [fourierKernel]
  rw [Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.ofReal_cos,
    Complex.two_cos, mul_add]
  congr 1 <;> rw [← Complex.exp_add] <;> congr 1 <;> push_cast <;> ring

/-- The double-centered frequency packet formed from the transform powers. -/
noncomputable def doubleCenteredPowerPacket
    (g : WeilTestFunction) (t : ℝ) (N : ℕ) (z : ℂ) : ℂ :=
  fourierLaplace g (z - (t : ℂ)) ^ N + fourierLaplace g (z + (t : ℂ)) ^ N

/-- The double-centered packet is the sum of the two shifted transforms of the
repeated convolution history. -/
theorem doubleCenteredPowerPacket_eq_shifted_convolutionSuccPower
    (g : WeilTestFunction) (t : ℝ) (n : ℕ) (z : ℂ) :
    doubleCenteredPowerPacket g t (n + 1) z =
      fourierLaplace (convolutionSuccPower g n) (z - (t : ℂ)) +
        fourierLaplace (convolutionSuccPower g n) (z + (t : ℂ)) := by
  simp [doubleCenteredPowerPacket, fourierLaplace_convolutionSuccPower]

/-- The Fourier-Laplace transform of the cosine-modulated inverse function is
exactly the double-centered packet. -/
theorem fourierLaplace_doubleCenteredInverse
    (g : WeilTestFunction) (t : ℝ) (n : ℕ) (z : ℂ) :
    fourierLaplace (doubleCenteredInverse g t n) z =
      doubleCenteredPowerPacket g t (n + 1) z := by
  rw [doubleCenteredPowerPacket_eq_shifted_convolutionSuccPower]
  unfold fourierLaplace
  rw [← integral_add
    (twisted_integrable (convolutionSuccPower g n) (z - (t : ℂ)))
    (twisted_integrable (convolutionSuccPower g n) (z + (t : ℂ)))]
  apply integral_congr_ae
  filter_upwards with x
  rw [doubleCenteredInverse_apply]
  calc
    fourierKernel z x *
          (((2 * Real.cos (t * x) : ℝ) : ℂ) * convolutionSuccPower g n x) =
        (fourierKernel z x * ((2 * Real.cos (t * x) : ℝ) : ℂ)) *
          convolutionSuccPower g n x := by ring
    _ = (fourierKernel (z - (t : ℂ)) x + fourierKernel (z + (t : ℂ)) x) *
          convolutionSuccPower g n x := by rw [fourierKernel_mul_two_cos]
    _ = fourierKernel (z - (t : ℂ)) x * convolutionSuccPower g n x +
          fourierKernel (z + (t : ℂ)) x * convolutionSuccPower g n x := by ring

/-- The cosine modulation does not enlarge the convolution power's support. -/
theorem doubleCenteredInverse_tsupport_subset
    (g : WeilTestFunction) (t : ℝ) (n : ℕ)
    (hsupport : tsupport (g : ℝ → ℂ) ⊆ Set.Ioo (-1) 1) :
    tsupport (doubleCenteredInverse g t n : ℝ → ℂ) ⊆
      Set.Ioo (-(n + 1 : ℝ)) (n + 1 : ℝ) := by
  refine (tsupport_mul_subset_right (f := fun x : ℝ =>
    ((2 * Real.cos (t * x) : ℝ) : ℂ))
    (g := fun x : ℝ => convolutionSuccPower g n x)).trans ?_
  exact convolutionSuccPower_tsupport_subset g n hsupport

/-- A real convolution history gives a real cosine-modulated inverse packet. -/
theorem doubleCenteredInverse_conj_eq_self
    (g : WeilTestFunction) (t : ℝ) (n : ℕ)
    (hreal : ∀ x, conj (g x) = g x) (x : ℝ) :
    conj (doubleCenteredInverse g t n x) = doubleCenteredInverse g t n x := by
  rw [doubleCenteredInverse_apply, map_mul,
    Complex.conj_ofReal, convolutionSuccPower_conj_eq_self g hreal]

/-- Even test functions have an even Fourier-Laplace transform on the entire
complex plane. -/
theorem fourierLaplace_even_complex (g : WeilTestFunction) (z : ℂ) :
    fourierLaplace g (-z) = fourierLaplace g z := by
  unfold fourierLaplace
  rw [← integral_neg_eq_self (fun x : ℝ => fourierKernel (-z) x * g x) volume]
  apply integral_congr_ae
  filter_upwards with x
  rw [g.even]
  congr 1
  simp only [fourierKernel]
  congr 1
  push_cast
  ring

/-- Every double-centered power packet is even. -/
theorem doubleCenteredPowerPacket_even
    (g : WeilTestFunction) (t : ℝ) (N : ℕ) (z : ℂ) :
    doubleCenteredPowerPacket g t N (-z) = doubleCenteredPowerPacket g t N z := by
  unfold doubleCenteredPowerPacket
  rw [show -z - (t : ℂ) = -(z + (t : ℂ)) by ring,
    show -z + (t : ℂ) = -(z - (t : ℂ)) by ring,
    fourierLaplace_even_complex, fourierLaplace_even_complex, add_comm]

/-- Every double-centered power packet is entire. -/
theorem doubleCenteredPowerPacket_entire (g : WeilTestFunction) (t : ℝ) (N : ℕ) :
    Differentiable ℂ (doubleCenteredPowerPacket g t N) := by
  apply Differentiable.add
  · exact ((fourierLaplace_entire g).comp
      (differentiable_id.sub (differentiable_const (c := (t : ℂ))))).pow N
  · exact ((fourierLaplace_entire g).comp
      (differentiable_id.add (differentiable_const (c := (t : ℂ))))).pow N

/-- A dominant complex power plus a strictly smaller complex power is
asymptotic to the dominant power after normalization. -/
theorem dominant_power_sum_normalized_tendsto_one
    (q r : ℂ) (hq : q ≠ 0) (hr : ‖r / q‖ < 1) :
    Tendsto (fun n : ℕ => (q ^ (n + 1) + r ^ (n + 1)) / q ^ (n + 1))
      atTop (nhds 1) := by
  have hpower : Tendsto (fun n : ℕ => (r / q) ^ (n + 1)) atTop (nhds 0) :=
    (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hr).comp (tendsto_add_atTop_nat 1)
  have hsum : Tendsto (fun n : ℕ => (1 : ℂ) + (r / q) ^ (n + 1))
      atTop (nhds 1) := by
    simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℂ)) atTop (nhds 1)).add
      hpower
  exact hsum.congr' (Filter.Eventually.of_forall fun n => by
    symm
    change (q ^ (n + 1) + r ^ (n + 1)) / q ^ (n + 1) =
      1 + (r / q) ^ (n + 1)
    rw [add_div, div_self (pow_ne_zero _ hq), ← div_pow])

/-- At the target `t + i delta`, strict triangle separation makes the side
packet negligible relative to the amplified main value `q0^(n+1)`. -/
theorem double_centered_convolution_power_amplification
    (g : WeilTestFunction) (t delta q0 : ℝ)
    (_ht : t ≠ 0) (_hdelta : 0 < delta)
    (hmain : fourierLaplace g (Complex.I * (delta : ℂ)) = (q0 : ℂ))
    (hq0 : 1 < q0)
    (hstrict :
      ‖fourierLaplace g (2 * (t : ℂ) + Complex.I * (delta : ℂ))‖ < q0) :
    Tendsto
      (fun n : ℕ =>
        doubleCenteredPowerPacket g t (n + 1)
            ((t : ℂ) + Complex.I * (delta : ℂ)) /
          (q0 : ℂ) ^ (n + 1))
      atTop (nhds 1) := by
  have hq0pos : 0 < q0 := zero_lt_one.trans hq0
  have hq0ne : (q0 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hq0pos.ne'
  have hratio :
      ‖fourierLaplace g (2 * (t : ℂ) + Complex.I * (delta : ℂ)) / (q0 : ℂ)‖ < 1 := by
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hq0pos.le, div_lt_one hq0pos]
    exact hstrict
  apply (dominant_power_sum_normalized_tendsto_one
    (q0 : ℂ)
    (fourierLaplace g (2 * (t : ℂ) + Complex.I * (delta : ℂ)))
    hq0ne hratio).congr'
  exact Filter.Eventually.of_forall fun n => by
    unfold doubleCenteredPowerPacket
    rw [show (t : ℂ) + Complex.I * (delta : ℂ) - (t : ℂ) =
      Complex.I * (delta : ℂ) by ring,
      show (t : ℂ) + Complex.I * (delta : ℂ) + (t : ℂ) =
        2 * (t : ℂ) + Complex.I * (delta : ℂ) by ring,
      hmain]

/- The first witness has ratio norm `1/2`, so the normalized sums tend to one. -/
example : ‖(1 : ℂ) / 2‖ = (1 : ℝ) / 2 ∧
    Tendsto
      (fun n : ℕ =>
        ((2 : ℂ) ^ (n + 1) + (1 : ℂ) ^ (n + 1)) / (2 : ℂ) ^ (n + 1))
      atTop (nhds 1) := by
  constructor
  · norm_num
  · apply dominant_power_sum_normalized_tendsto_one
    · norm_num
    · norm_num

/- When both powers have base one, the strict ratio premise fails with norm
one and the normalized sum is constantly two rather than tending to one. -/
example : ‖(1 : ℂ) / 1‖ = 1 ∧
    ¬Tendsto
      (fun n : ℕ =>
        ((1 : ℂ) ^ (n + 1) + (1 : ℂ) ^ (n + 1)) / (1 : ℂ) ^ (n + 1))
      atTop (nhds 1) := by
  constructor
  · norm_num
  · simp only [one_pow, div_one]
    rw [tendsto_const_nhds_iff]
    norm_num

#print axioms double_centered_convolution_power_amplification

end


end D5.S3.Fourier.ConvolutionPowerAmplification
