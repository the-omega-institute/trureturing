/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/WholeFormula
   generality: G
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/WholeFormula
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The unconditional integrated explicit formula holds at every positive real point. -/
/- Complete explicit-formula source candidate; final admission pending.
   Exact unconditional integrated Mangoldt formula, all actual occurrences,
   every real y>0, and the complete trivial-zero correction.
   No explicit formula, arithmetic transform, zero mass or symmetry is a premise.
   The digamma supplier excludes all integers; frequency zero is therefore
   obtained from continuity of the actual L1 Fourier transform, not by applying
   that supplier outside its domain. No continuity at y=0 is asserted or used. -/
import D5.S3.Weil.Mertens.IntegratedExplicit.CompleteMangoldtLaplace
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Topology.ClusterPt

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open MeasureTheory Set Filter
open D5.S3.Arith.Robin.CompleteMertensPeak
open D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds
open D5.S3.Zeros.CompletedZeta
open scoped BigOperators Topology FourierTransform

namespace D5.S3.Weil.Mertens.IntegratedExplicit

private theorem line_half_integerComplement {t : ℝ} (ht : t ≠ 0) :
    transformLine t / 2 ∈ Complex.integerComplement := by
  rintro ⟨n, hn⟩
  have him : (transformLine t / 2).im = Real.pi * t := by
    simp [transformLine, div_eq_mul_inv] <;> ring
  have he := congrArg Complex.im hn
  simp only [Complex.intCast_im, him] at he
  exact (mul_ne_zero Real.pi_ne_zero ht) he.symm

/-- Digamma, coefficient mass and the complete correction are combined only
as absolutely convergent HasSum statements. -/
private theorem digamma_trivial_balance {t : ℝ} (ht : t ≠ 0) :
    (Complex.digamma (transformLine t / 2) / 2 +
        (Real.eulerMascheroniConstant : ℂ) / 2 + 1 / transformLine t) /
          transformLine t +
      (transformLine t - 1) *
        (∫ y : ℝ in Ioi 0, Complex.exp (-transformLine t * y) * (trivialT y : ℂ)) =
      (1 - Real.log 2 : ℝ) := by
  let s := transformLine t
  have hs0 : s ≠ 0 := by intro e; have := congrArg Complex.re e; simp [s] at this
  have hA : HasSum (fun n : ℕ =>
      1 / (2 * ((n : ℂ) + 1) * (s + 2 * ((n : ℂ) + 1))))
      ((Complex.digamma (s / 2) / 2 +
        (Real.eulerMascheroniConstant : ℂ) / 2 + 1 / s) / s) := by
    have hdig : HasSum (fun n : ℕ => 1 / ((n : ℂ) + 1) - 1 / (s / 2 + n + 1))
        (Complex.digamma (s / 2) + (Real.eulerMascheroniConstant : ℂ) + 1 / (s / 2)) :=
      Zeta23.DigammaSeries.hasSum_digamma_series (line_half_integerComplement ht)
    convert hdig.mul_right (1 / (2 * s)) using 1
    · funext n
      have hj : ((n : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero n
      have hsj : s + 2 * ((n : ℂ) + 1) ≠ 0 := by
        intro e
        have := congrArg Complex.re e
        simp [s] at this
        linarith [Nat.cast_nonneg (α := ℝ) n]
      rw [show s / 2 + (n : ℂ) + 1 = (s + 2 * ((n : ℂ) + 1)) / 2 by ring,
        one_div_div]
      field_simp [hj, hsj, hs0]
      <;> ring
    · field_simp [hs0]
      <;> ring
  have hR : HasSum (fun n : ℕ => (trivialCoeff n : ℂ) / (s + 2 * ((n : ℂ) + 1)))
      (∫ y : ℝ in Ioi 0, Complex.exp (-s * y) * (trivialT y : ℂ)) :=
    trivialT_laplace_hasSum (by simp [s] : 0 < s.re)
  have hc : HasSum (fun n : ℕ => (trivialCoeff n : ℂ))
      ((Complex.digamma (s / 2) / 2 +
        (Real.eulerMascheroniConstant : ℂ) / 2 + 1 / s) / s +
        (s - 1) * (∫ y : ℝ in Ioi 0,
          Complex.exp (-s * y) * (trivialT y : ℂ))) := by
    convert hA.add (hR.mul_left (s - 1)) using 1
    funext n
    let j : ℂ := (n : ℂ) + 1
    have hj : j ≠ 0 := Nat.cast_add_one_ne_zero n
    have hj1 : 2 * j + 1 ≠ 0 := by
      intro e
      have := congrArg Complex.re e
      dsimp only [j] at this
      simp at this
      linarith [Nat.cast_nonneg (α := ℝ) n]
    have hsj : s + 2 * j ≠ 0 := by
      intro e
      have := congrArg Complex.re e
      simp [s, j] at this
      linarith [Nat.cast_nonneg (α := ℝ) n]
    have hcj : (trivialCoeff n : ℂ) = 1 / (2 * j * (2 * j + 1)) := by
      simp [trivialCoeff, j]
    rw [hcj]
    calc
      1 / (2 * j * (2 * j + 1)) =
          1 / (2 * j * (s + 2 * j)) +
            (s - 1) / (2 * j * (2 * j + 1) * (s + 2 * j)) :=
        (trivial_partial_fraction j s hj hj1 hsj).symm
      _ = _ := by
        change 1 / (2 * j * (s + 2 * j)) +
          (s - 1) / (2 * j * (2 * j + 1) * (s + 2 * j)) =
          1 / (2 * j * (s + 2 * j)) +
            (s - 1) * (1 / (2 * j * (2 * j + 1)) / (s + 2 * j))
        field_simp [hj, hj1, hsj]
        <;> ring
  exact hc.unique (Complex.hasSum_ofReal.mpr trivialCoeff_hasSum)

/-- All scalar cancellations, retaining the Euler constant and both logarithms. -/
private theorem transform_scalar_cancellation
    (s Z d R : ℂ) (hs0 : s ≠ 0) (hs1 : s - 1 ≠ 0)
    (hbalance : (d / 2 + (Real.eulerMascheroniConstant : ℂ) / 2 + 1 / s) / s +
      (s - 1) * R = (1 - Real.log 2 : ℝ)) :
    (-Z / (s * (s - 1)) - 1 / (s - 1) ^ 2 +
      ((1 + Real.eulerMascheroniConstant : ℝ) : ℂ) / (s - 1)) -
      (((firstLiMass : ℂ) * (s - 1 / 2) -
        (1 / s + 1 / (s - 1) - (Real.log Real.pi : ℂ) / 2 + d / 2 + Z)) /
          (s * (s - 1))) - (Real.log (2 * Real.pi) : ℂ) / s + R = 0 := by
  have hrel : (d / 2 + (Real.eulerMascheroniConstant : ℂ) / 2 + 1 / s) +
      s * (s - 1) * R = s * (1 - (Real.log 2 : ℂ)) := by
    calc
      _ = s * ((d / 2 + (Real.eulerMascheroniConstant : ℂ) / 2 + 1 / s) / s +
          (s - 1) * R) := by field_simp [hs0] <;> ring
      _ = _ := by rw [hbalance]; push_cast; rfl
  have hden : s * (s - 1) ≠ 0 := mul_ne_zero hs0 hs1
  apply mul_left_cancel₀ hden
  rw [mul_zero]
  calc
    s * (s - 1) * ((-Z / (s * (s - 1)) - 1 / (s - 1) ^ 2 +
        ((1 + Real.eulerMascheroniConstant : ℝ) : ℂ) / (s - 1)) -
        (((firstLiMass : ℂ) * (s - 1 / 2) -
          (1 / s + 1 / (s - 1) - (Real.log Real.pi : ℂ) / 2 + d / 2 + Z)) /
            (s * (s - 1))) - (Real.log (2 * Real.pi) : ℂ) / s + R) =
        (d / 2 + (Real.eulerMascheroniConstant : ℂ) / 2 + 1 / s) +
          s * (s - 1) * R - s * (1 - (Real.log 2 : ℂ)) := by
      rw [firstLiMass_split,
        Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero]
      push_cast
      field_simp [hs0, hs1]
      <;> ring
    _ = 0 := sub_eq_zero.mpr hrel

/-- The exact discrepancy; the complete H and complete U occur literally. -/
def explicitDiscrepancy (y : ℝ) : ℂ :=
  (U (Real.exp y) : ℂ) - actualH y - (Real.log (2 * Real.pi) : ℂ) + (trivialT y : ℂ)

/-- The requested half-line damping; continuity at zero is unnecessary. -/
def explicitFourierResidual : ℝ → ℂ := (Ioi (0 : ℝ)).indicator
  (fun y => Complex.exp (-(2 : ℂ) * y) * explicitDiscrepancy y)

private theorem constant_line_integrable (t : ℝ) :
    IntegrableOn (fun y : ℝ => Complex.exp (-transformLine t * y) *
      (Real.log (2 * Real.pi) : ℂ)) (Ioi 0) :=
  (integrableOn_exp_mul_complex_Ioi (by simp : (-transformLine t).re < 0) 0).mul_const _

private theorem constant_line_laplace (t : ℝ) :
    (∫ y : ℝ in Ioi 0, Complex.exp (-transformLine t * y) *
      (Real.log (2 * Real.pi) : ℂ)) =
        (Real.log (2 * Real.pi) : ℂ) / transformLine t := by
  rw [integral_mul_const, integral_exp_mul_complex_Ioi (by simp : (-transformLine t).re < 0)]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, div_neg, neg_neg]
  ring

theorem explicitDiscrepancy_line_integrable (t : ℝ) :
    IntegrableOn (fun y : ℝ => Complex.exp (-transformLine t * y) *
      explicitDiscrepancy y) (Ioi 0) := by
  have h := (((U_line_integrable t).sub
    (actualH_laplace_integrable (by simp : 1 < (transformLine t).re))).sub
      (constant_line_integrable t)).add
        (trivialT_laplace_integrable (by simp : 0 < (transformLine t).re))
  convert h using 1
  funext y
  dsimp only [explicitDiscrepancy, Pi.add_apply, Pi.sub_apply]
  ring

/-- The desired transform is a conclusion of the preceding actual proofs,
and is not introduced as a hypothesis of this theorem. -/
theorem explicitDiscrepancy_line_zero {t : ℝ} (ht : t ≠ 0) :
    (∫ y : ℝ in Ioi 0, Complex.exp (-transformLine t * y) *
      explicitDiscrepancy y) = 0 := by
  have he : (fun y : ℝ => Complex.exp (-transformLine t * y) * explicitDiscrepancy y) =
      (fun y : ℝ => ((Complex.exp (-transformLine t * y) * (U (Real.exp y) : ℂ) -
        Complex.exp (-transformLine t * y) * actualH y) -
          Complex.exp (-transformLine t * y) * (Real.log (2 * Real.pi) : ℂ)) +
            Complex.exp (-transformLine t * y) * (trivialT y : ℂ)) := by
    funext y
    dsimp only [explicitDiscrepancy]
    ring
  rw [he, integral_add (μ := volume.restrict (Ioi (0 : ℝ)))
    (f := fun y : ℝ => (Complex.exp (-transformLine t * y) * (U (Real.exp y) : ℂ) -
      Complex.exp (-transformLine t * y) * actualH y) -
        Complex.exp (-transformLine t * y) * (Real.log (2 * Real.pi) : ℂ))
    (g := fun y : ℝ => Complex.exp (-transformLine t * y) * (trivialT y : ℂ))
    (((U_line_integrable t).sub
    (actualH_laplace_integrable (by simp : 1 < (transformLine t).re))).sub
      (constant_line_integrable t))
    (trivialT_laplace_integrable (by simp : 0 < (transformLine t).re)),
    integral_sub (f := fun y : ℝ =>
      Complex.exp (-transformLine t * y) * (U (Real.exp y) : ℂ) -
        Complex.exp (-transformLine t * y) * actualH y)
      (g := fun y : ℝ => Complex.exp (-transformLine t * y) * (Real.log (2 * Real.pi) : ℂ))
      ((U_line_integrable t).sub
      (actualH_laplace_integrable (by simp : 1 < (transformLine t).re)))
      (constant_line_integrable t),
    integral_sub (f := fun y : ℝ => Complex.exp (-transformLine t * y) * (U (Real.exp y) : ℂ))
      (g := fun y : ℝ => Complex.exp (-transformLine t * y) * actualH y)
      (U_line_integrable t)
      (actualH_laplace_integrable (by simp : 1 < (transformLine t).re)),
    U_line_laplace, actualH_laplace (by simp : 1 < (transformLine t).re),
    constant_line_laplace, xi_logDeriv_right (by simp : 1 < (transformLine t).re)]
  simpa only [neg_div] using (transform_scalar_cancellation (transformLine t)
    (deriv riemannZeta (transformLine t) / riemannZeta (transformLine t))
    (Complex.digamma (transformLine t / 2))
    (∫ y : ℝ in Ioi 0, Complex.exp (-transformLine t * y) * (trivialT y : ℂ))
    (by intro e; have := congrArg Complex.re e; norm_num at this)
    (by intro e; have := congrArg Complex.re e; norm_num at this)
    (digamma_trivial_balance ht))

theorem explicitFourierResidual_integrable : Integrable explicitFourierResidual := by
  rw [explicitFourierResidual, integrable_indicator_iff measurableSet_Ioi]
  simpa only [transformLine, zero_mul, mul_zero, Complex.ofReal_zero, zero_add,
    add_zero] using explicitDiscrepancy_line_integrable 0

theorem explicitFourierResidual_continuousAt {y : ℝ} (hy : 0 < y) :
    ContinuousAt explicitFourierResidual y := by
  have he : explicitFourierResidual =ᶠ[𝓝 y]
      (fun x : ℝ => Complex.exp (-(2 : ℂ) * x) * explicitDiscrepancy x) := by
    filter_upwards [Ioi_mem_nhds hy] with x hx
    exact Set.indicator_of_mem hx _
  apply ContinuousAt.congr_of_eventuallyEq (hg := he)
  apply ContinuousAt.mul (by fun_prop)
  change ContinuousAt (fun x : ℝ => (U (Real.exp x) : ℂ) - actualH x -
    (Real.log (2 * Real.pi) : ℂ) + (trivialT x : ℂ)) y
  exact (((Complex.continuous_ofReal.continuousAt.comp U_exp_continuous.continuousAt).sub
    actualH_continuous.continuousAt).sub continuousAt_const).add
      (Complex.continuous_ofReal.continuousAt.comp (trivialT_continuousAt hy))

/-- Mathlib's minus-2*pi Fourier convention is converted to the actual Laplace line. -/
theorem explicitFourierResidual_fourier (t : ℝ) :
    𝓕 explicitFourierResidual t =
      ∫ y : ℝ in Ioi 0, Complex.exp (-transformLine t * y) * explicitDiscrepancy y := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  simp only [smul_eq_mul]
  have he : (fun y : ℝ => Complex.exp ((-2 * Real.pi * y * t : ℝ) * Complex.I) *
      explicitFourierResidual y) =
      (Ioi (0 : ℝ)).indicator (fun y : ℝ =>
        Complex.exp (-transformLine t * y) * explicitDiscrepancy y) := by
    funext y
    by_cases hy : y ∈ Ioi (0 : ℝ)
    · simp only [explicitFourierResidual, Set.indicator_of_mem hy, ← mul_assoc,
        ← Complex.exp_add]
      congr 2
      dsimp only [transformLine]
      push_cast
      ring
    · simp only [explicitFourierResidual, Set.indicator_of_notMem hy, mul_zero]
  rw [he, integral_indicator measurableSet_Ioi]

/-- Frequency zero is recovered from continuity of the genuinely L1 Fourier
transform. This closes the integer-complement edge of the digamma API. -/
theorem explicitFourierResidual_fourier_zero : 𝓕 explicitFourierResidual = 0 := by
  have hc : Continuous (𝓕 explicitFourierResidual) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (by fun_prop) explicitFourierResidual_integrable
  have hz : ({(0 : ℝ)}ᶜ : Set ℝ) ⊆ {t : ℝ | 𝓕 explicitFourierResidual t = 0} := by
    intro t ht
    change 𝓕 explicitFourierResidual t = 0
    rw [explicitFourierResidual_fourier, explicitDiscrepancy_line_zero
      (show t ≠ 0 by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using ht)]
  have hall := closure_minimal hz (isClosed_eq hc continuous_const)
  rw [(dense_compl_singleton (0 : ℝ)).closure_eq] at hall
  funext t
  exact hall (mem_univ t)

/-- The actual integrated formula at every positive real y. Fourier inversion
uses continuity only at this y; transform integrability follows from FT=0. -/
theorem actual_integrated_explicit_formula {y : ℝ} (hy : 0 < y) :
    actualH y =
      ((U (Real.exp y) - Real.log (2 * Real.pi) + trivialT y : ℝ) : ℂ) := by
  have hf : Integrable (𝓕 explicitFourierResidual) := by
    rw [explicitFourierResidual_fourier_zero]
    exact integrable_zero ℝ ℂ volume
  have hinv := explicitFourierResidual_integrable.fourierInv_fourier_eq hf
    (explicitFourierResidual_continuousAt hy)
  rw [explicitFourierResidual_fourier_zero, Real.fourierInv_eq'] at hinv
  simp only [Pi.zero_apply, smul_zero, integral_zero] at hinv
  have hz : Complex.exp (-(2 : ℂ) * y) * explicitDiscrepancy y = 0 := by
    simpa only [explicitFourierResidual,
      Set.indicator_of_mem (show y ∈ Ioi (0 : ℝ) from hy)] using hinv.symm
  have hd : explicitDiscrepancy y = 0 :=
    (mul_eq_zero.mp hz).resolve_left (Complex.exp_ne_zero _)
  dsimp only [explicitDiscrepancy] at hd
  push_cast
  linear_combination -hd

end D5.S3.Weil.Mertens.IntegratedExplicit
end
