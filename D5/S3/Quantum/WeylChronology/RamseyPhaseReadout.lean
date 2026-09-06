/- GID: D5/S3/Quantum/WeylChronology/RamseyPhaseReadout
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:exact-amplitude-identities)
   anchors: []
   digest: Two calibrated Ramsey settings read the complex phase, with explicit alias boundaries. -/

import D5.S3.Quantum.WeylChronology.SchrodingerDisplacement

/-!
# Ramsey probabilities and their observation kernel

The two equal-amplitude paths have relative phase phi. After an analyzer
phase theta and recombination, the plus-port coefficient is
(1+exp(i*(phi-theta)))/2. Its squared modulus is a Born probability.
A single experimental shot is a Bernoulli outcome, not this exact probability.

Fluehmann and Home, PRL 125, 043602 (2020), eq. (3), use the two phase settings
0 and pi/2 to obtain real and imaginary displacement-characteristic data.
Razian et al., arXiv:2604.06565v1, eq. (5) and following text, likewise use an
ancilla geometric phase and explicitly discuss aliasing at large coupling.
We prove the ideal coefficient algebra and observation kernel; no detector
noise, sampling theorem or quantum-metrological advantage is assumed.

The primitive is this physical two-port amplitude, not an appended score.
The phase and two probabilities have identical kernels. They must not be
counted as independent unique-capture contributions in a shared catalog.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.WeylChronology.RamseyPhaseReadout

noncomputable section

/-- The plus-port coefficient after equal path splitting and recombination. -/
def plusAmplitude (θ φ : ℝ) : ℂ :=
  (1 + Complex.exp (((φ - θ : ℝ) : ℂ) * Complex.I)) / 2

/-- Ideal plus probability; experimental estimation needs repeated shots. -/
def plusProbability (θ φ : ℝ) : ℝ := Complex.normSq (plusAmplitude θ φ)

/-- Two phase settings, measured on separate preparations. -/
def quadratureReadout (φ : ℝ) : ℝ × ℝ :=
  (plusProbability 0 φ, plusProbability (Real.pi / 2) φ)

private theorem normSq_phase (φ : ℝ) :
    Complex.normSq (Complex.exp ((φ : ℂ) * Complex.I)) = 1 := by
  rw [Complex.normSq_apply]
  simp only [Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  nlinarith [Real.sin_sq_add_cos_sq φ]

/-- The Ramsey fringe is derived from the amplitude, not postulated. -/
theorem plus_probability_formula (θ φ : ℝ) :
    plusProbability θ φ = (1 + Real.cos (φ - θ)) / 2 := by
  unfold plusProbability plusAmplitude
  rw [Complex.normSq_div]
  have h := normSq_phase (φ - θ)
  rw [Complex.normSq_apply] at h
  simp only [Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im] at h
  norm_num [Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im] <;>
    nlinarith [h]

/-- The ideal outputs are probabilities in the unit interval. -/
theorem plus_probability_mem_unit (θ φ : ℝ) :
    0 ≤ plusProbability θ φ ∧ plusProbability θ φ ≤ 1 := by
  rw [plus_probability_formula]
  constructor <;> nlinarith [Real.neg_one_le_cos (φ - θ), Real.cos_le_one (φ - θ)]

/-- Reading both analyzer settings is exactly reading the wrapped complex phase. -/
theorem quadrature_readout_kernel (φ ψ : ℝ) :
    quadratureReadout φ = quadratureReadout ψ ↔
      Complex.exp ((φ : ℂ) * Complex.I) = Complex.exp ((ψ : ℂ) * Complex.I) := by
  have hread (t : ℝ) : quadratureReadout t =
      ((1 + Real.cos t) / 2, (1 + Real.sin t) / 2) := by
    simp [quadratureReadout, plus_probability_formula, Real.cos_sub_pi_div_two]
  rw [hread, hread]
  constructor
  · intro h
    have hc := congrArg Prod.fst h
    have hs := congrArg Prod.snd h
    apply Complex.ext
    · simp only [Complex.exp_ofReal_mul_I_re]
      dsimp at hc
      linarith
    · simp only [Complex.exp_ofReal_mul_I_im]
      dsimp at hs
      linarith
  · intro h
    have hc := congrArg Complex.re h
    have hs := congrArg Complex.im h
    simp only [Complex.exp_ofReal_mul_I_re] at hc
    simp only [Complex.exp_ofReal_mul_I_im] at hs
    rw [hc, hs]

/-- Within the sine monotonicity band, a pi/2 analyzer alone identifies phase. -/
theorem sine_analyzer_injective_on_band (φ ψ : ℝ)
    (hφ : |φ| ≤ Real.pi / 2) (hψ : |ψ| ≤ Real.pi / 2)
    (h : plusProbability (Real.pi / 2) φ = plusProbability (Real.pi / 2) ψ) :
    φ = ψ := by
  rw [plus_probability_formula, plus_probability_formula,
    Real.cos_sub_pi_div_two, Real.cos_sub_pi_div_two] at h
  apply Real.injOn_sin (abs_le.mp hφ) (abs_le.mp hψ)
  linarith

/-- The zero analyzer loses orientation, even before periodic aliasing. -/
theorem cosine_analyzer_reversal_blind (φ : ℝ) :
    plusProbability 0 (-φ) = plusProbability 0 φ := by
  simp [plus_probability_formula]

/-- Two quadratures still cannot resolve a full turn without a range promise. -/
theorem full_turn_alias :
    quadratureReadout 0 = quadratureReadout (2 * Real.pi) ∧ (0 : ℝ) ≠ 2 * Real.pi := by
  constructor
  · apply (quadrature_readout_kernel 0 (2 * Real.pi)).mpr
    apply Complex.ext <;>
      simp [Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  · nlinarith [Real.pi_pos]

#print axioms plus_probability_formula
#print axioms quadrature_readout_kernel
#print axioms sine_analyzer_injective_on_band
#print axioms full_turn_alias

end
end D5.S3.Quantum.WeylChronology.RamseyPhaseReadout
