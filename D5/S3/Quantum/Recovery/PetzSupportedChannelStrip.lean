/- GID: D5/S3/Quantum/Recovery/PetzSupportedChannelStrip
   generality: G
   mirror-B: D5/B/S3/Quantum/Recovery/PetzSupportedChannelStrip
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Supported modular boundary deficits integrate to the trace-log loss of a quantum channel. -/

import D5.S3.Analytic.PetzStripFiniteSeries
import D5.S3.Quantum.Divergence.CanonicalRelativeModularModel
import D5.S3.Quantum.Divergence.ResolventDefectRigidity

/-!
# The supported-channel Petz strip identity

The strip identity of Yang, arXiv:2609.33815v2, Theorem II.1, is realized
for finite supported states as proposed in §V.3. The overlap uses the
mixed reference/source eigenvector coordinates of the supported channel model.
The two deficits account for the norm lost by the channel contractions on the
two strip boundaries.
-/

set_option autoImplicit false

noncomputable section

open Matrix MeasureTheory
open scoped BigOperators Classical ComplexOrder MatrixOrder
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Divergence.SupportAwareRelativeEntropy
open D5.S3.Quantum.Divergence.CanonicalChannelDPI
open D5.S3.Quantum.Divergence.ResolventDefectRigidity (contraction_saturation)
open D5.S3.Quantum.Dynamics.EntropyProductionCoherenceDeletionIdentity (cfc_diagonal)
open PetzCothStripMode (lowerWeight)
open PetzExponentialBoundaryEvaluation (petzWeight)

namespace D5.S3.Quantum.Recovery.PetzSupportedChannelStrip

section MatrixFacts

variable {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

private theorem pair_self_re (x : n → ℂ) :
    (star x ⬝ᵥ x).re = ∑ i, ‖x i‖ ^ 2 := by
  simpa only [Complex.ofReal_one, Matrix.diagonal_one, Matrix.one_mulVec, one_mul] using
    diagonal_quadratic_form (fun _ : n => (1 : ℝ)) x

private theorem adjoint_pair (V : Matrix n m ℂ) (x : n → ℂ) (y : m → ℂ) :
    star x ⬝ᵥ (V *ᵥ y) = star (Vᴴ *ᵥ x) ⬝ᵥ y := by
  rw [Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose, Matrix.dotProduct_mulVec]

private theorem hermitian_pair_eq_ofReal (H : Matrix n n ℂ) (hH : H.IsHermitian)
    (x : n → ℂ) :
    star x ⬝ᵥ (H *ᵥ x) = ((star x ⬝ᵥ (H *ᵥ x)).re : ℂ) := by
  exact (Complex.conj_eq_iff_re.mp (hH.star_dotProduct_mulVec_comm x x)).symm

private theorem pair_gram (V : Matrix n m ℂ) (y : m → ℂ) :
    (star (V *ᵥ y) ⬝ᵥ (V *ᵥ y)).re = (star y ⬝ᵥ ((Vᴴ * V) *ᵥ y)).re := by
  rw [← Matrix.mulVec_mulVec, adjoint_pair Vᴴ, Matrix.conjTranspose_conjTranspose]

private theorem pair_sum (V : Matrix n m ℂ) (x : n → ℂ) (y : m → ℂ) :
    star x ⬝ᵥ (V *ᵥ y) = ∑ ij : n × m, star (x ij.1) * V ij.1 ij.2 * y ij.2 := by
  simp only [Fintype.sum_prod_type, dotProduct, Matrix.mulVec, Pi.star_apply,
    Finset.mul_sum, mul_assoc]

private theorem contraction_sq_le (V : Matrix n m ℂ) (hV : Vᴴ * V ≤ 1) (y : m → ℂ) :
    (∑ i, ‖(V *ᵥ y) i‖ ^ 2) ≤ ∑ j, ‖y j‖ ^ 2 := by
  have hp := (Matrix.le_iff.mp hV).dotProduct_mulVec_nonneg y
  have hre := (Complex.nonneg_iff.mp hp).1
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub, Complex.sub_re,
    ← pair_gram, pair_self_re, pair_self_re] at hre
  exact sub_nonneg.mp hre

private theorem pair_deficit (x y : n → ℂ) (hx : (∑ i, ‖x i‖ ^ 2) = 1) :
    2 * (1 - (star x ⬝ᵥ y).re) =
      (∑ i, ‖x i - y i‖ ^ 2) + (1 - ∑ i, ‖y i‖ ^ 2) := by
  let x' : EuclideanSpace ℂ n := WithLp.toLp 2 x
  let y' : EuclideanSpace ℂ n := WithLp.toLp 2 y
  have hd := norm_sub_sq (𝕜 := ℂ) x' y'
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq,
    EuclideanSpace.norm_sq_eq, EuclideanSpace.inner_eq_star_dotProduct] at hd
  change (∑ i, ‖x i - y i‖ ^ 2) =
    (∑ i, ‖x i‖ ^ 2) - 2 * (y ⬝ᵥ star x).re + ∑ i, ‖y i‖ ^ 2 at hd
  rw [dotProduct_comm y (star x)] at hd
  rw [hd, hx]
  ring

/-- Diagonal complex power on the positive spectral coordinates. -/
def modularPower (d : n → ℝ) (z : ℂ) : Matrix n n ℂ :=
  diagonal fun i => Complex.exp ((Real.log (d i) : ℂ) * z)

private theorem modularPower_zero (d : n → ℝ) : modularPower d 0 = 1 := by
  simp only [modularPower, mul_zero, Complex.exp_zero, Matrix.diagonal_one]

private theorem modularPower_one (d : n → ℝ) (hd : ∀ i, 0 < d i) :
    modularPower d 1 = diagonal fun i => (d i : ℂ) := by
  simp only [modularPower, mul_one]
  apply congrArg Matrix.diagonal
  funext i
  rw [← Complex.ofReal_exp, Real.exp_log (hd i)]

private theorem modularPower_add (d : n → ℝ) (z w : ℂ) :
    modularPower d (z + w) = modularPower d z * modularPower d w := by
  simp only [modularPower, Matrix.diagonal_mul_diagonal, mul_add, Complex.exp_add]

private theorem modularPower_real_adjoint (d : n → ℝ) (r : ℝ) :
    (modularPower d (r : ℂ))ᴴ = modularPower d (r : ℂ) := by
  simp only [modularPower, Matrix.diagonal_conjTranspose]
  apply congrArg Matrix.diagonal
  funext i
  simp only [Pi.star_apply, ← Complex.ofReal_mul, ← Complex.ofReal_exp, Complex.star_def,
    Complex.conj_ofReal]

private theorem modularPower_unitary (d : n → ℝ) (t : ℂ) (ht : t.re = 0) :
    (modularPower d t)ᴴ * modularPower d t = 1 := by
  rw [← Matrix.diagonal_one]
  simp only [modularPower, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
  apply congrArg Matrix.diagonal
  funext i
  have he : ‖Complex.exp ((Real.log (d i) : ℂ) * t)‖ = 1 := by
    simp only [Complex.norm_exp, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      ht, mul_zero, zero_mul, sub_zero, Real.exp_zero]
  simp only [Pi.star_apply, Complex.star_def, Complex.conj_mul', he, one_pow, Complex.ofReal_one]

private theorem phase_preserves_sq (d : n → ℝ) (t : ℂ) (ht : t.re = 0) (x : n → ℂ) :
    (∑ i, ‖(modularPower d t *ᵥ x) i‖ ^ 2) = ∑ i, ‖x i‖ ^ 2 := by
  rw [← pair_self_re (modularPower d t *ᵥ x), pair_gram, modularPower_unitary d t ht,
    Matrix.one_mulVec, pair_self_re]

private theorem phase_contraction_sq_le (p : n → ℝ) (q : m → ℝ)
    (V : Matrix n m ℂ) (hV : Vᴴ * V ≤ 1) (t : ℂ) (ht : t.re = 0) (y : m → ℂ) :
    (∑ i, ‖(modularPower p t *ᵥ (V *ᵥ (modularPower q (-t) *ᵥ y))) i‖ ^ 2) ≤
      ∑ j, ‖y j‖ ^ 2 := by
  have hneg : (-t).re = 0 := by simp only [Complex.neg_re, ht, neg_zero]
  rw [phase_preserves_sq p t ht, ← phase_preserves_sq q (-t) hneg y]
  exact contraction_sq_le V hV _

end MatrixFacts

universe u v

variable {a : Type u} {b : Type v} [Fintype a] [DecidableEq a] [Nonempty a]
  [Fintype b] [DecidableEq b] [Nonempty b]
  {Φ : QuantumChannel a b} {ρ σ : DensityState a}

abbrev inputRatio (D : SupportedRelativeModularData Φ ρ σ) (i : D.J × D.I) : ℝ :=
  D.sj i.1 / D.ri i.2

abbrev outputRatio (D : SupportedRelativeModularData Φ ρ σ) (j : D.L × D.K) : ℝ :=
  D.ql j.1 / D.pk j.2

private theorem inputRatio_pos (D : SupportedRelativeModularData Φ ρ σ) (i : D.J × D.I) :
    0 < inputRatio D i :=
  div_pos i.1.2 i.2.2

private theorem outputRatio_pos (D : SupportedRelativeModularData Φ ρ σ) (j : D.L × D.K) :
    0 < outputRatio D j :=
  div_pos j.1.2 j.2.2

private def frequency (D : SupportedRelativeModularData Φ ρ σ)
    (ij : (D.J × D.I) × (D.L × D.K)) : ℝ :=
  Real.log (inputRatio D ij.1) - Real.log (outputRatio D ij.2)

private def coefficient (D : SupportedRelativeModularData Φ ρ σ)
    (ij : (D.J × D.I) × (D.L × D.K)) : ℂ :=
  star (D.ξ ij.1) * D.V ij.1 ij.2 * D.η ij.2

/-- The finite series with coefficient `conj ξᵢ * Vᵢⱼ * ηⱼ` and
frequency `log aᵢ - log bⱼ`. -/
def overlap (D : SupportedRelativeModularData Φ ρ σ) : ℂ → ℂ :=
  PetzStripFiniteSeries.finiteOverlap (frequency D) (coefficient D)

/-- The coordinates of `A^z V B^(-z) η` in the supported channel model. -/
def amplitude (D : SupportedRelativeModularData Φ ρ σ) (z : ℂ) : D.J × D.I → ℂ :=
  (modularPower (inputRatio D) z * D.V * modularPower (outputRatio D) (-z)) *ᵥ D.η

private theorem overlap_eq_pair (D : SupportedRelativeModularData Φ ρ σ) (z : ℂ) :
    overlap D z = star D.ξ ⬝ᵥ amplitude D z := by
  rw [overlap, PetzStripFiniteSeries.finiteOverlap, amplitude, pair_sum]
  apply Finset.sum_congr rfl
  intro ij _
  simp only [coefficient, frequency, modularPower, Matrix.mul_diagonal,
    Matrix.diagonal_mul, Complex.ofReal_sub]
  rw [sub_mul, sub_eq_add_neg, Complex.exp_add, mul_neg]
  ring

private theorem overlap_zero_re (M : SupportedRelativeModularModel Φ ρ σ) :
    (overlap M.data 0).re = 1 := by
  rw [overlap_eq_pair, amplitude, neg_zero, modularPower_zero, modularPower_zero,
    Matrix.one_mul, Matrix.mul_one, M.mapsη, pair_self_re, M.normξ]

private theorem adjoint_mapsξ (M : SupportedRelativeModularModel Φ ρ σ) :
    M.data.Vᴴ *ᵥ M.data.ξ = M.data.η := by
  have hs : (star (M.data.V *ᵥ M.data.η) ⬝ᵥ (M.data.V *ᵥ M.data.η)).re =
      (star M.data.η ⬝ᵥ M.data.η).re := by
    rw [M.mapsη, pair_self_re, pair_self_re, M.normξ, M.normη]
  simpa only [M.mapsη] using contraction_saturation M.data.V M.hVnorm M.data.η hs

private theorem spectral_slope (D : SupportedRelativeModularData Φ ρ σ) :
    (∑ ij, coefficient D ij * (frequency D ij : ℂ)) =
      star D.ξ ⬝ᵥ ((cfc Real.log D.A * D.V) *ᵥ D.η) -
        star D.ξ ⬝ᵥ ((D.V * cfc Real.log D.B) *ᵥ D.η) := by
  have hA : cfc Real.log D.A = diagonal (fun i => (Real.log (inputRatio D i) : ℂ)) :=
    cfc_diagonal Real.log (inputRatio D)
  have hB : cfc Real.log D.B = diagonal (fun j => (Real.log (outputRatio D j) : ℂ)) :=
    cfc_diagonal Real.log (outputRatio D)
  rw [hA, hB, pair_sum, pair_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro ij _
  simp only [coefficient, frequency, Matrix.diagonal_mul, Matrix.mul_diagonal, Complex.ofReal_sub]
  ring

/-- The complex derivative is the negative supported trace-log loss, embedded in ℂ. -/
theorem hasDerivAt_overlap_zero (M : SupportedRelativeModularModel Φ ρ σ) :
    HasDerivAt (overlap M.data)
      ((-(finiteTraceLogRelativeEntropy ρ σ -
        finiteTraceLogRelativeEntropy (Φ.mapState ρ) (Φ.mapState σ)) : ℝ) : ℂ) 0 := by
  have hA : (cfc Real.log M.data.A).IsHermitian :=
    (show IsSelfAdjoint (cfc Real.log M.data.A) from cfc_predicate Real.log M.data.A)
  have hB : (cfc Real.log M.data.B).IsHermitian :=
    (show IsSelfAdjoint (cfc Real.log M.data.B) from cfc_predicate Real.log M.data.B)
  have hd : (∑ ij, coefficient M.data ij * (frequency M.data ij : ℂ)) =
      ((-(finiteTraceLogRelativeEntropy ρ σ -
        finiteTraceLogRelativeEntropy (Φ.mapState ρ) (Φ.mapState σ)) : ℝ) : ℂ) := by
    rw [spectral_slope, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      M.mapsη, adjoint_pair M.data.V, adjoint_mapsξ M,
      hermitian_pair_eq_ofReal _ hA, hermitian_pair_eq_ofReal _ hB,
      ← Complex.ofReal_sub, M.canonicalTraceR, M.canonicalTraceT]
    congr 1
    ring
  rw [← hd]
  exact PetzStripFiniteSeries.hasDerivAt_finiteOverlap_zero (frequency M.data) (coefficient M.data)

private theorem deriv_overlap_zero_re (M : SupportedRelativeModularModel Φ ρ σ) :
    (deriv (overlap M.data) 0).re =
      -(finiteTraceLogRelativeEntropy ρ σ -
        finiteTraceLogRelativeEntropy (Φ.mapState ρ) (Φ.mapState σ)) := by
  simpa only [Complex.ofReal_re] using congrArg Complex.re (hasDerivAt_overlap_zero M).deriv

/-- The comparison map on the upper edge at imaginary part zero. -/
private def halfComparison (D : SupportedRelativeModularData Φ ρ σ) :
    Matrix (D.J × D.I) (D.L × D.K) ℂ :=
  modularPower (inputRatio D) ((1 / 2 : ℝ) : ℂ) * D.V *
    modularPower (outputRatio D) (-((1 / 2 : ℝ) : ℂ))

private theorem halfComparison_contraction (M : SupportedRelativeModularModel Φ ρ σ) :
    (halfComparison M.data)ᴴ * halfComparison M.data ≤ 1 := by
  let D := M.data
  let h : ℂ := ((1 / 2 : ℝ) : ℂ)
  let F := modularPower (inputRatio D) h
  let G := modularPower (outputRatio D) (-h)
  have hh : h + h = 1 := by
    rw [show h + h = (((1 / 2 : ℝ) + 1 / 2 : ℝ) : ℂ) from (Complex.ofReal_add _ _).symm,
      show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num, Complex.ofReal_one]
  have hsum : -h + 1 + -h = 0 := by
    rw [← hh]
    ring
  have hF : Fᴴ = F := modularPower_real_adjoint (inputRatio D) (1 / 2)
  have hG : Gᴴ = G := by
    simpa only [Complex.ofReal_neg] using modularPower_real_adjoint (outputRatio D) (-(1 / 2))
  have hFF : F * F = D.A := by
    change modularPower (inputRatio D) h * modularPower (inputRatio D) h = D.A
    rw [← modularPower_add, hh, modularPower_one _ (inputRatio_pos D)]
  have hGBG : Gᴴ * D.B * G = 1 := by
    have hB : modularPower (outputRatio D) 1 = D.B := modularPower_one _ (outputRatio_pos D)
    rw [hG, ← hB]
    change modularPower (outputRatio D) (-h) * modularPower (outputRatio D) 1 *
      modularPower (outputRatio D) (-h) = 1
    rw [← modularPower_add, ← modularPower_add, hsum, modularPower_zero]
  change (F * D.V * G)ᴴ * (F * D.V * G) ≤ 1
  calc
    _ = Gᴴ * (D.Vᴴ * D.A * D.V) * G := by
      simp only [Matrix.conjTranspose_mul, hF, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc F F, hFF]
    _ ≤ Gᴴ * D.B * G := by
      apply Matrix.le_iff.mpr
      simpa only [Matrix.mul_sub, Matrix.sub_mul] using
        ((Matrix.le_iff.mp M.hVA).conjTranspose_mul_mul_same G)
    _ = 1 := hGBG

private theorem lower_amplitude_sq_le (M : SupportedRelativeModularModel Φ ρ σ) (s : ℝ) :
    (∑ i, ‖amplitude M.data ((s : ℂ) * Complex.I) i‖ ^ 2) ≤ 1 := by
  simp only [amplitude, ← Matrix.mulVec_mulVec]
  calc
    _ ≤ ∑ j, ‖M.data.η j‖ ^ 2 :=
      phase_contraction_sq_le _ _ _ M.hVnorm ((s : ℂ) * Complex.I) (by simp [Complex.mul_re]) _
    _ = 1 := M.normη

private theorem upper_amplitude_sq_le (M : SupportedRelativeModularModel Φ ρ σ) (s : ℝ) :
    (∑ i, ‖amplitude M.data (((1 / 2 : ℝ) : ℂ) + (s : ℂ) * Complex.I) i‖ ^ 2) ≤ 1 := by
  let D := M.data
  let h : ℂ := ((1 / 2 : ℝ) : ℂ)
  let t : ℂ := (s : ℂ) * Complex.I
  have ha : amplitude D (h + t) =
      modularPower (inputRatio D) t *ᵥ
        (halfComparison D *ᵥ (modularPower (outputRatio D) (-t) *ᵥ D.η)) := by
    rw [amplitude, neg_add, add_comm h t,
      modularPower_add (inputRatio D) t h, modularPower_add (outputRatio D) (-h) (-t)]
    simp only [halfComparison, h, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  change (∑ i, ‖amplitude D (h + t) i‖ ^ 2) ≤ 1
  rw [ha]
  calc
    _ ≤ ∑ j, ‖D.η j‖ ^ 2 :=
      phase_contraction_sq_le _ _ _ (halfComparison_contraction M) t
        (by simp [t, Complex.mul_re]) _
    _ = 1 := M.normη

/-- The two boundary integrands use this same unsymmetrized overlap deficit. -/
def deficit (D : SupportedRelativeModularData Φ ρ σ) (r s : ℝ) : ℝ :=
  2 * (1 - (overlap D ((r : ℂ) + (s : ℂ) * Complex.I)).re)

/-- The overlap deficit is the squared distance of the two amplitudes plus
the norm defect of the second amplitude. -/
theorem deficit_eq_distance_add_defect (M : SupportedRelativeModularModel Φ ρ σ) (r s : ℝ) :
    let γ := amplitude M.data ((r : ℂ) + (s : ℂ) * Complex.I)
    deficit M.data r s =
      (∑ i, ‖M.data.ξ i - γ i‖ ^ 2) + (1 - ∑ i, ‖γ i‖ ^ 2) := by
  dsimp only
  rw [deficit, overlap_eq_pair]
  exact pair_deficit _ _ M.normξ

theorem lower_deficit_nonneg (M : SupportedRelativeModularModel Φ ρ σ) (s : ℝ) :
    0 ≤ deficit M.data 0 s := by
  rw [deficit_eq_distance_add_defect]
  simp only [Complex.ofReal_zero, zero_add]
  exact add_nonneg (Finset.sum_nonneg fun i _ => sq_nonneg _)
    (sub_nonneg.mpr (lower_amplitude_sq_le M s))

theorem upper_deficit_nonneg (M : SupportedRelativeModularModel Φ ρ σ) (s : ℝ) :
    0 ≤ deficit M.data (1 / 2) s := by
  rw [deficit_eq_distance_add_defect]
  exact add_nonneg (Finset.sum_nonneg fun i _ => sq_nonneg _)
    (sub_nonneg.mpr (upper_amplitude_sq_le M s))

/-- Both weighted boundary deficits of a supported model are integrable and their sum is the
actual channel entropy loss. Support containment supplies such a model through
`supported_relative_modular_model`. -/
theorem integral_supported_channel_strip (M : SupportedRelativeModularModel Φ ρ σ) :
    Integrable (fun s => lowerWeight s * deficit M.data 0 s) ∧
      Integrable (fun s => petzWeight s * deficit M.data (1 / 2) s) ∧
      (∫ s, lowerWeight s * deficit M.data 0 s) +
        (∫ s, petzWeight s * deficit M.data (1 / 2) s) =
        finiteTraceLogRelativeEntropy ρ σ -
          finiteTraceLogRelativeEntropy (Φ.mapState ρ) (Φ.mapState σ) := by
  have h := PetzStripFiniteSeries.integral_finiteOverlap_strip
    (frequency M.data) (coefficient M.data) (overlap_zero_re M)
    (lower_deficit_nonneg M)
  change Integrable (fun s => lowerWeight s * deficit M.data 0 s) ∧
    Integrable (fun s => petzWeight s * deficit M.data (1 / 2) s) ∧
    (∫ s, lowerWeight s * deficit M.data 0 s) +
      (∫ s, petzWeight s * deficit M.data (1 / 2) s) = -(deriv (overlap M.data) 0).re at h
  simpa only [deriv_overlap_zero_re M, neg_neg] using h

end D5.S3.Quantum.Recovery.PetzSupportedChannelStrip
