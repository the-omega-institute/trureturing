/- GID: D5/S3/Analytic/ExponentialGramWeightedEvaluation
   generality: G
   mirror-B: D5/B/S3/Analytic/ExponentialGramWeightedEvaluation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite exponential sums have sharp weighted evaluation at zero. -/

import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Measure.OpenPos
import D5.S3.Analytic.Entire.ExponentialBlockIndependence
import D5.S3.Quantum.Measurement.DetectorSensorDickeOptimality

/-!
# Weighted evaluation of finite exponential sums

This is the finite-frequency evaluation estimate used in the ordinary Petz
recovery audit. The trace proof computes the norm of evaluation at zero. The
entrywise Laplace integral identifies the matrix form with the weighted energy.
-/

set_option autoImplicit false

noncomputable section

open Filter Matrix MeasureTheory Set
open scoped BigOperators ComplexOrder Topology

namespace ExponentialGramWeightedEvaluation

open D5.S3.Analytic.Entire (blockEvaluation block_evaluation_injective)

variable {ι : Type*}

/-- The eigenvalue of differentiation at a real frequency. -/
def frequency (ω : ι → ℝ) (i : ι) : ℂ := Complex.I * (ω i : ℂ)

private def denominator (h : ℝ) (ω : ι → ℝ) (i j : ι) : ℂ :=
  (h : ℂ) - (frequency ω j - frequency ω i)

/-- The half-line exponential Gram matrix with the conjugated mode in the row index. -/
def gram (h : ℝ) (ω : ι → ℝ) : Matrix ι ι ℂ :=
  Matrix.of fun i j => 1 / denominator h ω i j

/-- The generator of differentiation on the finite span of the modes. -/
def generator [DecidableEq ι] (ω : ι → ℝ) : Matrix ι ι ℂ :=
  Matrix.diagonal (frequency ω)

private lemma star_frequency (ω : ι → ℝ) (i : ι) :
    star (frequency ω i) = -frequency ω i := by
  simp [frequency, neg_mul]

private lemma denominator_re (h : ℝ) (ω : ι → ℝ) (i j : ι) :
    (denominator h ω i j).re = h := by
  simp [denominator, frequency, Complex.sub_re, Complex.mul_re]

private lemma denominator_ne_zero {h : ℝ} (hh : 0 < h) (ω : ι → ℝ) (i j : ι) :
    denominator h ω i j ≠ 0 := by
  intro hz
  have hre := denominator_re h ω i j
  rw [hz, Complex.zero_re] at hre
  exact hh.ne' hre.symm

private lemma generator_conjTranspose [DecidableEq ι] (ω : ι → ℝ) :
    (generator ω)ᴴ = -generator ω := by
  unfold generator
  rw [Matrix.diagonal_conjTranspose]
  calc
    Matrix.diagonal (star (frequency ω)) = Matrix.diagonal (-frequency ω) :=
      congrArg Matrix.diagonal (funext fun i => star_frequency ω i)
    _ = -Matrix.diagonal (frequency ω) := (Matrix.diagonal_neg (frequency ω)).symm

variable [Fintype ι]

/-- The finite differentiation identity with the all-ones outer product. -/
private theorem gram_identity [DecidableEq ι] (h : ℝ) (ω : ι → ℝ) (hh : 0 < h) :
    (h : ℂ) • gram h ω - Matrix.vecMulVec (1 : ι → ℂ) (star (1 : ι → ℂ)) =
      gram h ω * generator ω + (generator ω)ᴴ * gram h ω := by
  apply Matrix.ext
  intro i j
  have hden : (h : ℂ) - (frequency ω j - frequency ω i) ≠ 0 :=
    denominator_ne_zero hh ω i j
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.vecMulVec_apply,
    star_one, Pi.one_apply, mul_one, Matrix.add_apply, generator,
    Matrix.diagonal_conjTranspose, Matrix.mul_diagonal, Matrix.diagonal_mul,
    Pi.star_apply, star_frequency, gram, Matrix.of_apply, denominator]
  field_simp [hden]
  ring

/-- Left multiplication by the inverse followed by the trace computes the
evaluation of the inverse against the all-ones vector. -/
private theorem inverse_evaluation [DecidableEq ι] (h : ℝ) (ω : ι → ℝ) (hh : 0 < h)
    (hG : (gram h ω).PosDef) :
    star (1 : ι → ℂ) ⬝ᵥ ((gram h ω)⁻¹ *ᵥ (1 : ι → ℂ)) =
      ((h * (Fintype.card ι : ℝ) : ℝ) : ℂ) := by
  let G := gram h ω
  let D := generator ω
  let e : ι → ℂ := 1
  have hdet : IsUnit G.det := (Matrix.isUnit_iff_isUnit_det G).mp hG.isUnit
  have hleft : G⁻¹ * G = 1 := Matrix.nonsing_inv_mul G hdet
  have hright : G * G⁻¹ = 1 := Matrix.mul_nonsing_inv G hdet
  have htrace : (h : ℂ) * (Fintype.card ι : ℂ) - (star e ⬝ᵥ (G⁻¹ *ᵥ e)) = 0 := calc
    _ = (G⁻¹ * ((h : ℂ) • G - Matrix.vecMulVec e (star e))).trace := by
      rw [mul_sub, Matrix.mul_smul, hleft, Matrix.trace_sub, Matrix.trace_smul,
        Matrix.trace_one, Matrix.mul_vecMulVec, Matrix.trace_vecMulVec,
        dotProduct_comm (G⁻¹ *ᵥ e) (star e), smul_eq_mul]
    _ = (G⁻¹ * (G * D + Dᴴ * G)).trace :=
      congrArg (fun M : Matrix ι ι ℂ => (G⁻¹ * M).trace) (gram_identity h ω hh)
    _ = 0 := by
      rw [mul_add, Matrix.trace_add, ← Matrix.mul_assoc G⁻¹ G D, hleft, one_mul,
        ← Matrix.mul_assoc G⁻¹ Dᴴ G, Matrix.trace_mul_cycle G⁻¹ Dᴴ G, hright, one_mul]
      change (generator ω).trace + ((generator ω)ᴴ).trace = 0
      rw [generator_conjTranspose, Matrix.trace_neg, add_neg_cancel]
  simpa only [Complex.ofReal_mul, Complex.ofReal_natCast] using (sub_eq_zero.mp htrace).symm

private lemma star_dotProduct_ones (a : ι → ℂ) :
    star a ⬝ᵥ (1 : ι → ℂ) = star (∑ i, a i) := by
  rw [star_dotProduct]
  simp [dotProduct]

/-- The sharp matrix inequality and its equality vector, assuming positivity.
The statement also applies when the index type is empty. -/
private theorem matrix_evaluation_of_posDef [DecidableEq ι] (h : ℝ) (ω : ι → ℝ) (hh : 0 < h)
    (hG : (gram h ω).PosDef) :
    let G := gram h ω
    let b := G⁻¹ *ᵥ (1 : ι → ℂ)
    (∀ a : ι → ℂ, ‖∑ i, a i‖ ^ 2 ≤
      (h * (Fintype.card ι : ℝ)) * (star a ⬝ᵥ (G *ᵥ a)).re) ∧
    ‖∑ i, b i‖ ^ 2 =
      (h * (Fintype.card ι : ℝ)) * (star b ⬝ᵥ (G *ᵥ b)).re := by
  dsimp only
  let G := gram h ω
  let b := G⁻¹ *ᵥ (1 : ι → ℂ)
  have hdet : IsUnit G.det := (Matrix.isUnit_iff_isUnit_det G).mp hG.isUnit
  have hb : G *ᵥ b = (1 : ι → ℂ) := by
    dsimp only [b]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv G hdet, Matrix.one_mulVec]
  have hsum : (∑ i, b i) = ((h * (Fintype.card ι : ℝ) : ℝ) : ℂ) := by
    simpa only [b, G, star_one, dotProduct, Pi.one_apply, one_mul] using
      inverse_evaluation h ω hh hG
  have hform : (star b ⬝ᵥ (G *ᵥ b)).re = h * (Fintype.card ι : ℝ) := by
    rw [hb, star_dotProduct_ones, hsum]
    simp
  change (∀ a : ι → ℂ, ‖∑ i, a i‖ ^ 2 ≤
      (h * (Fintype.card ι : ℝ)) * (star a ⬝ᵥ (G *ᵥ a)).re) ∧
    ‖∑ i, b i‖ ^ 2 = (h * (Fintype.card ι : ℝ)) * (star b ⬝ᵥ (G *ᵥ b)).re
  refine ⟨fun a => ?_, ?_⟩
  · have hcs :=
      D5.S3.Quantum.Measurement.DetectorSensorDickeOptimality.psd_cauchy_schwarz
        G hG.posSemidef a b
    rw [hform, hb, star_dotProduct_ones] at hcs
    simpa only [Complex.star_def, Complex.norm_conj, mul_comm] using hcs
  · have hcard : 0 ≤ h * (Fintype.card ι : ℝ) := mul_nonneg hh.le (Nat.cast_nonneg _)
    rw [hform, hsum, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hcard, pow_two]

/-- Entire extension of the finite exponential sum on the real line. -/
def exponentialSum (ω : ι → ℝ) (a : ι → ℂ) (z : ℂ) : ℂ :=
  ∑ i, a i * Complex.exp (frequency ω i * z)

/-- The weighted squared norm of the sum at real time `s`. -/
def weightedDensity (h : ℝ) (ω : ι → ℝ) (a : ι → ℂ) (s : ℝ) : ℝ :=
  Real.exp (-h * s) * ‖exponentialSum ω a (s : ℂ)‖ ^ 2

/-- The weighted energy over the positive real half-line. The endpoint has zero
Lebesgue measure, so this is also the integral over the closed half-line. -/
def weightedEnergy (h : ℝ) (ω : ι → ℝ) (a : ι → ℂ) : ℝ :=
  ∫ s : ℝ in Ioi 0, weightedDensity h ω a s

private lemma star_mode (ω : ι → ℝ) (i : ι) (s : ℝ) :
    star (Complex.exp (frequency ω i * (s : ℂ))) =
      Complex.exp (-frequency ω i * (s : ℂ)) := by
  change (starRingEnd ℂ) (Complex.exp (frequency ω i * (s : ℂ))) = _
  rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal]
  exact congrArg (fun z : ℂ => Complex.exp (z * (s : ℂ))) (star_frequency ω i)

private def pairIntegrand (h : ℝ) (ω : ι → ℝ) (a : ι → ℂ) (i j : ι) (s : ℝ) : ℂ :=
  (star (a i) * a j) * Complex.exp (-denominator h ω i j * (s : ℂ))

private lemma weightedDensity_expansion (h : ℝ) (ω : ι → ℝ) (a : ι → ℂ) (s : ℝ) :
    (weightedDensity h ω a s : ℂ) = ∑ i, ∑ j, pairIntegrand h ω a i j s := by
  rw [weightedDensity, Complex.ofReal_mul, ← Complex.normSq_eq_norm_sq,
    Complex.normSq_eq_conj_mul_self]
  change (Real.exp (-h * s) : ℂ) *
    (star (exponentialSum ω a (s : ℂ)) * exponentialSum ω a (s : ℂ)) = _
  simp only [exponentialSum, star_sum]
  rw [Finset.sum_mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [star_mul, star_mode, Complex.ofReal_exp, Complex.ofReal_mul, Complex.ofReal_neg]
  calc
    _ = (star (a i) * a j) *
        (Complex.exp (-(h : ℂ) * (s : ℂ)) *
          Complex.exp (-frequency ω i * (s : ℂ)) *
          Complex.exp (frequency ω j * (s : ℂ))) := by ring
    _ = pairIntegrand h ω a i j s := by
      have harg : -(h : ℂ) * (s : ℂ) + -frequency ω i * (s : ℂ) +
          frequency ω j * (s : ℂ) = -denominator h ω i j * (s : ℂ) := by
        unfold denominator
        ring
      rw [← Complex.exp_add, ← Complex.exp_add, harg, pairIntegrand]

private lemma neg_denominator_re_lt_zero {h : ℝ} (hh : 0 < h) (ω : ι → ℝ) (i j : ι) :
    (-denominator h ω i j).re < 0 := by
  simpa only [Complex.neg_re, denominator_re, neg_lt_zero] using hh

private lemma integral_mode_pair {h : ℝ} (hh : 0 < h) (ω : ι → ℝ) (i j : ι) :
    (∫ s : ℝ in Ioi 0, Complex.exp (-denominator h ω i j * (s : ℂ))) =
      gram h ω i j := by
  rw [integral_exp_mul_complex_Ioi (neg_denominator_re_lt_zero hh ω i j)]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, neg_div_neg_eq,
    gram, Matrix.of_apply]

/-- The exponentially weighted squared norm is integrable and its complex cast
is the Gram quadratic form. The pair integrals use the complex Laplace formula. -/
theorem weightedEnergy_eq_gram (h : ℝ) (ω : ι → ℝ) (hh : 0 < h) (a : ι → ℂ) :
    IntegrableOn (weightedDensity h ω a) (Ioi 0) ∧
      (weightedEnergy h ω a : ℂ) = star a ⬝ᵥ (gram h ω *ᵥ a) := by
  have hp (i j : ι) : IntegrableOn (pairIntegrand h ω a i j) (Ioi 0) :=
    (integrableOn_exp_mul_complex_Ioi (neg_denominator_re_lt_zero hh ω i j) 0).const_mul _
  have hsum : IntegrableOn (fun s => ∑ i, ∑ j, pairIntegrand h ω a i j s) (Ioi 0) :=
    integrable_finsetSum Finset.univ (fun i _ =>
      integrable_finsetSum Finset.univ (fun j _ => hp i j))
  have hexpand : (fun s : ℝ => (weightedDensity h ω a s : ℂ)) =
      fun s => ∑ i, ∑ j, pairIntegrand h ω a i j s :=
    funext (weightedDensity_expansion h ω a)
  refine ⟨?_, ?_⟩
  · rw [← hexpand] at hsum
    change Integrable (weightedDensity h ω a) (volume.restrict (Ioi 0))
    simpa only [RCLike.re_eq_complex_re, Complex.ofReal_re] using Integrable.re hsum
  · have hcast : (weightedEnergy h ω a : ℂ) =
        ∫ s : ℝ in Ioi 0, (weightedDensity h ω a s : ℂ) :=
      (integral_ofReal (𝕜 := ℂ) (f := weightedDensity h ω a)
        (μ := volume.restrict (Ioi (0 : ℝ)))).symm
    rw [hcast, hexpand]
    rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hp i j))]
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Pi.star_apply]
    apply Finset.sum_congr rfl
    intro i _
    rw [integral_finsetSum _ (fun j _ => hp i j)]
    simp only [pairIntegrand, integral_const_mul, integral_mode_pair hh]
    apply Finset.sum_congr rfl
    intro j _
    ring

private lemma gram_isHermitian (h : ℝ) (ω : ι → ℝ) : (gram h ω).IsHermitian := by
  change (gram h ω)ᴴ = gram h ω
  apply Matrix.ext
  intro i j
  rw [Matrix.conjTranspose_apply]
  have hs : star (denominator h ω j i) = denominator h ω i j := by
    unfold denominator
    rw [star_sub, star_sub, star_frequency, star_frequency, Complex.star_def,
      Complex.conj_ofReal]
    ring
  change (starRingEnd ℂ) (1 / denominator h ω j i) = 1 / denominator h ω i j
  rw [map_div₀, map_one]
  exact congrArg (fun z : ℂ => 1 / z) hs

private lemma exponentialSum_eq_zero_of_real (ω : ι → ℝ) (a : ι → ℂ)
    (hz : ∀ s : ℝ, 0 < s → exponentialSum ω a (s : ℂ) = 0) :
    exponentialSum ω a = 0 := by
  have ha : AnalyticOnNhd ℂ (exponentialSum ω a) univ := by
    intro z _
    unfold exponentialSum
    apply Finset.analyticAt_fun_sum
    intro i _
    exact analyticAt_const.mul ((analyticAt_const.mul analyticAt_id).cexp')
  have hz' : AnalyticOnNhd ℂ (0 : ℂ → ℂ) univ := by
    intro z _
    exact analyticAt_const
  have ht : Tendsto ((↑) : ℝ → ℂ) (𝓝[>] (0 : ℝ)) (𝓝[≠] ((0 : ℝ) : ℂ)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · exact Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with x hx
      exact Set.mem_compl_singleton_iff.mpr (Complex.ofReal_injective.ne (ne_of_gt hx))
  have he : ∀ᶠ s : ℝ in 𝓝[>] (0 : ℝ), exponentialSum ω a (s : ℂ) = 0 := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact hz s hs
  have hf : ∃ᶠ z : ℂ in 𝓝[≠] (0 : ℂ), exponentialSum ω a z = 0 := by
    simpa only [Complex.ofReal_zero] using
      ht.frequently (p := fun z => exponentialSum ω a z = 0) he.frequently
  exact ha.eq_of_frequently_eq hz' hf

private lemma coefficients_eq_zero (ω : ι → ℝ) (a : ι → ℂ)
    (hω : Function.Injective ω) (hz : exponentialSum ω a = 0) : a = 0 := by
  have hfreq : Function.Injective (frequency ω) := by
    intro i j hij
    apply hω
    simpa [frequency, Complex.mul_im] using congrArg Complex.im hij
  have hblocks : (fun i => Polynomial.C (a i)) = 0 := by
    apply block_evaluation_injective (frequency ω) hfreq
    rw [map_zero]
    funext z
    change (∑ i, Complex.exp (frequency ω i * z) * (Polynomial.C (a i)).eval z) = 0
    simpa only [Polynomial.eval_C, mul_comm, exponentialSum, Pi.zero_apply] using congrFun hz z
  funext i
  apply Polynomial.C_injective
  simpa only [Pi.zero_apply, map_zero] using congrFun hblocks i

/-- Distinct real frequencies yield a positive definite Gram matrix.
A zero energy forces the entire sum to vanish, and injectivity of evaluation
for constant polynomial blocks forces the coefficients to vanish. -/
private theorem gram_posDef (h : ℝ) (ω : ι → ℝ) (hh : 0 < h) (hω : Function.Injective ω) :
    (gram h ω).PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos (gram_isHermitian h ω) ?_
  intro a ha
  obtain ⟨hint, hform⟩ := weightedEnergy_eq_gram h ω hh a
  rw [← hform, Complex.pos_iff, Complex.ofReal_re, Complex.ofReal_im]
  refine ⟨?_, rfl⟩
  have hn : 0 ≤ weightedDensity h ω a := fun s =>
    mul_nonneg (Real.exp_pos _).le (sq_nonneg _)
  refine lt_of_le_of_ne (integral_nonneg hn) ?_
  intro hz
  have hae := (integral_eq_zero_iff_of_nonneg hn hint).mp hz.symm
  have hc : Continuous (weightedDensity h ω a) := by
    unfold weightedDensity exponentialSum
    fun_prop
  have hOn := Measure.eqOn_open_of_ae_eq (μ := volume) hae isOpen_Ioi
    hc.continuousOn continuous_const.continuousOn
  apply ha
  apply coefficients_eq_zero ω a hω
  apply exponentialSum_eq_zero_of_real
  intro s hs
  have hs' : Real.exp (-h * s) * ‖exponentialSum ω a (s : ℂ)‖ ^ 2 = 0 := hOn hs
  have hs'' := (mul_eq_zero.mp hs').resolve_left (Real.exp_pos _).ne'
  exact norm_eq_zero.mp ((pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)).mp hs'')

/-- Sharp weighted evaluation bound, with equality at the inverse Gram matrix
applied to the all-ones vector. The empty family has zero energy and evaluation. -/
theorem weighted_evaluation [DecidableEq ι] (h : ℝ) (ω : ι → ℝ) (hh : 0 < h)
    (hω : Function.Injective ω) :
    let b := (gram h ω)⁻¹ *ᵥ (1 : ι → ℂ)
    (∀ a : ι → ℂ, ‖∑ i, a i‖ ^ 2 ≤
      (h * (Fintype.card ι : ℝ)) * weightedEnergy h ω a) ∧
    ‖∑ i, b i‖ ^ 2 = (h * (Fintype.card ι : ℝ)) * weightedEnergy h ω b := by
  have hform (a : ι → ℂ) : (star a ⬝ᵥ (gram h ω *ᵥ a)).re = weightedEnergy h ω a := by
    rw [← (weightedEnergy_eq_gram h ω hh a).2, Complex.ofReal_re]
  simpa only [hform] using matrix_evaluation_of_posDef h ω hh (gram_posDef h ω hh hω)

private lemma exponentialSum_zero (ω : ι → ℝ) (a : ι → ℂ) :
    exponentialSum ω a 0 = ∑ i, a i := by
  simp [exponentialSum]

/-- For a nonempty family, the inverse-Gram equality witness has positive energy,
so the constant is optimal for evaluation at zero on the closed half-line. -/
theorem weighted_evaluation_least_constant [Nonempty ι]
    (h : ℝ) (ω : ι → ℝ) (hh : 0 < h) (hω : Function.Injective ω) :
    IsLeast {C : ℝ | ∀ a : ι → ℂ, ‖exponentialSum ω a 0‖ ^ 2 ≤
      C * (∫ s : ℝ in Ici 0, weightedDensity h ω a s)} (h * (Fintype.card ι : ℝ)) := by
  classical
  let G := gram h ω
  let b := G⁻¹ *ᵥ (1 : ι → ℂ)
  have hG : G.PosDef := gram_posDef h ω hh hω
  have hdet : IsUnit G.det := (Matrix.isUnit_iff_isUnit_det G).mp hG.isUnit
  have hb : G *ᵥ b = (1 : ι → ℂ) := by
    dsimp only [b]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv G hdet, Matrix.one_mulVec]
  have hsum : (∑ i, b i) = ((h * (Fintype.card ι : ℝ) : ℝ) : ℂ) := by
    simpa only [b, G, star_one, dotProduct, Pi.one_apply, one_mul] using
      inverse_evaluation h ω hh hG
  have henergy : 0 < weightedEnergy h ω b := by
    have hform := congrArg Complex.re (weightedEnergy_eq_gram h ω hh b).2
    change (weightedEnergy h ω b : ℂ).re = (star b ⬝ᵥ (G *ᵥ b)).re at hform
    rw [Complex.ofReal_re, hb, star_dotProduct_ones, hsum] at hform
    simp only [Complex.star_def, Complex.conj_ofReal, Complex.ofReal_re] at hform
    rw [hform]
    exact mul_pos hh (Nat.cast_pos.mpr Fintype.card_pos)
  obtain ⟨hle, heq⟩ := weighted_evaluation h ω hh hω
  refine ⟨?_, ?_⟩
  · intro a
    rw [exponentialSum_zero, integral_Ici_eq_integral_Ioi]
    exact hle a
  · intro C hC
    have hbound := hC b
    rw [exponentialSum_zero, integral_Ici_eq_integral_Ioi] at hbound
    change ‖∑ i, b i‖ ^ 2 ≤ C * weightedEnergy h ω b at hbound
    rw [heq] at hbound
    exact le_of_mul_le_mul_right hbound henergy

end ExponentialGramWeightedEvaluation
