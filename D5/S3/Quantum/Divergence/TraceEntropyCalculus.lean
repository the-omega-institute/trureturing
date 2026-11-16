/- GID: D5/S3/Quantum/Divergence/TraceEntropyCalculus
   generality: G
   mirror-B: D5/B/S3/Quantum/Divergence/TraceEntropyCalculus
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Two-sided differentiation of noncommuting finite-matrix trace entropy. -/

import D5.S3.Quantum.Divergence.SpectralCeilingRelativeEntropy
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-! proof_shape: content; admission_basis: escape-witness.
The two Klein inequalities bound the entropy remainder by a trace product of
the matrix increment and the logarithm increment. Its normalized norm tends
to zero on both sides of the time point. AmplifiedPauliEntropyFlow consumes
this chain rule for the actual dissipative matrix curve. These are analytic
statements, not finite certificates or numerical reductions; utility is none.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open Filter Matrix
open scoped Topology ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open D5.S3.Quantum.Divergence.SpectralCeilingRelativeEntropy

namespace D5.S3.Quantum.Divergence.TraceEntropyCalculus

variable {i : Type*} [Fintype i] [DecidableEq i]

private lemma eventually_posDef {X : ℝ → Matrix i i ℂ} {t₀ : ℝ}
    (hX : ContinuousAt X t₀) (hH : ∀ᶠ t in 𝓝 t₀, (X t).IsHermitian)
    (h₀ : (X t₀).PosDef) : ∀ᶠ t in 𝓝 t₀, (X t).PosDef := by
  cases isEmpty_or_nonempty i with
  | inl hi =>
    letI := hi
    exact Eventually.of_forall fun t => by
      simpa only [Subsingleton.elim (X t) 1] using (Matrix.PosDef.one :
        (1 : Matrix i i ℂ).PosDef)
  | inr hi =>
    letI := hi
    obtain ⟨r, hr, hrA⟩ := (CFC.exists_pos_algebraMap_le_iff (X t₀)).mpr
      (fun x hx => h₀.isStrictlyPositive.spectrum_pos hx)
    have hn : Tendsto (fun t => ‖X t - X t₀‖) (𝓝 t₀) (𝓝 0) := by
      simpa using (hX.sub (continuousAt_const (y := X t₀))).norm.tendsto
    filter_upwards [hH, hn.eventually (gt_mem_nhds (half_pos hr))] with t ht hnorm
    have hd : IsSelfAdjoint (X t - X t₀) := ht.sub h₀.isHermitian
    have hl : -(algebraMap ℝ (Matrix i i ℂ) (r / 2)) ≤ X t - X t₀ :=
      (neg_le_neg (algebraMap_mono (Matrix i i ℂ) hnorm.le)).trans
        hd.neg_algebraMap_norm_le_self
    have hfloor : algebraMap ℝ (Matrix i i ℂ) (r / 2) ≤ X t := by
      calc
        algebraMap ℝ (Matrix i i ℂ) (r / 2) =
            algebraMap ℝ (Matrix i i ℂ) r - algebraMap ℝ (Matrix i i ℂ) (r / 2) := by
          rw [← map_sub]
          congr 1
          ring
        _ ≤ X t₀ + (X t - X t₀) := add_le_add hrA hl
        _ = X t := by abel
    exact ((isStrictlyPositive_algebraMap (A := Matrix i i ℂ) (half_pos hr)).of_le
      hfloor).posDef

private lemma klein_remainder_bounds (A B : Matrix i i ℂ)
    (hA : A.PosDef) (hB : B.PosDef) (M : ℝ) (hM : 0 < M)
    (hAM : A ≤ (M : ℂ) • 1) (hBM : B ≤ (M : ℂ) • 1) :
    0 ≤ (B * cfc Real.log B).trace.re - (A * cfc Real.log A).trace.re -
        ((B - A) * (cfc Real.log A + 1)).trace.re ∧
    (B * cfc Real.log B).trace.re - (A * cfc Real.log A).trace.re -
        ((B - A) * (cfc Real.log A + 1)).trace.re ≤
      ((B - A) * (cfc Real.log B - cfc Real.log A)).trace.re := by
  have supportA : ∀ v, A *ᵥ v = 0 → B *ᵥ v = 0 := by
    intro v hv
    have : v = 0 := hA.mulVec_injective (by simpa using hv)
    simp [this]
  have supportB : ∀ v, B *ᵥ v = 0 → A *ᵥ v = 0 := by
    intro v hv
    have : v = 0 := hB.mulVec_injective (by simpa using hv)
    simp [this]
  have hab := actual_matrix_spectral_ceiling_strong_klein B A hB.posSemidef
    hA.posSemidef M hM hBM hAM supportA
  have hba := actual_matrix_spectral_ceiling_strong_klein A B hA.posSemidef
    hB.posSemidef M hM hAM hBM supportB
  have q (C : Matrix i i ℂ) : 0 ≤ (Cᴴ * C).trace.re / (2 * M) :=
    div_nonneg (Complex.nonneg_iff.mp (Matrix.posSemidef_conjTranspose_mul_self C).trace_nonneg).1
      (by positivity)
  have hab' := (q (B - A)).trans hab
  have hba' := (q (A - B)).trans hba
  simp only [mul_add, mul_sub, sub_mul, mul_one, Matrix.trace_add,
    Matrix.trace_sub, Complex.add_re, Complex.sub_re] at hab' hba' ⊢
  constructor <;> linarith

/-- The real chain rule for trace entropy, with no trace or commutation restriction.
The derivative and all continuity statements use the L2 operator norm. -/
theorem hasDerivAt_trace_mul_log (X : ℝ → Matrix i i ℂ) (V : Matrix i i ℂ) (t₀ : ℝ)
    (hX : HasDerivAt X V t₀) (hH : ∀ᶠ t in 𝓝 t₀, (X t).IsHermitian)
    (h₀ : (X t₀).PosDef) :
    HasDerivAt (fun t => (X t * cfc Real.log (X t)).trace.re)
      (V * (cfc Real.log (X t₀) + 1)).trace.re t₀ := by
  let A := X t₀
  let T : Matrix i i ℂ →L[ℝ] ℝ :=
    Complex.reCLM.comp (Matrix.traceLinearMap i ℝ ℂ).toContinuousLinearMap
  let R : ℝ → ℝ := fun t =>
    T (X t * cfc Real.log (X t)) - T (A * cfc Real.log A) -
      T ((X t - A) * (cfc Real.log A + 1))
  let Q : ℝ → Matrix i i ℂ := fun t => (t - t₀)⁻¹ • (X t - A)
  have hpd := eventually_posDef hX.continuousAt hH h₀
  have hlog : Tendsto (fun t => cfc Real.log (X t)) (𝓝 t₀)
      (𝓝 (cfc Real.log A)) := by
    have hm : ∀ᶠ t in 𝓝 t₀, X t ∈ {B : Matrix i i ℂ | IsSelfAdjoint B ∧ IsUnit B} :=
      hpd.mono fun t ht => ⟨ht.isHermitian, ht.isUnit⟩
    exact (CFC.continuousOn_log.continuousWithinAt
      ⟨h₀.isHermitian, h₀.isUnit⟩).tendsto.comp
        (tendsto_nhdsWithin_iff.mpr ⟨hX.continuousAt, hm⟩)
  have hQ : Tendsto Q (𝓝[≠] t₀) (𝓝 V) := by
    change Tendsto (slope X t₀) (𝓝[≠] t₀) (𝓝 V)
    exact hX.tendsto_slope
  have hK : Tendsto (fun t => cfc Real.log (X t) - cfc Real.log A)
      (𝓝[≠] t₀) (𝓝 0) := by
    simpa using (hlog.sub (tendsto_const_nhds (x := cfc Real.log A))).mono_left
      (nhdsWithin_le_nhds (s := {t₀}ᶜ))
  have hpair : Tendsto (fun t => T (Q t * (cfc Real.log (X t) - cfc Real.log A)))
      (𝓝[≠] t₀) (𝓝 0) := by
    simpa only [Function.comp_def, mul_zero, map_zero] using
      (T.continuous.tendsto _).comp (hQ.mul hK)
  have hnear : ∀ᶠ t in 𝓝 t₀, ‖X t‖ < ‖A‖ + 1 :=
    (hX.continuousAt.norm.tendsto).eventually (gt_mem_nhds (by dsimp [A]; linarith))
  have hb : ∀ᶠ t in 𝓝 t₀, 0 ≤ R t ∧ R t ≤
      T ((X t - A) * (cfc Real.log (X t) - cfc Real.log A)) := by
    filter_upwards [hpd, hnear] with t ht hnorm
    have hcast : algebraMap ℝ (Matrix i i ℂ) (‖A‖ + 1) =
        ((‖A‖ + 1 : ℝ) : ℂ) • (1 : Matrix i i ℂ) := by
      ext j k
      simp [Algebra.algebraMap_eq_smul_one, Complex.real_smul]
    have hAM : A ≤ ((‖A‖ + 1 : ℝ) : ℂ) • (1 : Matrix i i ℂ) := by
      rw [← hcast]
      exact (CStarAlgebra.norm_le_iff_le_algebraMap A (by positivity) h₀.posSemidef.nonneg).mp
        (by linarith : ‖A‖ ≤ ‖A‖ + 1)
    have hBM : X t ≤ ((‖A‖ + 1 : ℝ) : ℂ) • (1 : Matrix i i ℂ) := by
      rw [← hcast]
      exact (CStarAlgebra.norm_le_iff_le_algebraMap (X t) (by positivity)
        ht.posSemidef.nonneg).mp hnorm.le
    exact klein_remainder_bounds A (X t) h₀ ht (‖A‖ + 1) (by positivity) hAM hBM
  have hR : Tendsto (fun t => (t - t₀)⁻¹ * R t) (𝓝[≠] t₀) (𝓝 0) := by
    apply squeeze_zero_norm' (a := fun t =>
      ‖T (Q t * (cfc Real.log (X t) - cfc Real.log A))‖) _ (by simpa using hpair.norm)
    filter_upwards [hb.filter_mono nhdsWithin_le_nhds] with t ht
    have he : T (Q t * (cfc Real.log (X t) - cfc Real.log A)) =
        (t - t₀)⁻¹ * T ((X t - A) * (cfc Real.log (X t) - cfc Real.log A)) := by
      simp only [Q, smul_mul_assoc, map_smul, smul_eq_mul]
    rw [he, norm_mul, norm_mul]
    exact mul_le_mul_of_nonneg_left
      (by rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg ht.1,
              abs_of_nonneg (ht.1.trans ht.2)]; exact ht.2) (norm_nonneg _)
  have hlinear : Tendsto (fun t => T (Q t * (cfc Real.log A + 1)))
      (𝓝[≠] t₀) (𝓝 (T (V * (cfc Real.log A + 1)))) :=
    (T.continuous.tendsto _).comp (hQ.mul tendsto_const_nhds)
  change HasDerivAt (fun t => T (X t * cfc Real.log (X t)))
    (T (V * (cfc Real.log A + 1))) t₀
  apply hasDerivAt_iff_tendsto_slope.mpr
  have hs := hlinear.add hR
  rw [add_zero] at hs
  apply hs.congr'
  filter_upwards [] with t
  simp only [slope_def_field, Q, R, smul_mul_assoc, map_smul, smul_eq_mul]
  ring

-- This unequal-trace curve detects the identity correction at the identity.
example : HasDerivAt
    (fun t : ℝ => ((Real.exp t • (1 : Matrix Unit Unit ℂ)) *
      cfc Real.log (Real.exp t • (1 : Matrix Unit Unit ℂ))).trace.re) 1 0 := by
  let X : ℝ → Matrix Unit Unit ℂ := fun t => Real.exp t • 1
  have hd : HasDerivAt X 1 0 := by
    simpa [X] using (Real.hasDerivAt_exp 0).smul_const (1 : Matrix Unit Unit ℂ)
  have hp (t : ℝ) : (X t).PosDef := Matrix.PosDef.one.smul (Real.exp_pos t)
  simpa [X] using hasDerivAt_trace_mul_log X 1 0 hd
    (Eventually.of_forall fun t => (hp t).isHermitian) (hp 0)

end D5.S3.Quantum.Divergence.TraceEntropyCalculus
