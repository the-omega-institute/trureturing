/- GID: D5/S3/Observer/Linear/GaussianObservationLaw
   generality: G
   mirror-B: D5/B/S3/Observer/Linear/GaussianObservationLaw
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual Gaussian observation laws have their posterior disintegration and Radon–Nikodym information identities. -/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Order.Lattice.Nat
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.Order
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.Probability.Kernel.CompProdEqIff
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.LogLikelihoodRatio
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
import Mathlib.Probability.Kernel.Composition.Prod
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Probability.Kernel.Disintegration.Basic
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Topology.Instances.Matrix
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.Asymptotics.Lemmas

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Observer.Linear.GaussianObservationLaw
open MeasureTheory ProbabilityTheory WithLp ContinuousLinearMap Set Module
open scoped BigOperators ENNReal InnerProductSpace RealInnerProductSpace ProbabilityTheory MatrixOrder Topology Matrix.Norms.L2Operator

abbrev E (n : Type) := EuclideanSpace ℝ n

def action {d a : Type} [Fintype d] [DecidableEq d] [Fintype a] [DecidableEq a]
    (M : Matrix a d ℝ) : E d →L[ℝ] E a := (Matrix.toEuclideanLin M).toContinuousLinearMap

variable {n p : Type} [Fintype n] [DecidableEq n] [Fintype p] [DecidableEq p]

def precision (M : Matrix p n ℝ) (β τ : ℝ) : Matrix n n ℝ := β • (1 : Matrix n n ℝ) + τ • (M.transpose * M)

def covariance (M : Matrix p n ℝ) (β τ : ℝ) : Matrix n n ℝ := (precision M β τ)⁻¹

def ambientCov (β τ : ℝ) : Matrix (n ⊕ p) (n ⊕ p) ℝ := Matrix.fromBlocks (β⁻¹ • (1 : Matrix n n ℝ)) 0 0 (τ⁻¹ • (1 : Matrix p p ℝ))

def signal : Matrix n (n ⊕ p) ℝ := Matrix.fromCols 1 0

def noise : Matrix p (n ⊕ p) ℝ := Matrix.fromCols 0 1

def observation (M : Matrix p n ℝ) : Matrix p (n ⊕ p) ℝ := Matrix.fromCols M 1

def gain (M : Matrix p n ℝ) (β τ : ℝ) : Matrix n p ℝ := τ • (covariance M β τ * M.transpose)

def innovation (M : Matrix p n ℝ) (β τ : ℝ) : Matrix n (n ⊕ p) ℝ := Matrix.fromCols (β • covariance M β τ) (-gain M β τ)

def inputLaw (β τ : ℝ) : Measure (E (n ⊕ p)) := multivariateGaussian 0 (ambientCov β τ)

def dataLaw (M : Matrix p n ℝ) (β τ : ℝ) : Measure (E p) := (inputLaw β τ).map (action (observation M))

def jointLaw (M : Matrix p n ℝ) (β τ : ℝ) : Measure (E p × E n) := (inputLaw β τ).map (fun z => (action (observation M) z, action signal z))

def translatedKernel (K : E p →L[ℝ] E n) (ν : Measure (E n)) : Kernel (E p) (E n) := ((Kernel.id : Kernel (E p) (E p)) ×ₖ Kernel.const (E p) ν).map
    (fun z : E p × E n => K z.1 + z.2)

def posteriorKernel (M : Matrix p n ℝ) (β τ : ℝ) : Kernel (E p) (E n) := translatedKernel (action (gain M β τ)) (multivariateGaussian 0 (covariance M β τ))

def differentialEntropy (μ : Measure (E n)) : ℝ := -(∫ x, Real.log ((μ.rnDeriv volume x).toReal) ∂μ)

def physicalEnergy (x : E n) : ℝ := (∑ i, (x i) ^ 2) / 2

def physicalFreeEnergy (β : ℝ) (μ : Measure (E n)) : ℝ := (∫ x, physicalEnergy x ∂μ) - β⁻¹ * differentialEntropy μ

def mutualInformation (M : Matrix p n ℝ) (β τ : ℝ) : ℝ≥0∞ := InformationTheory.klDiv (jointLaw M β τ) ((jointLaw M β τ).fst.prod (jointLaw M β τ).snd)


theorem gaussian_observation_law {n p : Type} [Fintype n] [DecidableEq n] [Fintype p] [DecidableEq p]
    (M : Matrix p n ℝ) (β σ : ℝ) (hβ : 0 < β) (hσ : 0 < σ ^ 2) :
  let τ := (σ ^ 2)⁻¹
  mutualInformation M β τ ≠ ∞ ∧
    Integrable
      (llr (((inputLaw (n := n) (p := p) β τ).map (fun z => (action (observation M) z, action (signal (n := n) (p := p)) z))))
        ((((inputLaw (n := n) (p := p) β τ).map (fun z => (action (observation M) z, action (signal (n := n) (p := p)) z)))).fst.prod (((inputLaw (n := n) (p := p) β τ).map (fun z => (action (observation M) z, action (signal (n := n) (p := p)) z)))).snd))
      (((inputLaw (n := n) (p := p) β τ).map (fun z => (action (observation M) z, action (signal (n := n) (p := p)) z)))) ∧
    (∫ z : E p × E n,
      llr (((inputLaw (n := n) (p := p) β τ).map (fun z => (action (observation M) z, action (signal (n := n) (p := p)) z))))
        ((((inputLaw (n := n) (p := p) β τ).map (fun z => (action (observation M) z, action (signal (n := n) (p := p)) z)))).fst.prod (((inputLaw (n := n) (p := p) β τ).map (fun z => (action (observation M) z, action (signal (n := n) (p := p)) z)))).snd) z
        ∂((inputLaw (n := n) (p := p) β τ).map (fun z => (action (observation M) z, action (signal (n := n) (p := p)) z)))) =
      (Real.log ((β⁻¹ • (1 : Matrix n n ℝ)).det) -
        Real.log ((covariance M β τ).det)) / 2 ∧
    (mutualInformation M β τ).toReal =
      (Real.log ((β⁻¹ • (1 : Matrix n n ℝ)).det) -
        Real.log ((covariance M β τ).det)) / 2 ∧
    (mutualInformation M β τ).toReal =
      Real.log ((1 + (τ / β) • (M.transpose * M)).det) / 2 ∧
    ((∫ y : E p, physicalFreeEnergy β (posteriorKernel M β τ y)
        ∂((inputLaw (n := n) (p := p) β τ).map (action (observation M)))) -
      physicalFreeEnergy β
        (multivariateGaussian 0 (β⁻¹ • (1 : Matrix n n ℝ)))) =
      β⁻¹ * (mutualInformation M β τ).toReal ∧
    ((inputLaw (n := n) (p := p) β τ).map (fun z => (action (observation M) z, action (signal (n := n) (p := p)) z))) = ((inputLaw (n := n) (p := p) β τ).map (action (observation M))) ⊗ₘ posteriorKernel M β τ ∧
    ((inputLaw (n := n) (p := p) β τ).map (action signal) =
      multivariateGaussian 0 (β⁻¹ • (1 : Matrix n n ℝ)) ∧
    (inputLaw (n := n) (p := p) β τ).map (action noise) =
      multivariateGaussian 0 (τ⁻¹ • (1 : Matrix p p ℝ)) ∧
    IndepFun (action (signal (n := n) (p := p))) (action noise) (inputLaw β τ)) := by
  classical
  let transportedGaussianDensity (c : ℝ≥0∞) (S : Matrix n n ℝ)
      (m x : E n) : ℝ≥0∞ :=
    c * ENNReal.ofReal (∏ i, ProbabilityTheory.gaussianPDFReal 0 1
      ((action (CFC.sqrt S)⁻¹) (x - m) i))

  intro τ
  have hτ : 0 < τ := inv_pos.mpr hσ
  have action_apply {d a : Type} [Fintype d] [DecidableEq d] [Fintype a] [DecidableEq a] (M : Matrix a d ℝ) (x : E d) : action M x = toLp 2 (M.mulVec (ofLp x)) := rfl
  have action_comp {d a b : Type} [Fintype d] [DecidableEq d] [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (M : Matrix a b ℝ) (N : Matrix b d ℝ) :
      (action M).comp (action N) = action (M * N) := by
    ext x
    simp only [ContinuousLinearMap.comp_apply, action_apply, ofLp_toLp, Matrix.mulVec_mulVec]
  have action_add {d a : Type} [Fintype d] [DecidableEq d] [Fintype a] [DecidableEq a] (M N : Matrix a d ℝ) :
      action (M + N) = action M + action N := by
    ext x
    simp only [action_apply, ContinuousLinearMap.add_apply, Matrix.add_mulVec, WithLp.toLp_add]
  have inner_action {d a : Type} [Fintype d] [DecidableEq d] [Fintype a] [DecidableEq a] (M : Matrix a d ℝ) (x : E d) (y : E a) :
      ⟪action M x, y⟫_ℝ = ⟪x, action M.transpose y⟫_ℝ := by
    simpa only [EuclideanSpace.inner_eq_star_dotProduct, action_apply, ofLp_toLp, star_trivial, dotProduct_comm] using
      (Matrix.dotProduct_transpose_mulVec M (ofLp x) (ofLp y)).symm
  have action_adjoint {d a : Type} [Fintype d] [DecidableEq d] [Fintype a] [DecidableEq a] (M : Matrix a d ℝ) :
      (action M).adjoint = action M.transpose := by
    unfold action
    rw [← LinearMap.adjoint_toContinuousLinearMap, ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint, Matrix.conjTranspose_eq_transpose_of_trivial]
  have transpose_pairing {d a b : Type} [Fintype d] [DecidableEq d] [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (L : Matrix a d ℝ) (S : Matrix d d ℝ)
      (R : Matrix b d ℝ) (u : a → ℝ) (v : b → ℝ) : L.transpose.mulVec u ⬝ᵥ S.mulVec (R.transpose.mulVec v) =
        u ⬝ᵥ (L * S * R.transpose).mulVec v := by
    rw [dotProduct_comm (L.transpose.mulVec u), ← Matrix.dotProduct_transpose_mulVec L.transpose]
    simp only [Matrix.transpose_transpose, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  have action_cross_covariance {d a b : Type} [Fintype d] [DecidableEq d] [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (m : E d) (S : Matrix d d ℝ) (hS : S.PosSemidef)
      (L : Matrix a d ℝ) (R : Matrix b d ℝ) (u : E a) (v : E b) : cov[fun z => ⟪u, action L z⟫_ℝ, fun z => ⟪v, action R z⟫_ℝ;
        multivariateGaussian m S] = u ⬝ᵥ (L * S * R.transpose).mulVec v := by
    simp_rw [← ContinuousLinearMap.adjoint_inner_left, action_adjoint]
    rw [← covarianceBilin_apply_eq_cov IsGaussian.memLp_two_id, covarianceBilin_multivariateGaussian hS]
    exact transpose_pairing L S R (ofLp u) (ofLp v)
  have map_gaussian {d a : Type} [Fintype d] [DecidableEq d] [Fintype a] [DecidableEq a] (m : E d) (S : Matrix d d ℝ) (hS : S.PosSemidef) (L : Matrix a d ℝ) :
      (multivariateGaussian m S).map (action L) =
        multivariateGaussian (action L m) (L * S * L.transpose) := by
    have hLS : (L * S * L.transpose).PosSemidef := by
      simpa using hS.mul_mul_conjTranspose_same L
    apply IsGaussian.ext
    · change (∫ x, x ∂(multivariateGaussian m S).map (action L)) = ∫ x, x ∂multivariateGaussian (action L m) (L * S * L.transpose)
      rw [(action L).integral_id_map IsGaussian.integrable_id]
      simp only [integral_id_multivariateGaussian]
    · ext u v
      rw [covarianceBilin_map IsGaussian.memLp_two_id, covarianceBilin_multivariateGaussian hS, covarianceBilin_multivariateGaussian hLS, action_adjoint]
      exact transpose_pairing L S L (ofLp u) (ofLp v)
  have independent_actions {d a b : Type} [Fintype d] [DecidableEq d] [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (m : E d) (S : Matrix d d ℝ) (hS : S.PosSemidef)
      (L : Matrix a d ℝ) (R : Matrix b d ℝ) (hcross : L * S * R.transpose = 0) :
      IndepFun (action L) (action R) (multivariateGaussian m S) := by
    have hpair : HasGaussianLaw (fun z : E d => (action L z, action R z)) (multivariateGaussian m S) := (IsGaussian.hasGaussianLaw_id (μ := multivariateGaussian m S)).map_fun
        ((action L).prod (action R))
    apply hpair.indepFun_of_covariance_inner
    intro u v
    rw [action_cross_covariance m S hS L R, hcross, Matrix.zero_mulVec, dotProduct_zero]
  have translate_gaussian {d : Type} [Fintype d] [DecidableEq d] (m c : E d) (S : Matrix d d ℝ) : (multivariateGaussian m S).map (fun x => c + x) =
        multivariateGaussian (c + m) S := by
    unfold multivariateGaussian
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    congr 1
    funext x
    exact (add_assoc c m _).symm
  have precision_posDef (M : Matrix p n ℝ) (β τ : ℝ) (hβ : 0 < β) (hτ : 0 ≤ τ) :
      (precision M β τ).PosDef := by
    have hg : (M.transpose * M).PosSemidef := by
      simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
        Matrix.posSemidef_conjTranspose_mul_self M
    exact (Matrix.PosDef.one.smul hβ).add_posSemidef (hg.smul hτ)
  have ambientCov_posDef (β τ : ℝ) (hβ : 0 < β) (hτ : 0 < τ) :
      (ambientCov (n := n) (p := p) β τ).PosDef := by
    have hd : ambientCov (n := n) (p := p) β τ =
        Matrix.diagonal (Sum.elim (fun _ : n => β⁻¹) (fun _ : p => τ⁻¹)) := by
      ext i j
      rcases i with i | i <;> rcases j with j | j <;>
        simp [ambientCov, Matrix.fromBlocks, Matrix.diagonal, Matrix.one_apply]
    rw [hd, Matrix.posDef_diagonal_iff]
    intro i
    cases i with
    | inl i => exact inv_pos.mpr hβ
    | inr i => exact inv_pos.mpr hτ
  have innovation_times_cov (M : Matrix p n ℝ) (β τ : ℝ) (hβ : 0 < β) (hτ : 0 < τ) : innovation M β τ * ambientCov β τ =
        Matrix.fromCols (covariance M β τ) (-(covariance M β τ * M.transpose)) := by
    simp only [innovation, ambientCov, gain, Matrix.fromCols_mul_fromBlocks, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.smul_mul,
      Matrix.mul_smul, Matrix.mul_one, Matrix.neg_mul, smul_smul]
    simp [hβ.ne', hτ.ne', mul_comm]
  have signal_reconstruction (M : Matrix p n ℝ) (β τ : ℝ) (hβ : 0 < β) (hτ : 0 < τ) :
      signal (n := n) (p := p) = gain M β τ * observation M + innovation M β τ := by
    have hleft : gain M β τ * M + β • covariance M β τ = 1 := by
      have hu := (precision M β τ).isUnit_iff_isUnit_det.mp
        (precision_posDef M β τ hβ hτ.le).isUnit
      have hi : covariance M β τ * precision M β τ = 1 := by
        change (precision M β τ)⁻¹ * precision M β τ = 1
        exact Matrix.nonsing_inv_mul _ hu
      simpa only [precision, gain, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_assoc, add_comm] using hi
    rw [observation, innovation, Matrix.mul_fromCols, Matrix.mul_one]
    ext i j
    rcases j with j | j
    · change (1 : Matrix n n ℝ) i j = (gain M β τ * M) i j + (β • covariance M β τ) i j
      exact (congrArg (fun A : Matrix n n ℝ => A i j) hleft).symm
    · simp [signal]
  have innovation_data_covariance_zero (M : Matrix p n ℝ) (β τ : ℝ) (hβ : 0 < β) (hτ : 0 < τ) : innovation M β τ * ambientCov β τ * (observation M).transpose =
        (0 : Matrix n p ℝ) := by
    rw [innovation_times_cov M β τ hβ hτ, observation, Matrix.transpose_fromCols, Matrix.fromCols_mul_fromRows]
    simp
  have innovation_signal_covariance (M : Matrix p n ℝ) (β τ : ℝ) (hβ : 0 < β) (hτ : 0 < τ) : innovation M β τ * ambientCov β τ * (signal (n := n) (p := p)).transpose =
        covariance M β τ := by
    rw [innovation_times_cov M β τ hβ hτ, signal, Matrix.transpose_fromCols, Matrix.fromCols_mul_fromRows]
    simp
  have innovation_covariance (M : Matrix p n ℝ) (β τ : ℝ) (hβ : 0 < β) (hτ : 0 < τ) : innovation M β τ * ambientCov β τ * (innovation M β τ).transpose =
        covariance M β τ := by
    have h := innovation_signal_covariance M β τ hβ hτ
    rw [signal_reconstruction M β τ hβ hτ, Matrix.transpose_add, Matrix.transpose_mul, Matrix.mul_add, ← Matrix.mul_assoc,
      innovation_data_covariance_zero M β τ hβ hτ, Matrix.zero_mul, zero_add] at h
    exact h
  letI inputLaw_probability (β τ : ℝ) :
      IsProbabilityMeasure (inputLaw (n := n) (p := p) β τ) := by
    unfold inputLaw
    infer_instance
  have input_factors (β τ : ℝ) (hβ : 0 < β) (hτ : 0 < τ) : (inputLaw (n := n) (p := p) β τ).map (action signal) = multivariateGaussian 0 (β⁻¹ • (1 : Matrix n n ℝ)) ∧
      (inputLaw (n := n) (p := p) β τ).map (action noise) = multivariateGaussian 0 (τ⁻¹ • (1 : Matrix p p ℝ)) ∧
      IndepFun (action (signal (n := n) (p := p))) (action noise) (inputLaw β τ) := by
    have hd := (ambientCov_posDef β τ hβ hτ).posSemidef
    refine ⟨?_, ?_, ?_⟩
    · simpa [inputLaw, signal, ambientCov, Matrix.transpose_fromCols, Matrix.fromCols_mul_fromBlocks, Matrix.fromCols_mul_fromRows] using
        map_gaussian (0 : E (n ⊕ p)) (ambientCov β τ) hd (signal (n := n) (p := p))
    · simpa [inputLaw, noise, ambientCov, Matrix.transpose_fromCols, Matrix.fromCols_mul_fromBlocks, Matrix.fromCols_mul_fromRows] using
        map_gaussian (0 : E (n ⊕ p)) (ambientCov β τ) hd (noise (n := n) (p := p))
    · apply independent_actions 0 (ambientCov β τ) hd
      simp [signal, noise, ambientCov, Matrix.transpose_fromCols, Matrix.fromCols_mul_fromBlocks, Matrix.fromCols_mul_fromRows]
  letI dataLaw_probability (M : Matrix p n ℝ) (β τ : ℝ) :
      IsProbabilityMeasure (dataLaw M β τ) := by
    unfold dataLaw
    exact (inputLaw β τ).isProbabilityMeasure_map (by fun_prop)
  letI translatedKernel_markov (K : E p →L[ℝ] E n) (ν : Measure (E n))
      [IsProbabilityMeasure ν] : IsMarkovKernel (translatedKernel K ν) := by
    unfold translatedKernel
    exact Kernel.IsMarkovKernel.map _ (by fun_prop)
  have translatedKernel_apply (K : E p →L[ℝ] E n) (ν : Measure (E n))
      [IsProbabilityMeasure ν] (y : E p) :
      translatedKernel K ν y = ν.map (fun r => K y + r) := by
    have hm : Measurable (fun z : E p × E n => K z.1 + z.2) := by fun_prop
    ext s hs
    rw [translatedKernel, Kernel.map_apply' _ hm _ hs, Kernel.id_prod_apply' _ _ (hm hs), Kernel.const_apply,
      Measure.map_apply (by fun_prop) hs]
    rfl
  have translatedKernel_compProd (K : E p →L[ℝ] E n) (μ : Measure (E p)) (ν : Measure (E n))
      [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] : μ ⊗ₘ translatedKernel K ν =
        (μ.prod ν).map (fun z : E p × E n => (z.1, K z.1 + z.2)) := by
    have ht : Measurable (fun z : E p × E n => (z.1, K z.1 + z.2)) := by fun_prop
    ext s hs
    rw [Measure.compProd_apply hs, Measure.map_apply ht hs, Measure.prod_apply (ht hs)]
    apply lintegral_congr_ae
    filter_upwards [] with y
    rw [translatedKernel_apply, Measure.map_apply (by fun_prop) (measurable_prodMk_left hs)]
    rfl
  have joint_eq_compProd_of_independent_residual
      {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (X : Ω → E n) (Y : Ω → E p) (R : Ω → E n) (hY : Measurable Y) (hR : Measurable R) (K : E p →L[ℝ] E n) (ν : Measure (E n)) [IsProbabilityMeasure ν]
      (hind : IndepFun Y R P) (hlaw : P.map R = ν) (hX : ∀ ω, X ω = K (Y ω) + R ω) : P.map (fun ω => (Y ω, X ω)) =
        (P.map Y) ⊗ₘ translatedKernel K ν := by
    letI : IsProbabilityMeasure (P.map Y) := P.isProbabilityMeasure_map hY.aemeasurable
    rw [translatedKernel_compProd, ← hlaw, ← hind.map_prod_eq_prod_map_map hY.aemeasurable hR.aemeasurable,
      Measure.map_map (by fun_prop) (hY.prodMk hR)]
    congr 1
    funext ω
    exact Prod.ext rfl (hX ω)
  letI posteriorKernel_markov (M : Matrix p n ℝ) (β τ : ℝ) :
      IsMarkovKernel (posteriorKernel M β τ) := by
    unfold posteriorKernel
    infer_instance
  have posterior_disintegration (M : Matrix p n ℝ) (β τ : ℝ) (hβ : 0 < β) (hτ : 0 < τ) :
      jointLaw M β τ = (dataLaw M β τ) ⊗ₘ posteriorKernel M β τ := by
    have hd := (ambientCov_posDef β τ hβ hτ).posSemidef
    have hind : IndepFun (action (innovation M β τ)) (action (observation M)) (inputLaw β τ) := independent_actions 0 (ambientCov β τ) hd _ _
        (innovation_data_covariance_zero M β τ hβ hτ)
    have hlaw : (inputLaw β τ).map (action (innovation M β τ)) =
        multivariateGaussian 0 (covariance M β τ) := by
      simpa only [inputLaw, map_zero, innovation_covariance M β τ hβ hτ] using
        map_gaussian (0 : E (n ⊕ p)) (ambientCov β τ) hd (innovation M β τ)
    apply joint_eq_compProd_of_independent_residual
      (inputLaw β τ) (action signal) (action (observation M))
      (action (innovation M β τ)) (by fun_prop) (by fun_prop)
      (action (gain M β τ)) (multivariateGaussian 0 (covariance M β τ))
      hind.symm hlaw
    intro z
    have hm := congrArg (fun A : Matrix n (n ⊕ p) ℝ => action A z) (signal_reconstruction M β τ hβ hτ)
    simpa only [action_add, ContinuousLinearMap.add_apply, ← action_comp, ContinuousLinearMap.comp_apply] using hm
  have hStd : stdGaussian (EuclideanSpace ℝ n) = (volume : Measure (EuclideanSpace ℝ n)).withDensity
      (fun x => ENNReal.ofReal (∏ i, gaussianPDFReal 0 1 (x i))) := by
    have hPi : Measure.pi (fun _ : n => gaussianReal 0 1) = (volume : Measure (n → ℝ)).withDensity
          (fun x => ENNReal.ofReal (∏ i, gaussianPDFReal 0 1 (x i))) := by
      refine Measure.pi_eq fun s hs => ?_
      rw [withDensity_apply _ (MeasurableSet.univ_pi hs)]
      rw [volume_pi, Measure.restrict_pi_pi]
      have hInt : Integrable (fun x : n → ℝ => ∏ i, gaussianPDFReal 0 1 (x i)) (Measure.pi (fun i => (volume : Measure ℝ).restrict (s i))) :=
        Integrable.fintype_prod (fun i => (integrable_gaussianPDFReal 0 1).restrict)
      rw [← ofReal_integral_eq_lintegral_ofReal hInt (ae_of_all _ (fun x => Finset.prod_nonneg (fun i _ => gaussianPDFReal_nonneg 0 1 (x i))))]
      rw [integral_fintype_prod_eq_prod]
      rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => integral_nonneg (fun x => gaussianPDFReal_nonneg 0 1 x))]
      exact Finset.prod_congr rfl (fun i _ => (gaussianReal_apply_eq_integral 0 (v := 1) one_ne_zero (s i)).symm)
    have hG : stdGaussian (EuclideanSpace ℝ n) = (volume : Measure (EuclideanSpace ℝ n)).withDensity
          (fun x => ENNReal.ofReal (∏ i, gaussianPDFReal 0 1 (x i))) := by
      rw [← map_pi_eq_stdGaussian, hPi]
      refine Measure.ext fun s hs => ?_
      rw [Measure.map_apply (PiLp.volume_preserving_toLp n).measurable hs, withDensity_apply _ ((PiLp.volume_preserving_toLp n).measurable hs), withDensity_apply _ hs]
      exact (PiLp.volume_preserving_toLp n).setLIntegral_comp_preimage_emb
        (MeasurableEquiv.toLp 2 (n → ℝ)).measurableEmbedding
        (fun x : EuclideanSpace ℝ n => ENNReal.ofReal (∏ i, gaussianPDFReal 0 1 (x i))) s
    exact hG

  have hDensity
      (m : EuclideanSpace ℝ n) (S : Matrix n n ℝ) (hS : S.PosDef) : ∃ c : ℝ≥0∞, 0 < c ∧ c ≠ ∞ ∧
        multivariateGaussian m S = (volume : Measure (EuclideanSpace ℝ n)).withDensity
          (fun y => c * ENNReal.ofReal (∏ i, gaussianPDFReal 0 1 (((Matrix.toEuclideanCLM (𝕜 := ℝ)) (CFC.sqrt S)⁻¹) (y - m) i))) ∧
        c = ENNReal.ofReal
          |(LinearMap.det ((Matrix.toEuclideanCLM (𝕜 := ℝ)) (CFC.sqrt S)).toLinearMap)⁻¹| := by
    let A := CFC.sqrt S
    let L := (Matrix.toEuclideanCLM (𝕜 := ℝ)) A
    let R := (Matrix.toEuclideanCLM (𝕜 := ℝ)) A⁻¹
    let f : EuclideanSpace ℝ n → EuclideanSpace ℝ n := fun x => m + L x
    let finv : EuclideanSpace ℝ n → EuclideanSpace ℝ n := fun y => R (y - m)
    let d : EuclideanSpace ℝ n → ℝ≥0∞ := fun x => ENNReal.ofReal (∏ i, gaussianPDFReal 0 1 (x i))
    have hd : Measurable d := by
      dsimp [d]
      exact (Finset.measurable_prod _ fun i _ => (measurable_gaussianPDFReal 0 1).comp ((measurable_pi_apply i).comp (WithLp.measurable_ofLp 2 (n → ℝ)))).ennreal_ofReal
    have hAdet : A.det ≠ 0 := by
      dsimp [A]
      rw [hS.posSemidef.det_sqrt]
      simpa only [RCLike.sqrt_real] using (Real.sqrt_pos.2 hS.det_pos).ne'
    have hAunit : IsUnit A := A.isUnit_iff_isUnit_det.mpr (isUnit_iff_ne_zero.mpr hAdet)
    have hRL (x : EuclideanSpace ℝ n) : R (L x) = x := by
      calc
        R (L x) = (((Matrix.toEuclideanCLM (𝕜 := ℝ)) A⁻¹).comp ((Matrix.toEuclideanCLM (𝕜 := ℝ)) A)) x := rfl
        _ = (Matrix.toEuclideanCLM (𝕜 := ℝ)) (A⁻¹ * A) x := by
          rw [map_mul]
          rfl
        _ = x := by
          rw [Matrix.nonsing_inv_mul A (A.isUnit_iff_isUnit_det.mp hAunit)]
          rw [map_one]
          rfl
    have hleft (x : EuclideanSpace ℝ n) : finv (f x) = x := by
      simp only [finv, f, add_sub_cancel_left]
      exact hRL x
    have hLinDet : LinearMap.det L.toLinearMap ≠ 0 := by
      change (Matrix.toLpLin 2 2 A).det ≠ 0
      rw [LinearMap.det_toLpLin]
      exact hAdet
    let c : ℝ≥0∞ := ENNReal.ofReal |(LinearMap.det L.toLinearMap)⁻¹|
    have hc : 0 < c := by
      dsimp [c]
      exact ENNReal.ofReal_pos.mpr (abs_pos.mpr (inv_ne_zero hLinDet))
    have hcfin : c ≠ ∞ := ENNReal.ofReal_ne_top
    have hvolL : (volume : Measure (EuclideanSpace ℝ n)).map L.toLinearMap = c • volume := by
      simpa only [c] using
        (Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure (EuclideanSpace ℝ n)) hLinDet)
    have hvolL' : (volume : Measure (EuclideanSpace ℝ n)).map L = c • volume := by
      have hfun : (⇑L.toLinearMap : EuclideanSpace ℝ n → EuclideanSpace ℝ n) = (⇑L : EuclideanSpace ℝ n → EuclideanSpace ℝ n) := by
        funext x
        rfl
      simpa only [hfun] using hvolL
    have hf : Measurable f := by fun_prop
    have hfinv : Measurable finv := by fun_prop
    have hvolf : (volume : Measure (EuclideanSpace ℝ n)).map f = c • volume := by
      calc
        (volume : Measure (EuclideanSpace ℝ n)).map f =
            ((volume : Measure (EuclideanSpace ℝ n)).map L).map (fun x => m + x) := by
          rw [Measure.map_map (by fun_prop) (by fun_prop)]
          rfl
        _ = (c • (volume : Measure (EuclideanSpace ℝ n))).map (fun x => m + x) := by rw [hvolL']
        _ = c • volume := by
          rw [Measure.map_smul, map_add_left_eq_self (volume : Measure (EuclideanSpace ℝ n)) m]
    have htransport : ((volume : Measure (EuclideanSpace ℝ n)).withDensity d).map f =
        ((volume : Measure (EuclideanSpace ℝ n)).map f).withDensity (fun y => d (finv y)) := by
      ext s hs
      rw [Measure.map_apply hf hs, withDensity_apply _ (hs.preimage hf), withDensity_apply _ hs]
      change (∫⁻ a in f ⁻¹' s, d a ∂(volume : Measure (EuclideanSpace ℝ n))) = ∫⁻ a in s, (d ∘ finv) a ∂((volume : Measure (EuclideanSpace ℝ n)).map f)
      rw [setLIntegral_map hs (hd.comp hfinv) hf]
      apply lintegral_congr_ae
      filter_upwards [] with x
      change d x = d (finv (f x))
      rw [hleft x]
    have hlaw : multivariateGaussian m S = (stdGaussian (EuclideanSpace ℝ n)).map f := by
      dsimp [f, L, A]
      rfl
    refine ⟨c, hc, hcfin, ?_, rfl⟩
    calc
      multivariateGaussian m S = ((volume : Measure (EuclideanSpace ℝ n)).withDensity d).map f := by
        rw [hlaw, hStd]
      _ = ((volume : Measure (EuclideanSpace ℝ n)).map f).withDensity (fun y => d (finv y)) := htransport
      _ = (c • (volume : Measure (EuclideanSpace ℝ n))).withDensity (fun y => d (finv y)) := by
        rw [hvolf]
      _ = (volume : Measure (EuclideanSpace ℝ n)).withDensity (fun y => c * d (finv y)) := by
        rw [withDensity_smul_measure]
        change c • (volume : Measure (EuclideanSpace ℝ n)).withDensity (d ∘ finv) = (volume : Measure (EuclideanSpace ℝ n)).withDensity (c • (d ∘ finv))
        exact (withDensity_smul c (hd.comp hfinv)).symm
      _ = (volume : Measure (EuclideanSpace ℝ n)).withDensity (fun y => c * ENNReal.ofReal (∏ i, gaussianPDFReal 0 1 (((Matrix.toEuclideanCLM (𝕜 := ℝ)) (CFC.sqrt S)⁻¹) (y - m) i))) := rfl

  have hLog
      (m : E n) (S : Matrix n n ℝ) (hS : S.PosDef) : ∃ c : ℝ≥0∞, 0 < c ∧ c ≠ ∞ ∧
        multivariateGaussian m S = (volume : Measure (E n)).withDensity
          (fun y => c * ENNReal.ofReal (∏ i, ProbabilityTheory.gaussianPDFReal 0 1 ((action (CFC.sqrt S)⁻¹) (y - m) i))) ∧
        c = ENNReal.ofReal
          |(LinearMap.det (action (CFC.sqrt S)).toLinearMap)⁻¹| ∧
        Integrable (fun y : E n => Real.log ((c * ENNReal.ofReal (∏ i, ProbabilityTheory.gaussianPDFReal 0 1 ((action (CFC.sqrt S)⁻¹) (y - m) i))).toReal)) (multivariateGaussian m S) ∧
        (∫ y : E n, Real.log ((c * ENNReal.ofReal (∏ i, ProbabilityTheory.gaussianPDFReal 0 1 ((action (CFC.sqrt S)⁻¹) (y - m) i))).toReal) ∂multivariateGaussian m S) =
          -Real.log S.det / 2 - (Fintype.card n : ℝ) *
            (Real.log (Real.sqrt (2 * Real.pi)) + 1 / 2) := by
    obtain ⟨c, hc, hcfin, hLaw, hcDet⟩ := hDensity m S hS
    change c = ENNReal.ofReal |(LinearMap.det (action (CFC.sqrt S)).toLinearMap)⁻¹| at hcDet
    have hwhite : Integrable (fun y : E n => Real.log (∏ i, ProbabilityTheory.gaussianPDFReal 0 1 ((action (CFC.sqrt S)⁻¹) (y - m) i))) (multivariateGaussian m S) ∧
      (∫ y : E n, Real.log (∏ i, ProbabilityTheory.gaussianPDFReal 0 1 ((action (CFC.sqrt S)⁻¹) (y - m) i)) ∂multivariateGaussian m S) = -(Fintype.card n : ℝ) *
          (Real.log (Real.sqrt (2 * Real.pi)) + 1 / 2) := by
      let A := CFC.sqrt S
      let L := action A
      let R := action A⁻¹
      let w : E n → E n := fun y => R (y - m)
      have hAdet : A.det ≠ 0 := by
        dsimp [A]
        rw [hS.posSemidef.det_sqrt]
        simpa only [RCLike.sqrt_real] using (Real.sqrt_pos.2 hS.det_pos).ne'
      have hAunit : IsUnit A := A.isUnit_iff_isUnit_det.mpr (isUnit_iff_ne_zero.mpr hAdet)
      have hRL (x : E n) : R (L x) = x := by
        calc
          R (L x) = ((action A⁻¹).comp (action A)) x := rfl
          _ = action (A⁻¹ * A) x := by rw [action_comp]
          _ = x := by
            rw [Matrix.nonsing_inv_mul A (A.isUnit_iff_isUnit_det.mp hAunit)]
            simp [action_apply]
      have hw : Measurable w := by fun_prop
      have hwhite : (multivariateGaussian m S).map w = stdGaussian (E n) := by
        have hfun : (fun x : E n => w (m + L x)) = id := by
          funext x
          simp only [w, add_sub_cancel_left]
          exact hRL x
        calc
          (multivariateGaussian m S).map w =
              ((stdGaussian (E n)).map (fun x => m + L x)).map w := by rfl
          _ = (stdGaussian (E n)).map (fun x => w (m + L x)) := by
            rw [Measure.map_map hw (by fun_prop)]
            rfl
          _ = stdGaussian (E n) := by rw [hfun, Measure.map_id]
      have hpdf (z : ℝ) : Real.log (ProbabilityTheory.gaussianPDFReal 0 1 z) =
          -Real.log (Real.sqrt (2 * Real.pi)) - z ^ 2 / 2 := by
        have hs : Real.sqrt (2 * Real.pi) ≠ 0 :=
          (Real.sqrt_pos.2 (by positivity)).ne'
        simp only [ProbabilityTheory.gaussianPDFReal, NNReal.coe_one, sub_zero, mul_one]
        rw [Real.log_mul (inv_ne_zero hs) (Real.exp_ne_zero _), Real.log_inv, Real.log_exp]
        ring
      have hpoint (x : E n) : Real.log (∏ i, ProbabilityTheory.gaussianPDFReal 0 1 (x i)) = -(Fintype.card n : ℝ) * Real.log (Real.sqrt (2 * Real.pi)) -
              (∑ i, (x i) ^ 2) / 2 := by
        rw [Real.log_prod (fun i _ => (ProbabilityTheory.gaussianPDFReal_pos 0 1 (x i) one_ne_zero).ne')]
        simp_rw [hpdf]
        simp [Finset.sum_sub_distrib, Finset.sum_div]
      have hcoordL2 (i : n) : MemLp (fun x : E n => x i) 2 (stdGaussian (E n)) := by
        rw [← ProbabilityTheory.multivariateGaussian_zero_one]
        exact ((IsGaussian.hasGaussianLaw_id (μ := multivariateGaussian (0 : E n) (1 : Matrix n n ℝ))).map_fun (EuclideanSpace.proj i)).memLp_two
      have hcoordInt (i : n) : Integrable (fun x : E n => (x i) ^ 2) (stdGaussian (E n)) := (hcoordL2 i).integrable_sq
      have hcoordMean (i : n) : (∫ x : E n, x i ∂stdGaussian (E n)) = 0 := by
        have hi : Integrable (fun x : E n => x) (stdGaussian (E n)) := IsGaussian.integrable_id
        calc
          (∫ x : E n, x i ∂stdGaussian (E n)) = (EuclideanSpace.proj i) (∫ x : E n, x ∂stdGaussian (E n)) := (EuclideanSpace.proj i).integral_comp_comm hi
          _ = 0 := by rw [ProbabilityTheory.integral_id_stdGaussian]; rfl
      have hcoordSq (i : n) : (∫ x : E n, (x i) ^ 2 ∂stdGaussian (E n)) = 1 := by
        have hv : Var[fun x : E n => x i; stdGaussian (E n)] = 1 := by
          rw [← ProbabilityTheory.multivariateGaussian_zero_one, ProbabilityTheory.variance_eval_multivariateGaussian Matrix.PosSemidef.one i]
          simp
        have hs := variance_eq_sub (hcoordL2 i)
        rw [hcoordMean i] at hs
        simpa using hs.symm.trans hv
      have hstdEnergy : Integrable (fun x : E n => (∑ i, (x i) ^ 2) / 2)
          (stdGaussian (E n)) := by
        exact (integrable_finsetSum Finset.univ (fun i _ => hcoordInt i)).div_const 2
      have hstdMoment : (∫ x : E n, (∑ i, (x i) ^ 2) / 2 ∂stdGaussian (E n)) =
          (Fintype.card n : ℝ) / 2 := by
        rw [integral_div, integral_finsetSum _ (fun i _ => hcoordInt i)]
        simp [hcoordSq]
      have hstdLog : Integrable (fun x : E n => Real.log
          (∏ i, ProbabilityTheory.gaussianPDFReal 0 1 (x i))) (stdGaussian (E n)) := by
        apply Integrable.congr
          ((integrable_const _).sub hstdEnergy)
        exact Filter.Eventually.of_forall fun x => (hpoint x).symm
      have hlogMap : Integrable (fun y : E n => Real.log (∏ i, ProbabilityTheory.gaussianPDFReal 0 1 (w y i)))
          (multivariateGaussian m S) := by
        have h : Integrable (fun x : E n => Real.log (∏ i, ProbabilityTheory.gaussianPDFReal 0 1 (x i)))
            ((multivariateGaussian m S).map w) := by rw [hwhite]; exact hstdLog
        exact h.comp_aemeasurable hw.aemeasurable
      refine ⟨hlogMap, ?_⟩
      have hmeas : AEStronglyMeasurable
          (fun x : E n => Real.log (∏ i, ProbabilityTheory.gaussianPDFReal 0 1 (x i)))
          ((multivariateGaussian m S).map w) := by
        rw [hwhite]
        exact hstdLog.aestronglyMeasurable
      calc
        (∫ y : E n, Real.log (∏ i, ProbabilityTheory.gaussianPDFReal 0 1 (w y i)) ∂multivariateGaussian m S) = ∫ x : E n, Real.log
              (∏ i, ProbabilityTheory.gaussianPDFReal 0 1 (x i)) ∂stdGaussian (E n) := by
            rw [← hwhite, integral_map hw.aemeasurable hmeas]
        _ = ∫ x : E n,
              (-(Fintype.card n : ℝ) * Real.log (Real.sqrt (2 * Real.pi)) - (∑ i, (x i) ^ 2) / 2) ∂stdGaussian (E n) := integral_congr_ae (Filter.Eventually.of_forall hpoint)
        _ = -(Fintype.card n : ℝ) *
            (Real.log (Real.sqrt (2 * Real.pi)) + 1 / 2) := by
          rw [integral_sub (integrable_const _) hstdEnergy, integral_const, hstdMoment]
          simp only [probReal_univ, one_smul]
          ring
    obtain ⟨hwhiteInt, hwhiteMean⟩ := hwhite
    have hcReal : 0 < c.toReal := ENNReal.toReal_pos hc.ne' hcfin
    have hactionDet : (action (CFC.sqrt S)).toLinearMap.det =
        (CFC.sqrt S).det := by
      change (Matrix.toLpLin 2 2 (CFC.sqrt S)).det = (CFC.sqrt S).det
      exact LinearMap.det_toLpLin 2 (CFC.sqrt S)
    have hsqrtDet : (CFC.sqrt S).det = Real.sqrt S.det := by
      simpa only [RCLike.sqrt_real] using hS.posSemidef.det_sqrt
    have hcRealDet : c.toReal = (Real.sqrt S.det)⁻¹ := by
      calc
        c.toReal = |((action (CFC.sqrt S)).toLinearMap.det)⁻¹| := by
          rw [hcDet, ENNReal.toReal_ofReal (abs_nonneg _)]
        _ = (Real.sqrt S.det)⁻¹ := by
          rw [hactionDet, hsqrtDet, abs_of_pos (inv_pos.mpr (Real.sqrt_pos.2 hS.det_pos))]
    have hlogDet : Real.log c.toReal = -Real.log S.det / 2 := by
      rw [hcRealDet, Real.log_inv, Real.log_sqrt hS.det_pos.le]
      ring
    have hlog (y : E n) : Real.log ((c * ENNReal.ofReal (∏ i, ProbabilityTheory.gaussianPDFReal 0 1 ((action (CFC.sqrt S)⁻¹) (y - m) i))).toReal) = Real.log c.toReal + Real.log
          (∏ i, ProbabilityTheory.gaussianPDFReal 0 1
            ((action (CFC.sqrt S)⁻¹) (y - m) i)) := by
      have hq : 0 < ∏ i, ProbabilityTheory.gaussianPDFReal 0 1
          ((action (CFC.sqrt S)⁻¹) (y - m) i) := Finset.prod_pos fun i _ =>
          ProbabilityTheory.gaussianPDFReal_pos 0 1 _ one_ne_zero
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hq.le, Real.log_mul hcReal.ne' hq.ne']
    have hint : Integrable (fun y : E n => Real.log ((c * ENNReal.ofReal (∏ i, ProbabilityTheory.gaussianPDFReal 0 1 ((action (CFC.sqrt S)⁻¹) (y - m) i))).toReal))
        (multivariateGaussian m S) := by
      exact ((integrable_const _).add hwhiteInt).congr
        (Filter.Eventually.of_forall fun y => (hlog y).symm)
    refine ⟨c, hc, hcfin, hLaw, hcDet, hint, ?_⟩
    rw [integral_congr_ae (Filter.Eventually.of_forall hlog), integral_add (integrable_const _) hwhiteInt, integral_const, hwhiteMean, hlogDet]
    simp only [probReal_univ, one_smul]
    ring
  have hFree (M : Matrix p n ℝ) (β τ : ℝ) (hβ : 0 < β) (hτ : 0 < τ) : (∫ y : E p, physicalFreeEnergy β (posteriorKernel M β τ y) ∂dataLaw M β τ) -
        physicalFreeEnergy β (multivariateGaussian 0 (β⁻¹ • (1 : Matrix n n ℝ))) = β⁻¹ * (Real.log ((β⁻¹ • (1 : Matrix n n ℝ)).det) / 2 -
          Real.log ((covariance M β τ).det) / 2) := by
    let prior : Measure (E n) := multivariateGaussian 0 (β⁻¹ • (1 : Matrix n n ℝ))
    have hprior : (jointLaw M β τ).snd = prior := by
      unfold jointLaw Measure.snd prior
      rw [Measure.map_map measurable_snd (by fun_prop)]
      exact (input_factors β τ hβ hτ).1
    have hpriorPD : (β⁻¹ • (1 : Matrix n n ℝ)).PosDef := by
      have hd : β⁻¹ • (1 : Matrix n n ℝ) = Matrix.diagonal (fun _ : n => β⁻¹) := by
        ext i j
        simp [Matrix.diagonal, Matrix.one_apply]
      rw [hd, Matrix.posDef_diagonal_iff]
      intro i
      exact inv_pos.mpr hβ
    have hCov : (covariance M β τ).PosDef := (precision_posDef M β τ hβ hτ.le).inv
    have hEntropy (m : E n) (S : Matrix n n ℝ) (hS : S.PosDef) : differentialEntropy (multivariateGaussian m S) = Real.log S.det / 2 + (Fintype.card n : ℝ) *
            (Real.log (Real.sqrt (2 * Real.pi)) + 1 / 2) := by
      obtain ⟨c, _, _, hLaw, _, _, hMean⟩ := hLog m S hS
      let d : E n → ℝ≥0∞ := fun y => c * ENNReal.ofReal
        (∏ i, ProbabilityTheory.gaussianPDFReal 0 1 ((action (CFC.sqrt S)⁻¹) (y - m) i))
      have hd : Measurable d := by
        dsimp [d]
        have hcoord (i : n) : Measurable (fun y : E n => ((action (CFC.sqrt S)⁻¹) (y - m)) i) := ((measurable_pi_apply i).comp (WithLp.measurable_ofLp 2 (n → ℝ))).comp
            ((action (CFC.sqrt S)⁻¹).measurable.comp (measurable_id.sub_const m))
        have hprod : Measurable (fun y : E n => ∏ i, ProbabilityTheory.gaussianPDFReal 0 1 ((action (CFC.sqrt S)⁻¹) (y - m) i)) := Finset.measurable_prod _ fun i _ =>
            (ProbabilityTheory.measurable_gaussianPDFReal 0 1).comp (hcoord i)
        exact measurable_const.mul hprod.ennreal_ofReal
      change multivariateGaussian m S = (volume : Measure (E n)).withDensity d at hLaw
      have hAC : multivariateGaussian m S ≪ (volume : Measure (E n)) := by
        rw [hLaw]
        exact withDensity_absolutelyContinuous _ _
      have hRN : (fun y : E n => Real.log (((multivariateGaussian m S).rnDeriv volume y).toReal)) =ᵐ[
          multivariateGaussian m S] (fun y => Real.log ((d y).toReal)) := by
        have h := Measure.rnDeriv_withDensity (volume : Measure (E n)) hd
        rw [← hLaw] at h
        filter_upwards [hAC h] with y hy
        rw [hy]
      unfold differentialEntropy
      rw [integral_congr_ae hRN]
      change -(∫ y : E n, Real.log ((c * ENNReal.ofReal (∏ i, ProbabilityTheory.gaussianPDFReal 0 1 ((action (CFC.sqrt S)⁻¹) (y - m) i))).toReal) ∂multivariateGaussian m S) = _
      rw [hMean]
      ring
    have hpostEntropy (y : E p) : differentialEntropy (posteriorKernel M β τ y) = Real.log ((covariance M β τ).det) / 2 +
            (Fintype.card n : ℝ) *
              (Real.log (Real.sqrt (2 * Real.pi)) + 1 / 2) := by
      rw [posteriorKernel, translatedKernel_apply, translate_gaussian, add_zero]
      exact hEntropy _ _ hCov
    have hpriorEntropy : differentialEntropy prior = Real.log ((β⁻¹ • (1 : Matrix n n ℝ)).det) / 2 +
          (Fintype.card n : ℝ) *
            (Real.log (Real.sqrt (2 * Real.pi)) + 1 / 2) := hEntropy 0 _ hpriorPD
    have hcoord (i : n) : MemLp (fun x : E n => x i) 2 prior := ((IsGaussian.hasGaussianLaw_id (μ := prior)).map_fun (EuclideanSpace.proj i)).memLp_two
    have hEprior : Integrable physicalEnergy prior := by
      unfold physicalEnergy
      exact (integrable_finsetSum Finset.univ (fun i _ => (hcoord i).integrable_sq)).div_const 2
    have hEjoint : Integrable (fun z : E p × E n => physicalEnergy z.2)
        (jointLaw M β τ) := by
      have h : Integrable physicalEnergy (Measure.map Prod.snd (jointLaw M β τ)) := by
        change Integrable physicalEnergy (jointLaw M β τ).snd
        rw [hprior]
        exact hEprior
      exact h.comp_aemeasurable measurable_snd.aemeasurable
    have hEcomp : Integrable (fun z : E p × E n => physicalEnergy z.2)
        (dataLaw M β τ ⊗ₘ posteriorKernel M β τ) := by
      rw [← posterior_disintegration M β τ hβ hτ]
      exact hEjoint
    have hEouter : Integrable (fun y : E p =>
        ∫ x, physicalEnergy x ∂posteriorKernel M β τ y) (dataLaw M β τ) := by
      simpa only [Measure.compProd, Kernel.prodMkLeft_apply, Kernel.const_apply] using
        hEcomp.integral_compProd
    have hTower : (∫ y : E p, ∫ x, physicalEnergy x ∂posteriorKernel M β τ y
          ∂dataLaw M β τ) = ∫ x, physicalEnergy x ∂prior := by
      calc
        (∫ y : E p, ∫ x, physicalEnergy x ∂posteriorKernel M β τ y ∂dataLaw M β τ) = ∫ z : E p × E n, physicalEnergy z.2
              ∂(dataLaw M β τ ⊗ₘ posteriorKernel M β τ) := (Measure.integral_compProd hEcomp).symm
        _ = ∫ z : E p × E n, physicalEnergy z.2 ∂jointLaw M β τ := by
          rw [posterior_disintegration M β τ hβ hτ]
        _ = ∫ x, physicalEnergy x ∂prior := by
          rw [← hprior]
          have hsm : AEStronglyMeasurable physicalEnergy
              (Measure.map Prod.snd (jointLaw M β τ)) := by
            change AEStronglyMeasurable physicalEnergy (jointLaw M β τ).snd
            rw [hprior]
            exact hEprior.aestronglyMeasurable
          exact (integral_map measurable_snd.aemeasurable hsm).symm
    have hEntropyOuter : Integrable (fun y : E p => β⁻¹ * differentialEntropy (posteriorKernel M β τ y))
        (dataLaw M β τ) := by
      simp_rw [hpostEntropy]
      exact integrable_const _
    change (∫ y : E p, (∫ x, physicalEnergy x ∂posteriorKernel M β τ y) - β⁻¹ * differentialEntropy (posteriorKernel M β τ y) ∂dataLaw M β τ) -
      ((∫ x, physicalEnergy x ∂prior) - β⁻¹ * differentialEntropy prior) = _
    rw [integral_sub hEouter hEntropyOuter, hTower, hpriorEntropy]
    simp_rw [hpostEntropy]
    rw [integral_const]
    simp only [probReal_univ, one_smul]
    ring
  have hLikelihood (M : Matrix p n ℝ) (β τ : ℝ) (hβ : 0 < β) (hτ : 0 < τ) : ∃ cprior cpost : ℝ≥0∞,
        0 < cprior ∧ cprior ≠ ∞ ∧ 0 < cpost ∧ cpost ≠ ∞ ∧
        cprior = ENNReal.ofReal
          |(LinearMap.det (action (CFC.sqrt (β⁻¹ • (1 : Matrix n n ℝ)))).toLinearMap)⁻¹| ∧
        cpost = ENNReal.ofReal
          |(LinearMap.det (action (CFC.sqrt (covariance M β τ))).toLinearMap)⁻¹| ∧
        Measurable (fun z : E p × E n => transportedGaussianDensity cpost (covariance M β τ) (action (gain M β τ) z.1) z.2 * (transportedGaussianDensity cprior
              (β⁻¹ • (1 : Matrix n n ℝ)) 0 z.2)⁻¹) ∧
        jointLaw M β τ = ((jointLaw M β τ).fst.prod (jointLaw M β τ).snd).withDensity
            (fun z => transportedGaussianDensity cpost (covariance M β τ) (action (gain M β τ) z.1) z.2 * (transportedGaussianDensity cprior
                (β⁻¹ • (1 : Matrix n n ℝ)) 0 z.2)⁻¹) := by
    let prior : Measure (E n) := multivariateGaussian 0 (β⁻¹ • (1 : Matrix n n ℝ))
    have hprior : (jointLaw M β τ).snd = prior := by
      unfold jointLaw Measure.snd prior
      rw [Measure.map_map measurable_snd (by fun_prop)]
      exact (input_factors β τ hβ hτ).1
    have hpriorPD : (β⁻¹ • (1 : Matrix n n ℝ)).PosDef := by
      have hd : β⁻¹ • (1 : Matrix n n ℝ) = Matrix.diagonal (fun _ : n => β⁻¹) := by
        ext i j
        simp [Matrix.diagonal, Matrix.one_apply]
      rw [hd, Matrix.posDef_diagonal_iff]
      intro i
      exact inv_pos.mpr hβ
    have hCov : (covariance M β τ).PosDef := (precision_posDef M β τ hβ hτ.le).inv
    obtain ⟨cprior, hcprior, hcpriorFin, hpriorLaw, hcpriorDet⟩ := hDensity (0 : E n) (β⁻¹ • (1 : Matrix n n ℝ)) hpriorPD
    obtain ⟨cpost, hcpost, hcpostFin, _, hcpostDet⟩ := hDensity (0 : E n) (covariance M β τ) hCov
    let dprior : E n → ℝ≥0∞ := transportedGaussianDensity cprior (β⁻¹ • (1 : Matrix n n ℝ)) 0
    let dpost : E p → E n → ℝ≥0∞ := fun y =>
      transportedGaussianDensity cpost (covariance M β τ) (action (gain M β τ) y)
    let ratio : E p × E n → ℝ≥0∞ := fun z => dpost z.1 z.2 * (dprior z.2)⁻¹
    change prior = (volume : Measure (E n)).withDensity dprior at hpriorLaw
    have hdprior : Measurable dprior := by
      have hcoord (i : n) : Measurable (fun x : E n => ((action (CFC.sqrt (β⁻¹ • (1 : Matrix n n ℝ)))⁻¹) (x - 0)) i) := ((measurable_pi_apply i).comp (WithLp.measurable_ofLp 2 (n → ℝ))).comp
          ((action (CFC.sqrt (β⁻¹ • (1 : Matrix n n ℝ)))⁻¹).measurable.comp (measurable_id.sub_const 0))
      have hprod : Measurable (fun x : E n => ∏ i, ProbabilityTheory.gaussianPDFReal 0 1 ((action (CFC.sqrt (β⁻¹ • (1 : Matrix n n ℝ)))⁻¹) (x - 0) i)) := Finset.measurable_prod _ fun i _ =>
          (ProbabilityTheory.measurable_gaussianPDFReal 0 1).comp (hcoord i)
      exact measurable_const.mul hprod.ennreal_ofReal
    have hdpost : Measurable (Function.uncurry dpost) := by
      have hcenter : Measurable (fun z : E p × E n => z.2 - action (gain M β τ) z.1) := measurable_snd.sub ((action (gain M β τ)).measurable.comp measurable_fst)
      have hcoord (i : n) : Measurable (fun z : E p × E n => ((action (CFC.sqrt (covariance M β τ))⁻¹) (z.2 - action (gain M β τ) z.1)) i) :=
        ((measurable_pi_apply i).comp (WithLp.measurable_ofLp 2 (n → ℝ))).comp
          ((action (CFC.sqrt (covariance M β τ))⁻¹).measurable.comp hcenter)
      have hprod : Measurable (fun z : E p × E n => ∏ i, ProbabilityTheory.gaussianPDFReal 0 1 ((action (CFC.sqrt (covariance M β τ))⁻¹) (z.2 - action (gain M β τ) z.1) i)) :=
        Finset.measurable_prod _ fun i _ =>
          (ProbabilityTheory.measurable_gaussianPDFReal 0 1).comp (hcoord i)
      exact measurable_const.mul hprod.ennreal_ofReal
    have hratio : Measurable ratio := by
      exact hdpost.mul ((hdprior.comp measurable_snd).inv)
    have hratioY (y : E p) : Measurable (fun x => ratio (y, x)) := by
      have hpair : Measurable (fun x : E n => (y, x)) := by fun_prop
      exact hratio.comp hpair
    have hdpriorPos (x : E n) : dprior x ≠ 0 := by
      dsimp [dprior, transportedGaussianDensity]
      apply mul_ne_zero hcprior.ne'
      apply (ENNReal.ofReal_pos.mpr ?_).ne'
      exact Finset.prod_pos fun i _ =>
        ProbabilityTheory.gaussianPDFReal_pos 0 1 _ one_ne_zero
    have hdpriorFin (x : E n) : dprior x ≠ ∞ := by
      dsimp [dprior, transportedGaussianDensity]
      exact ENNReal.mul_ne_top hcpriorFin ENNReal.ofReal_ne_top
    have hpostLaw (y : E p) :
        posteriorKernel M β τ y = (volume : Measure (E n)).withDensity (dpost y) := by
      obtain ⟨cy, _, _, hcyLaw, hcyDet⟩ := hDensity (action (gain M β τ) y) (covariance M β τ) hCov
      have hcy : cy = cpost := hcyDet.trans hcpostDet.symm
      rw [hcy] at hcyLaw
      have hm : posteriorKernel M β τ y =
          multivariateGaussian (action (gain M β τ) y) (covariance M β τ) := by
        rw [posteriorKernel, translatedKernel_apply, translate_gaussian, add_zero]
      rw [hm]
      exact hcyLaw
    have hkernel (y : E p) : posteriorKernel M β τ y =
        prior.withDensity (fun x => ratio (y, x)) := by
      calc
        posteriorKernel M β τ y = (volume : Measure (E n)).withDensity (dpost y) := hpostLaw y
        _ = (volume : Measure (E n)).withDensity
            (dprior * fun x => ratio (y, x)) := by
          apply withDensity_congr_ae
          exact Filter.Eventually.of_forall fun x => by
            change dpost y x = dprior x * (dpost y x * (dprior x)⁻¹)
            calc
              dpost y x = dpost y x * dprior x * (dprior x)⁻¹ := (ENNReal.mul_inv_cancel_right (hdpriorPos x) (hdpriorFin x)).symm
              _ = dprior x * (dpost y x * (dprior x)⁻¹) := by ac_rfl
        _ = ((volume : Measure (E n)).withDensity dprior).withDensity
            (fun x => ratio (y, x)) := withDensity_mul volume hdprior (hratioY y)
        _ = prior.withDensity (fun x => ratio (y, x)) := by rw [← hpriorLaw]
    let κ : Kernel (E p) (E n) := Kernel.const (E p) prior
    have hratioKernel : Measurable
        (Function.uncurry (fun y x => ratio (y, x))) := hratio
    have hκ : posteriorKernel M β τ = κ.withDensity (fun y x => ratio (y, x)) := by
      apply Kernel.ext
      intro y
      rw [Kernel.withDensity_apply κ hratioKernel y]
      exact hkernel y
    letI : IsSFiniteKernel (κ.withDensity (fun y x => ratio (y, x))) := by
      rw [← hκ]
      infer_instance
    refine ⟨cprior, cpost, hcprior, hcpriorFin, hcpost, hcpostFin, hcpriorDet, hcpostDet, hratio, ?_⟩
    calc
      jointLaw M β τ = dataLaw M β τ ⊗ₘ posteriorKernel M β τ := posterior_disintegration M β τ hβ hτ
      _ = dataLaw M β τ ⊗ₘ κ.withDensity (fun y x => ratio (y, x)) := by rw [hκ]
      _ = (dataLaw M β τ ⊗ₘ κ).withDensity
          ratio := Measure.compProd_withDensity hratioKernel
      _ = ((dataLaw M β τ).prod prior).withDensity
          ratio := by rw [Measure.compProd_const]
      _ = ((jointLaw M β τ).fst.prod (jointLaw M β τ).snd).withDensity
          ratio := by
            have hdata : (jointLaw M β τ).fst = dataLaw M β τ := by
              unfold jointLaw dataLaw Measure.fst
              rw [Measure.map_map measurable_fst (by fun_prop)]
              rfl
            rw [hdata, hprior]
      _ = _ := rfl
  let joint := jointLaw M β τ
  let product := joint.fst.prod joint.snd
  let prior : Measure (E n) := multivariateGaussian 0 (β⁻¹ • (1 : Matrix n n ℝ))
  have hprior : joint.snd = prior := by
    dsimp [joint, prior, jointLaw, Measure.snd]
    rw [Measure.map_map measurable_snd (by fun_prop)]
    exact (input_factors β τ hβ hτ).1
  have hpriorPD : (β⁻¹ • (1 : Matrix n n ℝ)).PosDef := by
    have hd : β⁻¹ • (1 : Matrix n n ℝ) = Matrix.diagonal (fun _ : n => β⁻¹) := by
      ext i j
      simp [Matrix.diagonal, Matrix.one_apply]
    rw [hd, Matrix.posDef_diagonal_iff]
    intro i
    exact inv_pos.mpr hβ
  have hCov : (covariance M β τ).PosDef := (precision_posDef M β τ hβ hτ.le).inv
  obtain ⟨cprior, cpost, hcprior, hcpriorFin, hcpost, hcpostFin, hcpriorDet, hcpostDet, hratioMeas, hJoint⟩ := hLikelihood M β τ hβ hτ
  let dprior : E n → ℝ≥0∞ := transportedGaussianDensity cprior (β⁻¹ • (1 : Matrix n n ℝ)) 0
  let dpost : E p × E n → ℝ≥0∞ := fun z =>
    transportedGaussianDensity cpost (covariance M β τ) (action (gain M β τ) z.1) z.2
  let ratio : E p × E n → ℝ≥0∞ := fun z => dpost z * (dprior z.2)⁻¹
  change joint = product.withDensity ratio at hJoint
  have hratio : Measurable ratio := hratioMeas
  let residual : E p × E n → E n := fun z => z.2 - action (gain M β τ) z.1
  have hresMeas : Measurable residual := by fun_prop
  have hresLaw : joint.map residual =
      multivariateGaussian 0 (covariance M β τ) := by
    have hfun (z : E (n ⊕ p)) : residual (action (observation M) z, action signal z) =
          action (innovation M β τ) z := by
      have hm := congrArg (fun A : Matrix n (n ⊕ p) ℝ => action A z) (signal_reconstruction M β τ hβ hτ)
      have heq : action signal z = action (gain M β τ) (action (observation M) z) +
            action (innovation M β τ) z := by
        simpa only [action_add, ContinuousLinearMap.add_apply, ← action_comp, ContinuousLinearMap.comp_apply] using hm
      change action signal z - action (gain M β τ) (action (observation M) z) = action (innovation M β τ) z
      rw [heq]
      abel
    calc
      joint.map residual = (inputLaw β τ).map (action (innovation M β τ)) := by
        dsimp [joint, jointLaw]
        rw [Measure.map_map hresMeas (by fun_prop)]
        congr 1
        funext z
        exact hfun z
      _ = multivariateGaussian 0 (covariance M β τ) := by
        simpa only [inputLaw, map_zero, innovation_covariance M β τ hβ hτ] using
          map_gaussian (0 : E (n ⊕ p)) (ambientCov β τ) (ambientCov_posDef β τ hβ hτ).posSemidef
            (innovation M β τ)
  obtain ⟨cp, _, _, _, hcpDet, hpostInt0, hpostMean0⟩ := hLog (0 : E n) (covariance M β τ) hCov
  have hcp : cp = cpost := hcpDet.trans hcpostDet.symm
  rw [hcp] at hpostInt0 hpostMean0
  obtain ⟨cq, _, _, _, hcqDet, hpriorInt0, hpriorMean0⟩ := hLog (0 : E n) (β⁻¹ • (1 : Matrix n n ℝ)) hpriorPD
  have hcq : cq = cprior := hcqDet.trans hcpriorDet.symm
  rw [hcq] at hpriorInt0 hpriorMean0
  let postLog : E n → ℝ := fun x =>
    Real.log ((transportedGaussianDensity cpost (covariance M β τ) 0 x).toReal)
  let priorLog : E n → ℝ := fun x => Real.log ((dprior x).toReal)
  have hpostInt : Integrable postLog
      (multivariateGaussian 0 (covariance M β τ)) := by
    simpa only [postLog, transportedGaussianDensity] using hpostInt0
  have hpriorInt : Integrable priorLog prior := by
    simpa only [priorLog, dprior, transportedGaussianDensity, prior] using hpriorInt0
  have hpostExpr (z : E p × E n) :
      Real.log ((dpost z).toReal) = postLog (residual z) := by
    simp [dpost, postLog, residual, transportedGaussianDensity]
  have hpostMapInt : Integrable postLog (joint.map residual) := by
    rw [hresLaw]
    exact hpostInt
  have hpostJointInt : Integrable (fun z => Real.log ((dpost z).toReal)) joint := by
    exact (hpostMapInt.comp_aemeasurable hresMeas.aemeasurable).congr
      (Filter.Eventually.of_forall fun z => (hpostExpr z).symm)
  have hpriorMapInt : Integrable priorLog joint.snd := by
    rw [hprior]
    exact hpriorInt
  have hpriorJointInt : Integrable (fun z : E p × E n => priorLog z.2) joint := hpriorMapInt.comp_aemeasurable measurable_snd.aemeasurable
  have hpostJointMean : (∫ z, Real.log ((dpost z).toReal) ∂joint) = -Real.log ((covariance M β τ).det) / 2 -
          (Fintype.card n : ℝ) *
            (Real.log (Real.sqrt (2 * Real.pi)) + 1 / 2) := by
    calc
      (∫ z, Real.log ((dpost z).toReal) ∂joint) = ∫ z, postLog (residual z) ∂joint := integral_congr_ae (Filter.Eventually.of_forall hpostExpr)
      _ = ∫ x, postLog x ∂joint.map residual := by
        exact (integral_map hresMeas.aemeasurable
          (by rw [hresLaw]; exact hpostInt.aestronglyMeasurable)).symm
      _ = _ := by
        rw [hresLaw]
        simpa only [postLog, transportedGaussianDensity] using hpostMean0
  have hpriorJointMean : (∫ z : E p × E n, priorLog z.2 ∂joint) = -Real.log ((β⁻¹ • (1 : Matrix n n ℝ)).det) / 2 -
          (Fintype.card n : ℝ) *
            (Real.log (Real.sqrt (2 * Real.pi)) + 1 / 2) := by
    calc
      (∫ z : E p × E n, priorLog z.2 ∂joint) =
          ∫ x, priorLog x ∂joint.snd := by
        change (∫ z, priorLog (Prod.snd z) ∂joint) = _
        exact (integral_map measurable_snd.aemeasurable
          (by change AEStronglyMeasurable priorLog joint.snd
              rw [hprior]
              exact hpriorInt.aestronglyMeasurable)).symm
      _ = _ := by
        rw [hprior]
        simpa only [priorLog, dprior, prior, transportedGaussianDensity] using
          hpriorMean0
  have hdpriorPos (x : E n) : dprior x ≠ 0 := by
    dsimp [dprior, transportedGaussianDensity]
    apply mul_ne_zero hcprior.ne'
    apply (ENNReal.ofReal_pos.mpr ?_).ne'
    exact Finset.prod_pos fun i _ =>
      ProbabilityTheory.gaussianPDFReal_pos 0 1 _ one_ne_zero
  have hdpriorFin (x : E n) : dprior x ≠ ∞ := by
    dsimp [dprior, transportedGaussianDensity]
    exact ENNReal.mul_ne_top hcpriorFin ENNReal.ofReal_ne_top
  have hdpostPos (z : E p × E n) : dpost z ≠ 0 := by
    dsimp [dpost, transportedGaussianDensity]
    apply mul_ne_zero hcpost.ne'
    apply (ENNReal.ofReal_pos.mpr ?_).ne'
    exact Finset.prod_pos fun i _ =>
      ProbabilityTheory.gaussianPDFReal_pos 0 1 _ one_ne_zero
  have hdpostFin (z : E p × E n) : dpost z ≠ ∞ := by
    dsimp [dpost, transportedGaussianDensity]
    exact ENNReal.mul_ne_top hcpostFin ENNReal.ofReal_ne_top
  have hlogRatio (z : E p × E n) : Real.log ((ratio z).toReal) =
        Real.log ((dpost z).toReal) - priorLog z.2 := by
    dsimp [ratio, priorLog]
    rw [ENNReal.toReal_mul, ENNReal.toReal_inv, Real.log_mul (ENNReal.toReal_pos (hdpostPos z) (hdpostFin z)).ne' (inv_ne_zero (ENNReal.toReal_pos (hdpriorPos z.2) (hdpriorFin z.2)).ne'),
      Real.log_inv]
    ring
  have hAC : joint ≪ product := by
    rw [hJoint]
    exact withDensity_absolutelyContinuous _ _
  letI : IsProbabilityMeasure joint := by
    dsimp [joint, jointLaw]
    exact (inputLaw β τ).isProbabilityMeasure_map (by fun_prop)
  letI : IsProbabilityMeasure product := by
    dsimp [product]
    infer_instance
  have hRN : joint.rnDeriv product =ᵐ[joint] ratio := by
    have h := Measure.rnDeriv_withDensity product hratio
    rw [← hJoint] at h
    exact hAC h
  have hllrEq : llr joint product =ᵐ[joint]
      (fun z => Real.log ((dpost z).toReal) - priorLog z.2) := by
    filter_upwards [hRN] with z hz
    rw [llr, hz, hlogRatio z]
  have hllrInt : Integrable (llr joint product) joint := (hpostJointInt.sub hpriorJointInt).congr hllrEq.symm
  have hllrMean : (∫ z, llr joint product z ∂joint) = (Real.log ((β⁻¹ • (1 : Matrix n n ℝ)).det) -
        Real.log ((covariance M β τ).det)) / 2 := by
    rw [integral_congr_ae hllrEq, integral_sub hpostJointInt hpriorJointInt, hpostJointMean, hpriorJointMean]
    ring
  have hmassJoint : joint.real Set.univ = 1 := by simp
  have hmassProduct : product.real Set.univ = 1 := by simp
  have hMICov : (mutualInformation M β τ).toReal = (Real.log ((β⁻¹ • (1 : Matrix n n ℝ)).det) -
        Real.log ((covariance M β τ).det)) / 2 := by
    change (InformationTheory.klDiv joint product).toReal = _
    rw [InformationTheory.toReal_klDiv hAC hllrInt, hllrMean, hmassProduct, hmassJoint]
    ring
  have hfactor : (β⁻¹ • (1 : Matrix n n ℝ)) * precision M β τ =
        1 + (τ / β) • (M.transpose * M) := by
    rw [precision, Matrix.mul_add]
    simp only [Matrix.smul_mul, Matrix.one_mul, smul_smul]
    simp [div_eq_mul_inv, mul_comm, hβ.ne']
  have hdetCov : (covariance M β τ).det = (precision M β τ).det⁻¹ := by
    change ((precision M β τ)⁻¹).det = (precision M β τ).det⁻¹
    simp
  have hdetPriorPos : 0 < (β⁻¹ • (1 : Matrix n n ℝ)).det := hpriorPD.det_pos
  have hdetPrecisionPos : 0 < (precision M β τ).det := (precision_posDef M β τ hβ hτ.le).det_pos
  have hdetFactor : ((β⁻¹ • (1 : Matrix n n ℝ)).det) * (precision M β τ).det =
        (1 + (τ / β) • (M.transpose * M)).det := by
    rw [← Matrix.det_mul, hfactor]
  have hlogdet : Real.log ((β⁻¹ • (1 : Matrix n n ℝ)).det) -
        Real.log ((covariance M β τ).det) =
          Real.log ((1 + (τ / β) • (M.transpose * M)).det) := by
    calc
      Real.log ((β⁻¹ • (1 : Matrix n n ℝ)).det) -
          Real.log ((covariance M β τ).det) = Real.log (((β⁻¹ • (1 : Matrix n n ℝ)).det) *
            ((precision M β τ).det)) := by
        rw [hdetCov, Real.log_inv, Real.log_mul hdetPriorPos.ne' hdetPrecisionPos.ne']
        ring
      _ = Real.log ((1 + (τ / β) • (M.transpose * M)).det) := congrArg Real.log hdetFactor
    all_goals rfl
  refine ⟨InformationTheory.klDiv_ne_top hAC hllrInt, hllrInt, hllrMean, hMICov, ?_, ?_, posterior_disintegration M β τ hβ hτ, input_factors β τ hβ hτ⟩
  · rw [hMICov, hlogdet]
  · change ((∫ y : E p, physicalFreeEnergy β (posteriorKernel M β τ y) ∂dataLaw M β τ) - physicalFreeEnergy β (multivariateGaussian 0 (β⁻¹ • (1 : Matrix n n ℝ)))) =
      β⁻¹ * (mutualInformation M β τ).toReal
    rw [hFree M β τ hβ hτ, hMICov]
    ring

end D5.S3.Observer.Linear.GaussianObservationLaw
