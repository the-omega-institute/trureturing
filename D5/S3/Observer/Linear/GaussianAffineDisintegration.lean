/- GID: D5/S3/Observer/Linear/GaussianAffineDisintegration
   generality: G
   mirror-B: D5/B/S3/Observer/Linear/GaussianAffineDisintegration
   mirror-E: none(waiver:general-gaussian-disintegration)
   anchors: []
   digest: Actual rectangular Gaussian images, independent readouts, and constructed affine conditional kernels. -/

import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
import Mathlib.Probability.Kernel.Composition.Prod
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Probability.Kernel.Disintegration.Basic
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Tactic

/-!
Library-first: the v4.33.0 Gaussian covariance and Gaussian independence
APIs, finite-dimensional matrix linear maps, and Markov-kernel products are
used directly. Rectangular matrices act on Euclidean spaces, not on a
silently substituted entrywise-norm Hilbert space. The affine kernel below
is constructed as a map of an actual deterministic/constant kernel product.
Its composition-product identity is equality of probability measures.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace D5.S3.Observer.Linear.GaussianAffineDisintegration

open Matrix MeasureTheory ProbabilityTheory WithLp
open scoped RealInnerProductSpace ProbabilityTheory ENNReal

abbrev E (n : Type*) := EuclideanSpace ℝ n

section Matrices
variable {d a b : Type*} [Fintype d] [DecidableEq d]
  [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

/-- The actual rectangular matrix map, with Euclidean domain and codomain. -/
def action (M : Matrix a d ℝ) : E d →L[ℝ] E a :=
  (Matrix.toEuclideanLin M).toContinuousLinearMap

@[simp] theorem action_apply (M : Matrix a d ℝ) (x : E d) :
    action M x = toLp 2 (M.mulVec (ofLp x)) := rfl

@[simp] theorem action_comp (M : Matrix a b ℝ) (N : Matrix b d ℝ) :
    (action M).comp (action N) = action (M * N) := by
  ext x
  simp only [ContinuousLinearMap.comp_apply, action_apply, ofLp_toLp,
    Matrix.mulVec_mulVec]

@[simp] theorem action_add (M N : Matrix a d ℝ) :
    action (M + N) = action M + action N := by
  ext x
  simp only [action_apply, ContinuousLinearMap.add_apply, Matrix.add_mulVec,
    WithLp.toLp_add]

/-- Transposition is the genuine Hilbert adjoint of the rectangular action. -/
theorem inner_action (M : Matrix a d ℝ) (x : E d) (y : E a) :
    ⟪action M x, y⟫_ℝ = ⟪x, action M.transpose y⟫_ℝ := by
  simpa only [EuclideanSpace.inner_eq_star_dotProduct, action_apply,
    ofLp_toLp, star_trivial, dotProduct_comm] using
    (Matrix.dotProduct_transpose_mulVec M (ofLp x) (ofLp y)).symm

theorem action_adjoint (M : Matrix a d ℝ) :
    (action M).adjoint = action M.transpose := by
  ext y
  apply ext_inner_left ℝ
  intro x
  rw [ContinuousLinearMap.adjoint_inner_right, inner_action]

private theorem transpose_pairing (L : Matrix a d ℝ) (S : Matrix d d ℝ)
    (R : Matrix b d ℝ) (u : a → ℝ) (v : b → ℝ) :
    L.transpose.mulVec u ⬝ᵥ S.mulVec (R.transpose.mulVec v) =
      u ⬝ᵥ (L * S * R.transpose).mulVec v := by
  rw [dotProduct_comm (L.transpose.mulVec u),
    ← Matrix.dotProduct_transpose_mulVec L.transpose]
  simp only [Matrix.transpose_transpose, Matrix.mulVec_mulVec, Matrix.mul_assoc]

/-- Covariance of two actual readouts of the same Gaussian vector. -/
theorem action_cross_covariance (m : E d) (S : Matrix d d ℝ) (hS : S.PosSemidef)
    (L : Matrix a d ℝ) (R : Matrix b d ℝ) (u : E a) (v : E b) :
    cov[fun z => ⟪u, action L z⟫_ℝ, fun z => ⟪v, action R z⟫_ℝ;
      multivariateGaussian m S] = u ⬝ᵥ (L * S * R.transpose).mulVec v := by
  simp_rw [← ContinuousLinearMap.adjoint_inner_left, action_adjoint]
  rw [← covarianceBilin_apply_eq_cov IsGaussian.memLp_two_id,
    covarianceBilin_multivariateGaussian hS]
  exact transpose_pairing L S R (ofLp u) (ofLp v)

/-- Linear image formula, including singular covariances and blind readouts. -/
theorem map_gaussian (m : E d) (S : Matrix d d ℝ) (hS : S.PosSemidef)
    (L : Matrix a d ℝ) :
    (multivariateGaussian m S).map (action L) =
      multivariateGaussian (action L m) (L * S * L.transpose) := by
  have hLS : (L * S * L.transpose).PosSemidef := by
    simpa using hS.mul_mul_conjTranspose_same L
  apply IsGaussian.ext
  · rw [(action L).integral_id_map IsGaussian.integrable_id]
    simp only [integral_id_multivariateGaussian]
  · ext u v
    rw [covarianceBilin_map IsGaussian.memLp_two_id,
      covarianceBilin_multivariateGaussian hS,
      covarianceBilin_multivariateGaussian hLS, action_adjoint]
    exact transpose_pairing L S L (ofLp u) (ofLp v)

/-- Zero cross covariance gives independence for these constructed Gaussian maps. -/
theorem independent_actions (m : E d) (S : Matrix d d ℝ) (hS : S.PosSemidef)
    (L : Matrix a d ℝ) (R : Matrix b d ℝ) (hcross : L * S * R.transpose = 0) :
    IndepFun (action L) (action R) (multivariateGaussian m S) := by
  have hpair : HasGaussianLaw (fun z : E d => (action L z, action R z))
      (multivariateGaussian m S) :=
    (IsGaussian.hasGaussianLaw_id (μ := multivariateGaussian m S)).map_fun
      ((action L).prod (action R))
  apply hpair.indepFun_of_covariance_inner
  intro u v
  rw [action_cross_covariance m S hS L R, hcross, Matrix.zero_mulVec, dotProduct_zero]

/-- Translation is identified by the defining Gaussian map, without a density oracle. -/
theorem translate_gaussian (m c : E d) (S : Matrix d d ℝ) :
    (multivariateGaussian m S).map (fun x => c + x) =
      multivariateGaussian (c + m) S := by
  unfold multivariateGaussian
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext x
  exact (add_assoc c m _).symm

end Matrices

section Kernel
variable {n p : Type*} [Fintype n] [DecidableEq n] [Fintype p] [DecidableEq p]

/-- Sampling a fixed residual and adding a deterministic linear prediction. -/
def translatedKernel (K : E p →L[ℝ] E n) (ν : Measure (E n)) : Kernel (E p) (E n) :=
  ((Kernel.id : Kernel (E p) (E p)) ×ₖ Kernel.const (E p) ν).map
    (fun z : E p × E n => K z.1 + z.2)

instance translatedKernel_markov (K : E p →L[ℝ] E n) (ν : Measure (E n))
    [IsProbabilityMeasure ν] : IsMarkovKernel (translatedKernel K ν) := by
  unfold translatedKernel
  exact Kernel.IsMarkovKernel.map _ (by fun_prop)

/-- The conditional distribution at every data value is the actual translated measure. -/
theorem translatedKernel_apply (K : E p →L[ℝ] E n) (ν : Measure (E n))
    [IsProbabilityMeasure ν] (y : E p) :
    translatedKernel K ν y = ν.map (fun r => K y + r) := by
  have hm : Measurable (fun z : E p × E n => K z.1 + z.2) := by fun_prop
  ext s hs
  rw [translatedKernel, Kernel.map_apply' _ hm _ hs,
    Kernel.id_prod_apply' _ _ (hm hs), Kernel.const_apply,
    Measure.map_apply (by fun_prop) hs]
  rfl

/-- The full joint law of the affine kernel is a pushforward of a product law. -/
theorem translatedKernel_compProd (K : E p →L[ℝ] E n)
    (μ : Measure (E p)) (ν : Measure (E n))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    μ ⊗ₘ translatedKernel K ν =
      (μ.prod ν).map (fun z : E p × E n => (z.1, K z.1 + z.2)) := by
  have ht : Measurable (fun z : E p × E n => (z.1, K z.1 + z.2)) := by fun_prop
  ext s hs
  rw [Measure.compProd_apply hs, Measure.map_apply ht hs, Measure.prod_apply (ht hs)]
  apply lintegral_congr_ae
  filter_upwards [] with y
  rw [translatedKernel_apply, Measure.map_apply (by fun_prop) (measurable_prodMk_left hs)]
  rfl

/-- Constructed disintegration from independent residuals, as equality of joint laws.
The observation-specific theorem discharges residual independence and its law. -/
theorem joint_eq_compProd_of_independent_residual
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → E n) (Y : Ω → E p) (R : Ω → E n)
    (hY : Measurable Y) (hR : Measurable R)
    (K : E p →L[ℝ] E n) (ν : Measure (E n)) [IsProbabilityMeasure ν]
    (hind : IndepFun Y R P) (hlaw : P.map R = ν)
    (hX : ∀ ω, X ω = K (Y ω) + R ω) :
    P.map (fun ω => (Y ω, X ω)) =
      (P.map Y) ⊗ₘ translatedKernel K ν := by
  letI : IsProbabilityMeasure (P.map Y) := P.isProbabilityMeasure_map hY.aemeasurable
  rw [translatedKernel_compProd, ← hlaw,
    ← hind.map_prod_eq_prod_map_map hY.aemeasurable hR.aemeasurable,
    Measure.map_map (by fun_prop) (hY.prodMk hR)]
  congr 1
  funext ω
  exact Prod.ext rfl (hX ω)

end Kernel

#print axioms map_gaussian
#print axioms independent_actions
#print axioms translatedKernel_markov
#print axioms translatedKernel_compProd
#print axioms joint_eq_compProd_of_independent_residual
end D5.S3.Observer.Linear.GaussianAffineDisintegration
