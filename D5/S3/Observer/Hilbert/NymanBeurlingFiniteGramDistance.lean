/- GID: D5/S3/Observer/Hilbert/NymanBeurlingFiniteGramDistance
   generality: G
   mirror-B: D5/B/S3/Observer/Hilbert/NymanBeurlingFiniteGramDistance
   mirror-E: none(waiver:universal-hilbert-theorem)
   anchors: []
   utility: none
   digest: The complex Nyman-Beurling carrier has the finite singular Gram distance formula. -/

import D5.S3.Observer.Hilbert.FiniteSynthesisGramDistance
import D5.S3.Constants.InnerProducts.FractionalReciprocalInnerProduct

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Observer.Hilbert.NymanBeurlingFiniteGramDistance

open Set MeasureTheory
open scoped ENNReal InnerProductSpace BigOperators
open D5.S3.Constants.InnerProducts.FractionalReciprocalInnerProduct
open D5.S3.Observer.Hilbert.FiniteMoorePenroseInverse
open D5.S3.Observer.Hilbert.FiniteSynthesisGramDistance

/-- The source complex Hilbert carrier, with the canonical positive-half-line measure. -/
abbrev Carrier := Lp ℂ 2 positiveMeasure

private theorem unit_interval_measure : positiveMeasure (Ioo (0 : ℝ) 1) = 1 := by
  rw [positiveMeasure, Measure.restrict_apply measurableSet_Ioo,
    inter_eq_left.mpr Ioo_subset_Ioi_self, Real.volume_Ioo]
  norm_num

/-- The actual unit-interval indicator in the complex carrier. -/
def target : Carrier := indicatorConstLp 2 measurableSet_Ioo
  (by rw [unit_interval_measure]; exact ENNReal.one_ne_top) (1 : ℂ)

/-- The canonical real fractional-reciprocal vector embedded into complex L2. -/
def sourceVector (a : ℕ) (ha : 1 ≤ a) : Carrier :=
  Complex.ofRealCLM.compLp (fractionalReciprocal a ha)

/-- The chosen Lp target represents the source indicator almost everywhere. -/
theorem target_coe_ae : (target : ℝ → ℂ) =ᵐ[positiveMeasure]
    (Ioo (0 : ℝ) 1).indicator (fun _ => (1 : ℂ)) :=
  indicatorConstLp_coeFn

/-- Complexification preserves the canonical fractional-reciprocal representative. -/
theorem sourceVector_coe_ae (a : ℕ) (ha : 1 ≤ a) :
    (sourceVector a ha : ℝ → ℂ) =ᵐ[positiveMeasure]
      fun x => ((Int.fract (1 / ((a : ℝ) * x)) : ℝ) : ℂ) := by
  have hr : (fractionalReciprocal a ha : ℝ → ℝ) =ᵐ[positiveMeasure]
      fractionalReciprocalFn a := by
    unfold fractionalReciprocal
    exact MemLp.coeFn_toLp _
  filter_upwards [Complex.ofRealCLM.coeFn_compLp (fractionalReciprocal a ha), hr]
    with x hx hrx
  simpa only [sourceVector, Complex.ofRealCLM_apply, hrx, fractionalReciprocalFn] using hx

/-- The unit target has exactly the source normalization, proved from its measure. -/
theorem target_norm_sq : ‖target‖ ^ 2 = 1 := by
  rw [target, norm_indicatorConstLp (by norm_num) (by norm_num),
    measureReal_def, unit_interval_measure]
  norm_num

/-- Finite synthesis in the standard orthonormal coordinates indexed by a = i+1. -/
def synthesis (N : ℕ) : EuclideanSpace ℂ (Fin N) →L[ℂ] Carrier :=
  ((EuclideanSpace.basisFun (Fin N) ℂ).toBasis.constr ℂ
    (fun i => sourceVector (i.val + 1) (by omega))).toContinuousLinearMap

/-- The finite arithmetic shell is independently defined as the source span. -/
def shell (N : ℕ) : Submodule ℂ Carrier :=
  Submodule.span ℂ (Set.range (fun i : Fin N => sourceVector (i.val + 1) (by omega)))

instance shell_finiteDimensional (N : ℕ) : FiniteDimensional ℂ (shell N) :=
  FiniteDimensional.span_of_finite ℂ (Set.finite_range _)

instance shell_completeSpace (N : ℕ) : CompleteSpace (shell N) :=
  FiniteDimensional.complete ℂ (shell N)

/-- The distance is the metric infimum over the source span. -/
def distance (N : ℕ) : ℝ := Metric.infDist target (shell N : Set Carrier)

/-- The Gram operator on the actual finite coefficient space. -/
def gramOperator (N : ℕ) : EuclideanSpace ℂ (Fin N) →ₗ[ℂ] EuclideanSpace ℂ (Fin N) :=
  gram (synthesis N)

/-- The target correlations in the standard orthonormal coefficient space. -/
def correlations (N : ℕ) : EuclideanSpace ℂ (Fin N) := (synthesis N).adjoint target

theorem synthesis_apply (N : ℕ) (c : EuclideanSpace ℂ (Fin N)) :
    synthesis N c = ∑ i : Fin N, c i • sourceVector (i.val + 1) (by omega) := by
  simp [synthesis, Module.Basis.constr_apply_fintype, EuclideanSpace.basisFun_repr]

theorem synthesis_range (N : ℕ) : (synthesis N).range = shell N :=
  (EuclideanSpace.basisFun (Fin N) ℂ).toBasis.constr_range ℂ

private theorem synthesis_basis (N : ℕ) (i : Fin N) :
    synthesis N (EuclideanSpace.basisFun (Fin N) ℂ i) =
      sourceVector (i.val + 1) (by omega) := by
  exact (EuclideanSpace.basisFun (Fin N) ℂ).toBasis.constr_basis ℂ _ i

/-- The Gram operator has exactly the source's inner-product entries. -/
theorem gramOperator_entry (N : ℕ) (i j : Fin N) :
    gramOperator N (EuclideanSpace.basisFun (Fin N) ℂ j) i =
      inner ℂ (sourceVector (i.val + 1) (by omega))
        (sourceVector (j.val + 1) (by omega)) := by
  rw [← EuclideanSpace.basisFun_inner]
  change inner ℂ (EuclideanSpace.basisFun (Fin N) ℂ i)
    ((synthesis N).adjoint (synthesis N (EuclideanSpace.basisFun (Fin N) ℂ j))) = _
  rw [ContinuousLinearMap.adjoint_inner_right, synthesis_basis, synthesis_basis]

theorem correlations_entry (N : ℕ) (i : Fin N) :
    correlations N i = inner ℂ (sourceVector (i.val + 1) (by omega)) target := by
  rw [← EuclideanSpace.basisFun_inner]
  change inner ℂ (EuclideanSpace.basisFun (Fin N) ℂ i) ((synthesis N).adjoint target) = _
  rw [ContinuousLinearMap.adjoint_inner_right, synthesis_basis]

/-- All three clauses of source Theorem 29.6, including singular Gram operators.
The real squared distance is coerced into C; the second equality therefore also proves
that the complex Gram quadratic expression is real. The last clause alone assumes
invertibility, expressed as a linear equivalence with the same Gram operator. -/
theorem nyman_beurling_finite_gram_distance (N : ℕ) :
    (shell N).starProjection = (synthesis N).comp
      ((moorePenroseInverse (gramOperator N)).toContinuousLinearMap.comp
        (synthesis N).adjoint) ∧
    (distance N ^ 2 : ℂ) = 1 - inner ℂ (correlations N)
      (moorePenroseInverse (gramOperator N) (correlations N)) ∧
    ∀ G : EuclideanSpace ℂ (Fin N) ≃ₗ[ℂ] EuclideanSpace ℂ (Fin N),
      G.toLinearMap = gramOperator N →
      (distance N ^ 2 : ℂ) = 1 - inner ℂ (correlations N) (G.symm (correlations N)) := by
  have hp := finite_synthesis_gram_projection (synthesis N)
  refine ⟨by simpa only [synthesis_range, gramOperator] using hp, ?_⟩
  have hd : (distance N ^ 2 : ℂ) = 1 - inner ℂ (correlations N)
      (moorePenroseInverse (gramOperator N) (correlations N)) := by
    have hr := finite_synthesis_gram_distance (synthesis N) target
    have hq := finite_synthesis_gram_quadratic (synthesis N) target
    rw [synthesis_range, target_norm_sq] at hr
    change distance N ^ 2 = 1 - Complex.re (inner ℂ (correlations N)
      (moorePenroseInverse (gramOperator N) (correlations N))) at hr
    change inner ℂ (correlations N)
      (moorePenroseInverse (gramOperator N) (correlations N)) = _ at hq
    rw [hq]
    simp only [hq] at hr
    change distance N ^ 2 = 1 - RCLike.re (RCLike.ofReal
      (‖(synthesis N).range.starProjection target‖ ^ 2) : ℂ) at hr
    rw [RCLike.ofReal_re] at hr
    change (Complex.ofReal (distance N)) ^ 2 =
      1 - Complex.ofReal (‖(synthesis N).range.starProjection target‖ ^ 2)
    rw [← Complex.ofReal_pow, hr, Complex.ofReal_sub, Complex.ofReal_one]
  refine ⟨hd, ?_⟩
  intro G hG
  rw [hd, ← hG, moore_penrose_eq_inverse]
  rfl

#print axioms nyman_beurling_finite_gram_distance

end D5.S3.Observer.Hilbert.NymanBeurlingFiniteGramDistance
