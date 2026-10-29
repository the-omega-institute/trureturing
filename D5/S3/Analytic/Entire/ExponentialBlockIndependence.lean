/- GID: D5/S3/Analytic/Entire/ExponentialBlockIndependence
   generality: G
   mirror-B: D5/B/S3/Analytic/Entire/ExponentialBlockIndependence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Independence of distinct entire exponential-polynomial derivative blocks. -/

import D5.S3.Analytic.Entire.ExponentialPolynomial
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! Distinct complex exponential blocks belong to independent generalized eigenspaces. -/

noncomputable section

namespace D5.S3.Analytic.Entire
open scoped BigOperators Classical

/-- Scalar differentiation on all entire functions. This is an algebraic
endomorphism of the entire-function module, with no Fock boundedness claim. -/
def entireDerivative : Module.End ℂ entireSubmodule where
  toFun f := ⟨deriv (f : ℂ → ℂ), f.property.deriv⟩
  map_add' f g := by
    apply Subtype.ext
    funext z
    exact deriv_add (f.property z) (g.property z)
  map_smul' c f := by
    apply Subtype.ext
    funext z
    exact deriv_const_mul c (f.property z)

def exponentialPolynomialBlock (α : ℂ) (p : Polynomial ℂ) : entireSubmodule :=
  ⟨fun z => Complex.exp (α * z) * p.eval z,
    (Complex.differentiable_exp.comp (differentiable_id.const_mul α)).mul p.differentiable⟩

theorem shifted_derivative_block (α : ℂ) (p : Polynomial ℂ) :
    (entireDerivative - α • 1) (exponentialPolynomialBlock α p) =
      exponentialPolynomialBlock α p.derivative := by
  apply Subtype.ext
  funext z
  have he := (Complex.hasDerivAt_exp (α * z)).comp z
    ((hasDerivAt_id z).const_mul α)
  change deriv (fun x => Complex.exp (α * x) * p.eval x) z -
    α * (Complex.exp (α * z) * p.eval z) =
      Complex.exp (α * z) * p.derivative.eval z
  have hd := (he.mul (p.hasDerivAt z)).deriv
  change deriv (fun x => Complex.exp (α * x) * p.eval x) z = _ at hd
  rw [hd]
  simp only [Function.comp_apply]
  ring

theorem shifted_derivative_pow_block (α : ℂ) (p : Polynomial ℂ) (n : ℕ) :
    ((entireDerivative - α • 1) ^ n) (exponentialPolynomialBlock α p) =
      exponentialPolynomialBlock α (Polynomial.derivative^[n] p) := by
  induction n with
  | zero => simp only [pow_zero, Module.End.one_apply, Function.iterate_zero_apply]
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, ih, shifted_derivative_block,
      Function.iterate_succ_apply']

theorem block_mem_generalized_eigenspace (α : ℂ) (p : Polynomial ℂ) :
    exponentialPolynomialBlock α p ∈ entireDerivative.maxGenEigenspace α := by
  apply (Module.End.mem_maxGenEigenspace _ _ _).mpr
  refine ⟨p.natDegree + 1, ?_⟩
  rw [shifted_derivative_pow_block,
    Polynomial.iterate_derivative_eq_zero (Nat.lt_succ_self p.natDegree)]
  apply Subtype.ext
  funext z
  simp [exponentialPolynomialBlock]

theorem exponential_polynomial_block_ne_zero (α : ℂ) {p : Polynomial ℂ}
    (hp : p ≠ 0) : exponentialPolynomialBlock α p ≠ 0 := by
  intro h
  apply hp
  apply Polynomial.funext
  intro z
  have hz := congrArg (fun f : entireSubmodule => (f : ℂ → ℂ) z) h
  change Complex.exp (α * z) * p.eval z = 0 at hz
  simpa only [Polynomial.eval_zero] using (mul_eq_zero.mp hz).resolve_left (Complex.exp_ne_zero _)

/-- Nonzero polynomial-exponential blocks at arbitrary distinct complex
parameters are linearly independent. No growth separation along a chosen
real ray, positivity, real-coefficient premise or finite cutoff is used. -/
theorem independent_exponential_polynomial_blocks {ι : Type*}
    (α : ι → ℂ) (hα : Function.Injective α) (p : ι → Polynomial ℂ)
    (hp : ∀ i, p i ≠ 0) :
    LinearIndependent ℂ (fun i => exponentialPolynomialBlock (α i) (p i)) :=
  entireDerivative.independent_maxGenEigenspace.comp hα |>.linearIndependent _
    (fun i => block_mem_generalized_eigenspace _ _)
    (fun i => exponential_polynomial_block_ne_zero _ (hp i))

/-- A finite presentation can be normalized at the actual complex exponents,
without introducing a real-parameter restriction or retaining zero blocks. -/
theorem ExponentialPolynomial.distinct_presentation {f : ℂ → ℂ}
    (hf : ExponentialPolynomial f) :
    ∃ (s : Finset ℂ) (p : ℂ → Polynomial ℂ),
      (∀ α ∈ s, p α ≠ 0) ∧
      ∀ z, f z = ∑ α ∈ s, Complex.exp (α*z) * (p α).eval z := by
  classical
  obtain ⟨n, α, q, hq⟩ := hf
  let t : Finset ℂ := Finset.univ.image α
  let p : ℂ → Polynomial ℂ := fun β => ∑ i : Fin n, if α i = β then q i else 0
  refine ⟨t.filter (fun β => p β ≠ 0), p, ?_, ?_⟩
  · intro β hβ
    exact (Finset.mem_filter.mp hβ).2
  · intro z
    rw [Finset.sum_filter]
    have hfilter : (∑ β ∈ t, if p β ≠ 0 then
        Complex.exp (β*z) * (p β).eval z else 0) =
        ∑ β ∈ t, Complex.exp (β*z) * (p β).eval z := by
      apply Finset.sum_congr rfl
      intro β _
      by_cases h : p β = 0 <;> simp [h]
    rw [hfilter, hq]
    simp only [p, Polynomial.eval_finsetSum, apply_ite,
      Polynomial.eval_zero, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    have hi : α i ∈ t := Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
    simp only [mul_ite, mul_zero]
    rw [Finset.sum_eq_single (α i)]
    · simp
    · intro β _ hβ
      exact if_neg (Ne.symm hβ)
    · exact fun h => (h hi).elim

/-- Evaluation of an arbitrary finite tuple of polynomial blocks. -/
def blockEvaluation {ι : Type*} [Fintype ι] (α : ι → ℂ) :
    (ι → Polynomial ℂ) →ₗ[ℂ] (ℂ → ℂ) where
  toFun p z := ∑ i, Complex.exp (α i*z) * (p i).eval z
  map_add' p q := by
    funext z
    simp only [Pi.add_apply, Polynomial.eval_add, mul_add, Finset.sum_add_distrib]
  map_smul' c p := by
    funext z
    simp only [Pi.smul_apply, Polynomial.eval_smul, smul_eq_mul, Finset.mul_sum,
      RingHom.id_apply]
    apply Finset.sum_congr rfl
    intro i _
    ring

/-- Distinct complex exponential blocks have unique polynomial coordinates,
with no degree bound on the tuple. -/
theorem block_evaluation_injective {ι : Type*} [Fintype ι]
    (α : ι → ℂ) (hα : Function.Injective α) :
    Function.Injective (blockEvaluation α) := by
  classical
  apply (injective_iff_map_eq_zero _).mpr
  intro p hp
  have hsum : (∑ i, exponentialPolynomialBlock (α i) (p i)) = 0 := by
    apply Subtype.ext
    funext z
    have hz := congrFun hp z
    simpa only [blockEvaluation, LinearMap.coe_mk, AddHom.coe_mk,
      exponentialPolynomialBlock, Submodule.coe_sum, Submodule.coe_zero,
      Finset.sum_apply, Pi.zero_apply] using hz
  have hind := entireDerivative.independent_maxGenEigenspace.comp hα
  have heach := (iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero _).mp hind
    Finset.univ (fun i => exponentialPolynomialBlock (α i) (p i))
    (fun i _ => block_mem_generalized_eigenspace _ _) hsum
  funext i
  by_contra hi
  exact exponential_polynomial_block_ne_zero (α i) hi (heach i (Finset.mem_univ _))

/-- The entire polynomial-exponential part at one exponent, extended as an
algebraic linear projection on all functions. -/
def blockProjection {ι : Type*} [Fintype ι] (α : ι → ℂ) (i : ι) :
    (ℂ → ℂ) →ₗ[ℂ] (ℂ → ℂ) where
  toFun f z := Complex.exp (α i*z) * (((blockEvaluation α).leftInverse f) i).eval z
  map_add' f g := by
    funext z
    simp only [map_add, Pi.add_apply, Polynomial.eval_add, mul_add]
  map_smul' c f := by
    funext z
    simp only [map_smul, Pi.smul_apply, Polynomial.eval_smul, smul_eq_mul,
      RingHom.id_apply]
    ring

theorem block_projection_evaluation {ι : Type*} [Fintype ι]
    (α : ι → ℂ) (hα : Function.Injective α) (p : ι → Polynomial ℂ) (i : ι) :
    blockProjection α i (blockEvaluation α p) =
      fun z => Complex.exp (α i*z) * (p i).eval z := by
  change (fun z => Complex.exp (α i*z) *
    (((blockEvaluation α).leftInverse (blockEvaluation α p)) i).eval z) = _
  rw [LinearMap.leftInverse_apply_of_inj
    (LinearMap.ker_eq_bot.mpr (block_evaluation_injective α hα))]

theorem block_projection_single {ι : Type*} [Fintype ι]
    (α : ι → ℂ) (hα : Function.Injective α) (i j : ι) (p : Polynomial ℂ) :
    blockProjection α i (fun z => Complex.exp (α j*z) * p.eval z) =
      if i = j then (fun z => Complex.exp (α j*z) * p.eval z) else 0 := by
  classical
  have hsum : blockEvaluation α (Pi.single j p) =
      fun z => Complex.exp (α j*z) * p.eval z := by
    funext z
    change (∑ a, Complex.exp (α a*z) * ((Pi.single j p : ι → Polynomial ℂ) a).eval z) = _
    simp only [Pi.single_apply, apply_ite, Polynomial.eval_zero, mul_ite, mul_zero]
    simp
  rw [← hsum, block_projection_evaluation α hα]
  by_cases hij : i = j
  · subst i
    simp only [if_pos rfl, Pi.single_eq_same]
    exact hsum.symm
  · simp only [if_neg hij, Pi.single_eq_of_ne hij, Polynomial.eval_zero, mul_zero]
    rfl

/-- Projecting the left variable of a weighted exponential-polynomial sum
selects exactly that exponent block, with the polynomial dependence on the
other variable reconstructed before the projection is applied. -/
theorem block_projection_weighted_sum {ι : Type*} [Fintype ι]
    (α : ι → ℂ) (hα : Function.Injective α) (p : ι → Polynomial ℂ)
    (i : ι) (w : ℂ) :
    blockProjection α i (fun z => weightedHankel (blockEvaluation α p) z w) =
      fun z => weightedHankel (fun z => Complex.exp (α i*z) * (p i).eval z) z w := by
  let q : ι → Polynomial ℂ := fun j =>
    Polynomial.C (Complex.exp (α j*w)) *
      (Polynomial.X-Polynomial.C w)^2 * Polynomial.taylor w (p j)
  have hsum : (fun z => weightedHankel (blockEvaluation α p) z w) =
      blockEvaluation α q := by
    funext z
    simp only [weightedHankel, blockEvaluation, LinearMap.coe_mk, AddHom.coe_mk,
      q, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub,
      Polynomial.eval_C, Polynomial.eval_X, Polynomial.taylor_eval, Finset.mul_sum,
      mul_add, Complex.exp_add]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hsum, block_projection_evaluation α hα]
  funext z
  simp only [q, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.taylor_eval, weightedHankel,
    mul_add, Complex.exp_add]
  ring

theorem block_projection_weighted_single {ι : Type*} [Fintype ι]
    (α : ι → ℂ) (hα : Function.Injective α) (i j : ι) (p : Polynomial ℂ) (w : ℂ) :
    blockProjection α i
      (fun z => weightedHankel (fun z => Complex.exp (α j*z) * p.eval z) z w) =
      if i = j then
        (fun z => weightedHankel (fun z => Complex.exp (α j*z) * p.eval z) z w)
      else 0 := by
  let q : Polynomial ℂ := Polynomial.C (Complex.exp (α j*w)) *
    (Polynomial.X-Polynomial.C w)^2 * Polynomial.taylor w p
  have hq : (fun z => weightedHankel (fun z => Complex.exp (α j*z) * p.eval z) z w) =
      fun z => Complex.exp (α j*z) * q.eval z := by
    funext z
    simp only [q, weightedHankel, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_sub, Polynomial.eval_C, Polynomial.eval_X,
      Polynomial.taylor_eval, mul_add, Complex.exp_add]
    ring
  rw [hq, block_projection_single α hα]

theorem block_projection_weighted_single_right {ι : Type*} [Fintype ι]
    (α : ι → ℂ) (hα : Function.Injective α) (i j : ι) (p : Polynomial ℂ) (z : ℂ) :
    blockProjection α i
      (fun w => weightedHankel (fun z => Complex.exp (α j*z) * p.eval z) z w) =
      if i = j then
        (fun w => weightedHankel (fun z => Complex.exp (α j*z) * p.eval z) z w)
      else 0 := by
  have hsym : (fun w => weightedHankel (fun z => Complex.exp (α j*z) * p.eval z) z w) =
      fun w => weightedHankel (fun z => Complex.exp (α j*z) * p.eval z) w z := by
    funext w
    simp only [weightedHankel, add_comm w z]
    ring
  rw [hsym]
  exact block_projection_weighted_single α hα i j p z

#print axioms independent_exponential_polynomial_blocks

end D5.S3.Analytic.Entire
