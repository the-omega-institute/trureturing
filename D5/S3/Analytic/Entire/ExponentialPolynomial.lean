/- GID: D5/S3/Analytic/Entire/ExponentialPolynomial
   generality: G
   mirror-B: D5/B/S3/Analytic/Entire/ExponentialPolynomial
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite entire translation spaces reconstructed by generalized derivative eigenspaces. -/

import D5.S3.Analytic.Entire.WeightedHankel
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! Generalized derivative eigenvectors reconstruct entire exponential polynomials. -/

noncomputable section
open scoped BigOperators

namespace D5.S3.Analytic.Entire

/-- Finite sums of polynomial-exponential blocks, over arbitrary complex
parameters and coefficients. Repeated parameters and zero polynomials are
allowed in a presentation; these do not enlarge the class of functions. -/
def ExponentialPolynomial (f : ℂ → ℂ) : Prop :=
  ∃ n : ℕ, ∃ α : Fin n → ℂ, ∃ p : Fin n → Polynomial ℂ,
    ∀ z, f z = ∑ i, Complex.exp (α i * z) * (p i).eval z

theorem exponential_polynomial_zero : ExponentialPolynomial (0 : ℂ → ℂ) := by
  refine ⟨0, Fin.elim0, Fin.elim0, ?_⟩
  intro z
  simp

theorem ExponentialPolynomial.block (α : ℂ) (p : Polynomial ℂ) :
    ExponentialPolynomial (fun z => Complex.exp (α * z) * p.eval z) := by
  refine ⟨1, fun _ => α, fun _ => p, ?_⟩
  intro z
  simp

theorem ExponentialPolynomial.add {f g : ℂ → ℂ}
    (hf : ExponentialPolynomial f) (hg : ExponentialPolynomial g) :
    ExponentialPolynomial (f + g) := by
  obtain ⟨m, α, p, hf⟩ := hf
  obtain ⟨n, β, q, hg⟩ := hg
  refine ⟨m + n, Fin.addCases α β, Fin.addCases p q, ?_⟩
  intro z
  rw [Fin.sum_univ_add]
  simpa only [Fin.addCases_left, Fin.addCases_right, Pi.add_apply, hf, hg]

theorem ExponentialPolynomial.smul (c : ℂ) {f : ℂ → ℂ}
    (hf : ExponentialPolynomial f) : ExponentialPolynomial (c • f) := by
  obtain ⟨n, α, p, hf⟩ := hf
  refine ⟨n, α, fun i => c • p i, ?_⟩
  intro z
  simp only [Pi.smul_apply, smul_eq_mul, hf, Finset.mul_sum, Polynomial.eval_smul]
  apply Finset.sum_congr rfl
  intro i _
  ring

def exponentialPolynomialSubmodule : Submodule ℂ (ℂ → ℂ) where
  carrier := {f | ExponentialPolynomial f}
  zero_mem' := exponential_polynomial_zero
  add_mem' := ExponentialPolynomial.add
  smul_mem' := ExponentialPolynomial.smul

/-- A scalar polynomial has a polynomial primitive over the complex numbers. -/
theorem exists_polynomial_primitive (p : Polynomial ℂ) :
    ∃ q : Polynomial ℂ, q.derivative = p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    obtain ⟨P, hP⟩ := hp
    obtain ⟨Q, hQ⟩ := hq
    exact ⟨P + Q, by rw [Polynomial.derivative_add, hP, hQ]⟩
  | monomial n a =>
    refine ⟨Polynomial.monomial (n + 1) (a / (n + 1)), ?_⟩
    rw [Polynomial.derivative_monomial_succ]
    congr 1
    exact div_mul_cancel₀ a (by exact_mod_cast Nat.succ_ne_zero n)

/-- An entire function killed by an actual iterated scalar derivative is a
polynomial function. This proof uses primitives and the complex mean-value
constant-function theorem, rather than a formal ODE premise. -/
theorem polynomial_of_iterated_deriv_zero (n : ℕ) {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hzero : iteratedDeriv n f = 0) :
    ∃ p : Polynomial ℂ, ∀ z, f z = p.eval z := by
  induction n generalizing f with
  | zero =>
    refine ⟨0, ?_⟩
    intro z
    simpa only [iteratedDeriv_zero, Polynomial.eval_zero, Pi.zero_apply] using congrFun hzero z
  | succ n ih =>
    have hd : iteratedDeriv n (deriv f) = 0 := by
      simpa only [iteratedDeriv_succ'] using hzero
    obtain ⟨p, hp⟩ := ih hf.deriv hd
    obtain ⟨q, hq⟩ := exists_polynomial_primitive p
    let g : ℂ → ℂ := fun z => f z - q.eval z
    have hg : Differentiable ℂ g := hf.sub q.differentiable
    have hgzero (z : ℂ) : deriv g z = 0 := by
      change deriv (f - fun x => q.eval x) z = 0
      rw [deriv_sub (hf z) q.differentiableAt, Polynomial.deriv, hq, hp]
      exact sub_self _
    refine ⟨q + Polynomial.C (g 0), ?_⟩
    intro z
    have hc : g z = g 0 := is_const_of_deriv_eq_zero hg hgzero z 0
    simp only [Polynomial.eval_add, Polynomial.eval_C]
    change f z - q.eval z = g 0 at hc
    exact sub_eq_iff_eq_add.mp hc |>.trans (add_comm _ _)

theorem iterated_deriv_polynomial (n : ℕ) (p : Polynomial ℂ) :
    iteratedDeriv n (fun z : ℂ => p.eval z) =
      fun z => (Polynomial.derivative^[n] p).eval z := by
  induction n with
  | zero => simp only [iteratedDeriv_zero, Function.iterate_zero_apply]
  | succ n ih =>
    rw [iteratedDeriv_succ, ih, Function.iterate_succ_apply']
    funext z
    exact Polynomial.deriv _

/-- The polynomial reconstructed from a vanishing n-th derivative has
degree less than n, with the zero polynomial handled exactly when n=0. -/
theorem polynomial_of_iterated_deriv_zero_bounded (n : ℕ) {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hzero : iteratedDeriv n f = 0) :
    ∃ p : Polynomial ℂ, (∀ z, f z = p.eval z) ∧ (p = 0 ∨ p.natDegree < n) := by
  obtain ⟨p, hp⟩ := polynomial_of_iterated_deriv_zero n hf hzero
  refine ⟨p, hp, ?_⟩
  by_cases hp0 : p = 0
  · exact Or.inl hp0
  · right
    have heq : f = fun z => p.eval z := funext hp
    rw [heq, iterated_deriv_polynomial] at hzero
    have hpoly : Polynomial.derivative^[n] p = 0 := by
      apply Polynomial.funext
      intro z
      simpa only [Polynomial.eval_zero, Pi.zero_apply] using congrFun hzero z
    by_contra hdegree
    have hn : n ≤ p.natDegree := Nat.le_of_not_gt hdegree
    have hc := congrArg (fun q : Polynomial ℂ => q.coeff (p.natDegree - n)) hpoly
    rw [Polynomial.coeff_iterate_derivative, Nat.sub_add_cancel hn,
      Polynomial.coeff_zero, Polynomial.coeff_natDegree, nsmul_eq_mul] at hc
    have hfac : (p.natDegree.descFactorial n : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.descFactorial_pos.mpr hn).ne'
    exact (mul_ne_zero hfac (Polynomial.leadingCoeff_ne_zero.mpr hp0)) hc

def exponentialGauge (α : ℂ) (f : ℂ → ℂ) : ℂ → ℂ :=
  fun z => Complex.exp (-α * z) * f z

theorem exponential_gauge_entire (α : ℂ) {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) : Differentiable ℂ (exponentialGauge α f) :=
  (Complex.differentiable_exp.comp (differentiable_id.const_mul (-α))).mul hf

/-- Multiplication by exp(-α z) conjugates D-α to the scalar derivative. -/
theorem deriv_exponential_gauge (α : ℂ) {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) :
    deriv (exponentialGauge α f) = exponentialGauge α (deriv f - α • f) := by
  funext z
  have he := (Complex.hasDerivAt_exp (-α * z)).comp z
    ((hasDerivAt_id z).const_mul (-α))
  have h := (he.mul (hf z).hasDerivAt).deriv
  change deriv (fun x => Complex.exp (-α * x) * f x) z = _ at h
  change deriv (fun x => Complex.exp (-α * x) * f x) z = _
  rw [h]
  simp only [exponentialGauge, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    Function.comp_apply]
  ring

theorem iterated_deriv_exponential_gauge
    (W : Submodule ℂ (ℂ → ℂ)) [FiniteDimensional ℂ W]
    (hentire : W ≤ entireSubmodule)
    (htranslate : ∀ t, W ≤ W.comap (translateLinear t))
    (α : ℂ) (n : ℕ) (f : W) :
    iteratedDeriv n (exponentialGauge α f) =
      exponentialGauge α (((derivativeEnd W hentire htranslate - α • 1) ^ n) f) := by
  induction n with
  | zero => simp only [iteratedDeriv_zero, pow_zero, Module.End.one_apply]
  | succ n ih =>
    rw [iteratedDeriv_succ, ih, pow_succ', Module.End.mul_apply]
    rw [deriv_exponential_gauge α (hentire (Submodule.coe_mem _))]
    rfl

/-- Every generalized derivative eigenvector is a genuine polynomial times
an exponential on the entire complex plane. -/
theorem exponential_polynomial_of_generalized_eigenvector
    (W : Submodule ℂ (ℂ → ℂ)) [FiniteDimensional ℂ W]
    (hentire : W ≤ entireSubmodule)
    (htranslate : ∀ t, W ≤ W.comap (translateLinear t))
    (α : ℂ) (f : W)
    (hf : f ∈ (derivativeEnd W hentire htranslate).maxGenEigenspace α) :
    ExponentialPolynomial (f : ℂ → ℂ) := by
  obtain ⟨n, hn⟩ := (Module.End.mem_maxGenEigenspace _ _ _).mp hf
  have hzero : iteratedDeriv n (exponentialGauge α f) = 0 := by
    rw [iterated_deriv_exponential_gauge W hentire htranslate, hn]
    funext z
    simp [exponentialGauge]
  obtain ⟨p, hp, _hdegree⟩ := polynomial_of_iterated_deriv_zero_bounded n
    (exponential_gauge_entire α (hentire f.property)) hzero
  have heq : (f : ℂ → ℂ) = fun z => Complex.exp (α * z) * p.eval z := by
    funext z
    rw [← hp z]
    simp only [exponentialGauge, ← mul_assoc, ← Complex.exp_add, ← add_mul,
      add_neg_cancel, zero_mul, Complex.exp_zero, one_mul]
  rw [heq]
  exact ExponentialPolynomial.block α p

/-- The finite entire translation-space theorem, with no assumption that
the given functions belong to Fock space. -/
theorem exponential_polynomial_of_finite_translation_space {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) [FiniteDimensional ℂ (translationSpace f)] :
    ExponentialPolynomial f := by
  let W := translationSpace f
  let D := derivativeEnd W (translation_space_entire hf) (translation_space_invariant f)
  have hle : (⊤ : Submodule ℂ W) ≤
      exponentialPolynomialSubmodule.comap W.subtype := by
    rw [← Module.End.iSup_maxGenEigenspace_eq_top D]
    apply iSup_le
    intro α g hg
    exact exponential_polynomial_of_generalized_eigenvector W
      (translation_space_entire hf) (translation_space_invariant f) α g hg
  exact hle (show (⟨f, mem_translation_space f⟩ : W) ∈ ⊤ from Submodule.mem_top)

theorem exponential_polynomial_of_weighted_separation {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hF : FiniteSeparated (weightedHankel f)) :
    ExponentialPolynomial f := by
  letI := finite_translation_space_of_weighted hf hF
  exact exponential_polynomial_of_finite_translation_space hf

theorem FiniteSeparated.sum {ι : Type*} (s : Finset ι)
    (F : ι → (ℂ → ℂ → ℂ)) (hF : ∀ i ∈ s, FiniteSeparated (F i)) :
    FiniteSeparated (∑ i ∈ s, F i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    change FiniteSeparated (fun _ _ : ℂ => 0)
    exact finite_separated_const 0
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (hF i (Finset.mem_insert_self _ _)).add
      (ih (fun j hj => hF j (Finset.mem_insert_of_mem hj)))

theorem FiniteSeparated.polynomial_eval {F : ℂ → ℂ → ℂ}
    (hF : FiniteSeparated F) (p : Polynomial ℂ) :
    FiniteSeparated (fun z w => p.eval (F z w)) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    convert hp.add hq using 1
    funext z w
    simp only [Polynomial.eval_add, Pi.add_apply]
  | monomial n a =>
    simpa only [Polynomial.eval_monomial, Pi.pow_apply] using (hF.pow n).const_mul a

theorem finite_separated_left_coordinate : FiniteSeparated (fun z _ : ℂ => z) := by
  refine ⟨1, ?_⟩
  simpa using separated_of_fintype (fun _ : Fin 1 => (id : ℂ → ℂ))
    (fun _ : Fin 1 => fun _ : ℂ => (1 : ℂ))
    (fun _ => differentiable_id) (fun _ => differentiable_const _)

theorem finite_separated_right_coordinate : FiniteSeparated (fun _ w : ℂ => w) := by
  refine ⟨1, ?_⟩
  simpa using separated_of_fintype (fun _ : Fin 1 => fun _ : ℂ => (1 : ℂ))
    (fun _ : Fin 1 => (id : ℂ → ℂ))
    (fun _ => differentiable_const _) (fun _ => differentiable_id)

theorem finite_separated_exponential_hankel (α : ℂ) :
    FiniteSeparated (fun z w => Complex.exp (α * (z + w))) := by
  refine ⟨1, ?_⟩
  have he : Differentiable ℂ (fun z : ℂ => Complex.exp (α * z)) :=
    Complex.differentiable_exp.comp (differentiable_id.const_mul α)
  simpa only [Fintype.card_fin, Fin.sum_univ_one, mul_add, Complex.exp_add] using
    separated_of_fintype (fun _ : Fin 1 => fun z : ℂ => Complex.exp (α * z))
      (fun _ : Fin 1 => fun z : ℂ => Complex.exp (α * z)) (fun _ => he) (fun _ => he)

theorem finite_separated_weighted_exponential_block (α : ℂ) (p : Polynomial ℂ) :
    FiniteSeparated (weightedHankel (fun z => Complex.exp (α * z) * p.eval z)) := by
  have hdiff := (finite_separated_left_coordinate.sub finite_separated_right_coordinate).pow 2
  have hpoly := (finite_separated_left_coordinate.add finite_separated_right_coordinate).polynomial_eval p
  convert (hdiff.mul (finite_separated_exponential_hankel α)).mul hpoly using 1
  funext z w
  simp only [weightedHankel, Pi.mul_apply, Pi.pow_apply, Pi.sub_apply, Pi.add_apply]
  ring

/-- Every finite polynomial-exponential presentation gives a finite entire
separation of the quadratic kernel, for arbitrary complex coefficients. -/
theorem ExponentialPolynomial.weighted_separation {f : ℂ → ℂ}
    (hf : ExponentialPolynomial f) : FiniteSeparated (weightedHankel f) := by
  classical
  obtain ⟨n, α, p, hf⟩ := hf
  have h := FiniteSeparated.sum Finset.univ
    (fun i : Fin n => weightedHankel (fun z => Complex.exp (α i * z) * (p i).eval z))
    (fun i _ => finite_separated_weighted_exponential_block _ _)
  have heq : (∑ i : Fin n,
      weightedHankel (fun z => Complex.exp (α i * z) * (p i).eval z)) =
        weightedHankel f := by
    funext z w
    simp only [Finset.sum_apply, weightedHankel, hf, Finset.mul_sum]
  rw [heq] at h
  exact h

/-- The complete entire-function classification of the weighted Hankel
kernel. Hilbert-space reconstruction and physical beam-splitter rank joins
are handled separately; neither is assumed in this statement. -/
theorem finite_weighted_separation_iff_exponential_polynomial {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) :
    FiniteSeparated (weightedHankel f) ↔ ExponentialPolynomial f :=
  ⟨exponential_polynomial_of_weighted_separation hf,
    ExponentialPolynomial.weighted_separation⟩

#print axioms polynomial_of_iterated_deriv_zero
#print axioms exponential_polynomial_of_weighted_separation
#print axioms finite_weighted_separation_iff_exponential_polynomial

end D5.S3.Analytic.Entire
