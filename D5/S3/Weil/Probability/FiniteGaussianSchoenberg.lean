/- GID: D5/S3/Weil/Probability/FiniteGaussianSchoenberg
   generality: G
   mirror-B: D5/B/S3/Weil/Probability/FiniteGaussianSchoenberg
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The Schur product theorem and the scalar exponential series prove complex Gaussian positivity for every finite real Gram matrix. -/

import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
This is the finite Gram form of the classical forward Schoenberg theorem.
The exponential is entrywise, never the matrix exponential. Schur powers and
nonnegative factorial weights give positive partial sums. Scalar exponential
convergence then preserves every finite quadratic inequality. Real positivity
is transported to complex coefficients by an actual Gram factorization.
No conditional-negative-definiteness or exponential-positivity oracle is used.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Weil.Probability.FiniteGaussianSchoenberg

open Matrix Filter Topology
open scoped BigOperators ComplexOrder MatrixOrder

variable {I : Type*} [Fintype I] [DecidableEq I]

private theorem ones_posSemidef : Matrix.PosSemidef (fun _ _ : I => (1 : ℝ)) := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    (by apply Matrix.IsHermitian.ext; intros; rfl)
  intro x
  simpa only [dotProduct, mulVec, star_trivial, one_mul, ← Finset.mul_sum,
    ← Finset.sum_mul, pow_two] using sq_nonneg (∑ i, x i)

private theorem entrywise_power_posSemidef (A : Matrix I I ℝ) (hA : A.PosSemidef) :
    ∀ n : ℕ, Matrix.PosSemidef (fun i j => A i j ^ n) := by
  intro n
  induction n with
  | zero => simpa only [pow_zero] using (ones_posSemidef (I := I))
  | succ n ih =>
      have hp : (fun i j => A i j ^ (n + 1)) = (fun i j => A i j ^ n) ⊙ A := by
        ext i j
        exact pow_succ (A i j) n
      rw [hp]
      exact ih.hadamard hA

/-- Entrywise exponentiation preserves real Gram positivity, using the Schur
product theorem and the convergent scalar series rather than spectral calculus. -/
theorem entrywise_exp_posSemidef (A : Matrix I I ℝ) (hA : A.PosSemidef) :
    Matrix.PosSemidef (fun i j => Real.exp (A i j)) := by
  let partialSum (N : ℕ) : Matrix I I ℝ :=
    ∑ n ∈ Finset.range N, (n.factorial : ℝ)⁻¹ • Matrix.of (fun i j => A i j ^ n)
  have hpartial (N : ℕ) : (partialSum N).PosSemidef :=
    Matrix.posSemidef_sum _ (fun n _ =>
      (entrywise_power_posSemidef A hA n).smul (by positivity))
  have hlimit : Tendsto partialSum atTop (𝓝 (fun i j => Real.exp (A i j))) := by
    apply tendsto_pi_nhds.mpr
    intro i
    apply tendsto_pi_nhds.mpr
    intro j
    have hsum : HasSum (fun n : ℕ => A i j ^ n / (n.factorial : ℝ)) (Real.exp (A i j)) := by
      rw [Real.exp_eq_exp_ℝ]
      exact NormedSpace.expSeries_div_hasSum_exp (A i j)
    simpa only [partialSum, Matrix.sum_apply, Matrix.smul_apply, Matrix.of_apply,
      smul_eq_mul, div_eq_mul_inv, mul_comm] using hsum.tendsto_sum_nat
  have hsym (i j : I) : A j i = A i j := by
    simpa only [star_trivial] using hA.isHermitian.apply i j
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    (by apply Matrix.IsHermitian.ext; intro i j; simp only [star_trivial, hsym])
  intro x
  have hcontinuous : Continuous (fun B : Matrix I I ℝ => star x ⬝ᵥ (B *ᵥ x)) := by
    unfold dotProduct mulVec
    fun_prop
  exact ge_of_tendsto (hcontinuous.continuousAt.tendsto.comp hlimit)
    (Filter.Eventually.of_forall fun N => (hpartial N).dotProduct_mulVec_nonneg x)

/-- Squared Gram distances have an exact zero-sum quadratic identity. -/
theorem gram_distance_zero_sum (A : Matrix I I ℝ) (x : I → ℝ) (hx : ∑ i, x i = 0) :
    (∑ i, ∑ j, x i * x j * (A i i + A j j - 2 * A i j)) =
      -2 * (star x ⬝ᵥ (A *ᵥ x)) := by
  have entry (i j : I) : x i * x j * (A i i + A j j - 2 * A i j) =
      (x i * A i i) * x j + x i * (x j * A j j) - 2 * (x i * A i j * x j) := by ring
  conv_lhs =>
    arg 2
    ext i
    arg 2
    ext j
    rw [entry]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp_rw [← Finset.mul_sum, ← Finset.sum_mul]
  simp only [hx, mul_zero, zero_mul, add_zero, zero_sub]
  simp only [dotProduct, mulVec, star_trivial, Finset.mul_sum, mul_assoc]
  ring_nf
  simp only [← Finset.sum_neg_distrib]

/-- Every squared Gram-distance matrix is conditionally negative on real
zero-sum vectors. Repeated points and singular Gram matrices are allowed. -/
theorem gram_distance_conditionally_negative (A : Matrix I I ℝ) (hA : A.PosSemidef)
    (x : I → ℝ) (hx : ∑ i, x i = 0) :
    (∑ i, ∑ j, x i * x j * (A i i + A j j - 2 * A i j)) ≤ 0 := by
  rw [gram_distance_zero_sum A x hx]
  linarith [hA.dotProduct_mulVec_nonneg x]

/-- The Gaussian of squared Gram distance is positive semidefinite for every
nonnegative time, including zero time and degenerate Gram matrices. -/
theorem real_gram_gaussian_posSemidef (A : Matrix I I ℝ) (hA : A.PosSemidef)
    (t : ℝ) (ht : 0 ≤ t) :
    Matrix.PosSemidef (fun i j => Real.exp (-t * (A i i + A j j - 2 * A i j))) := by
  let B : Matrix I I ℝ := fun i j => Real.exp ((2 * t) * A i j)
  have hB : B.PosSemidef :=
    entrywise_exp_posSemidef ((2 * t) • A) (hA.smul (by positivity))
  let d : I → ℝ := fun i => Real.exp (-t * A i i)
  have factor (i j : I) : Real.exp (-t * (A i i + A j j - 2 * A i j)) =
      d i * B i j * d j := by
    simp only [d, B, ← Real.exp_add]
    congr 1
    ring
  have hsym (i j : I) : A j i = A i j := by
    simpa only [star_trivial] using hA.isHermitian.apply i j
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    (by apply Matrix.IsHermitian.ext; intro i j
        simp only [star_trivial, hsym]; congr 1; ring)
  intro x
  have h := hB.dotProduct_mulVec_nonneg (fun i => d i * x i)
  convert h using 1
  simp only [dotProduct, mulVec, star_trivial, Finset.mul_sum, factor]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- A real positive Gram matrix remains positive against complex coefficient
vectors. This scalar extension uses the original matrix's Gram factorization. -/
theorem ofReal_posSemidef (A : Matrix I I ℝ) (hA : A.PosSemidef) :
    Matrix.PosSemidef (fun i j => (A i j : ℂ)) := by
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg
  let C : Matrix I I ℂ := fun i j => (B i j : ℂ)
  have factor : (fun i j => (A i j : ℂ)) = Cᴴ * C := by
    ext i j
    have h := congrArg (fun X : Matrix I I ℝ => (X i j : ℂ)) hB
    change (A i j : ℂ) = ∑ k, star (B k i : ℂ) * (B k j : ℂ)
    simpa only [star_eq_conjTranspose, Matrix.mul_apply, Matrix.conjTranspose_apply,
      star_trivial, Complex.ofReal_sum, Complex.ofReal_mul, Complex.star_def,
      Complex.conj_ofReal] using h
  rw [factor]
  exact Matrix.posSemidef_conjTranspose_mul_self C

/-- Complex-coefficient forward Schoenberg theorem for any finite real Gram
matrix. The same distance entries are retained in the exponential. -/
theorem gram_gaussian_posSemidef (A : Matrix I I ℝ) (hA : A.PosSemidef)
    (t : ℝ) (ht : 0 ≤ t) :
    Matrix.PosSemidef (fun i j => (Real.exp (-t * (A i i + A j j - 2 * A i j)) : ℂ)) :=
  ofReal_posSemidef _ (real_gram_gaussian_posSemidef A hA t ht)

#print axioms entrywise_exp_posSemidef
#print axioms gram_distance_conditionally_negative
#print axioms gram_gaussian_posSemidef

end D5.S3.Weil.Probability.FiniteGaussianSchoenberg
