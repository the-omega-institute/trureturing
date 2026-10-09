/- GID: D5/S3/Quantum/Entanglement/WitnessKernelTraceCriteriaRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/WitnessKernelTraceCriteriaRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Entanglement/WitnessKernelTraceCriteriaRefutation.claim; result=D5/S3/Quantum/Entanglement/WitnessKernelTraceCriteriaRefutation.result; claim=D5/S3/Quantum/Entanglement/WitnessKernelTraceCriteriaRefutation.claim
   digest: A two-qubit witness satisfies the kernel criterion but not the trace criterion. -/
import D5.S3.Quantum.Information.PartialTraceMutualInformation
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false
noncomputable section
namespace D5.S3.Quantum.Entanglement.WitnessKernelTraceCriteriaRefutation
open Matrix
open scoped BigOperators ComplexOrder Kronecker
open D5.S3.Quantum.Information.PartialTraceMutualInformation

/-- Nonnegative complex expectation on every product vector. -/
def blockPositive {m n : ℕ} (W : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) : Prop :=
  ∀ (x : Fin m → ℂ) (y : Fin n → ℂ),
    0 ≤ star (fun p : Fin m × Fin n => x p.1 * y p.2) ⬝ᵥ
      (W *ᵥ (fun p : Fin m × Fin n => x p.1 * y p.2))

/-- The negative trace is expressed by its real part; traces of Hermitian products are real. -/
def IsWitness {m n : ℕ} (W : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) : Prop :=
  blockPositive W ∧ ∃ σ : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ,
    σ.PosSemidef ∧ (W * σ).trace.re < 0

/-- Trace out the second factor, using the existing partial-trace definition. -/
def trTwo {m n : ℕ} (W : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) :
    Matrix (Fin m) (Fin m) ℂ := partialTraceRight W

/-- Trace out the first factor, using the existing partial-trace definition. -/
def trOne {m n : ℕ} (W : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ := partialTraceLeft W

local notation "tr₂" => trTwo
local notation "tr₁" => trOne

/-- Schmidt rank is the rank of the coefficient matrix. -/
def schmidtRank {m n : ℕ} (v : Fin m × Fin n → ℂ) : ℕ :=
  (Matrix.of fun i j => v (i, j)).rank

/-- Either dimension-ordered alternative of the kernel criterion. -/
def kernelCriterion {m n : ℕ} (W : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) : Prop :=
  (m ≤ n ∧ ∃ v, (W + tr₂ W ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ)) *ᵥ v = 0 ∧
    schmidtRank v = m) ∨
  (n ≤ m ∧ ∃ v, (W + (1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ tr₁ W) *ᵥ v = 0 ∧
    schmidtRank v = n)

/-- Equal Schmidt coefficients on orthonormal families of size `min m n`. -/
def maximallyEntangled {m n : ℕ} (Ω : Fin m × Fin n → ℂ) : Prop :=
  ∃ (u : Fin (min m n) → (Fin m → ℂ)) (w : Fin (min m n) → (Fin n → ℂ)),
    Orthonormal ℂ (fun j => (WithLp.toLp 2 (u j) : EuclideanSpace ℂ (Fin m))) ∧
    Orthonormal ℂ (fun j => (WithLp.toLp 2 (w j) : EuclideanSpace ℂ (Fin n))) ∧
    Ω = ∑ j, (Real.rpow ((min m n : ℕ) : ℝ) (-(1 / 2 : ℝ)) : ℂ) •
      (fun p : Fin m × Fin n => u j p.1 * w j p.2)

/-- Equality in the source's trace bound. -/
def traceCriterion {m n : ℕ} (W : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) : Prop :=
  ∃ Ω, maximallyEntangled Ω ∧ star Ω ⬝ᵥ (W *ᵥ Ω) = -(W.trace / ((min m n : ℕ) : ℂ))

/-- The proposed equivalence for all finite-dimensional entanglement witnesses. -/
def claim : Prop :=
  ∀ (m n : ℕ) (W : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ),
    IsWitness W → (kernelCriterion W ↔ traceCriterion W)

private def counterexample : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  fun p q => (!![0, 0, 0, -2; 0, 1, 0, 0; 0, 0, 4, 0; -2, 0, 0, 0])
    (finProdFinEquiv p) (finProdFinEquiv q)

private theorem product_expectation (x y : Fin 2 → ℂ) :
    star (fun p : Fin 2 × Fin 2 => x p.1 * y p.2) ⬝ᵥ
      (counterexample *ᵥ (fun p : Fin 2 × Fin 2 => x p.1 * y p.2)) =
    (Complex.normSq (star (x 0) * y 1 - 2 * star (x 1) * y 0) : ℂ) := by
  simp only [counterexample, Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
    Fin.sum_univ_two, Pi.star_apply]
  norm_num [finProdFinEquiv, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons]
  rw [Complex.normSq_eq_conj_mul_self]
  simp only [map_mul, map_sub, map_ofNat, Complex.conj_conj]
  ring

private def bellVector : Fin 2 × Fin 2 → ℂ :=
  fun p => if p.1 = p.2 then (Real.sqrt 2 : ℂ)⁻¹ else 0

private theorem witness : IsWitness counterexample := by
  unfold IsWitness
  refine ⟨?_, vecMulVec bellVector (star bellVector),
    Matrix.posSemidef_vecMulVec_self_star bellVector, ?_⟩
  · unfold blockPositive
    intro x y
    rw [product_expectation, Complex.zero_le_real]
    exact Complex.normSq_nonneg _
  · have hs : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
      norm_cast
      exact Real.sq_sqrt (by norm_num)
    have hz : (Real.sqrt 2 : ℂ) ≠ 0 := by
      exact_mod_cast (ne_of_gt (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)))
    have ht : (counterexample * vecMulVec bellVector (star bellVector)).trace = -2 := by
      simp only [counterexample, bellVector, Matrix.trace, Matrix.diag_apply,
        Matrix.mul_apply, vecMulVec_apply, Pi.star_apply, Fintype.sum_prod_type,
        Fin.sum_univ_two]
      norm_num [finProdFinEquiv, Matrix.cons_val_two, Matrix.cons_val_three,
        Matrix.head_cons, Matrix.tail_cons, Complex.star_def, map_inv₀]
      field_simp
      linear_combination hs
    rw [ht]
    norm_num

private theorem kernel : kernelCriterion counterexample := by
  unfold kernelCriterion
  refine Or.inl ⟨le_rfl, (fun p => (!![2, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℂ)
    p.1 p.2), ?_, ?_⟩
  · ext p
    rcases p with ⟨i, j⟩
    fin_cases i <;> fin_cases j <;>
      simp only [counterexample, trTwo, partialTraceRight, Matrix.mulVec, dotProduct,
        Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.add_apply,
        Matrix.kroneckerMap_apply]
    all_goals norm_num [finProdFinEquiv, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.head_cons, Matrix.tail_cons, Matrix.one_apply]
  · unfold schmidtRank
    change ( (!![2, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℂ)).rank = 2
    apply (Matrix.rank_of_isUnit _ ?_).trans (by simp)
    apply (Matrix.isUnit_iff_isUnit_det _).mpr
    norm_num [Matrix.det_fin_two]

private theorem maximal_unit {Ω : Fin 2 × Fin 2 → ℂ} (hΩ : maximallyEntangled Ω) :
    star Ω ⬝ᵥ Ω = 1 := by
  simp only [maximallyEntangled, min_self] at hΩ
  obtain ⟨u, w, hu, hw, hΩ⟩ := hΩ
  have ui (j k : Fin 2) : star (u j) ⬝ᵥ u k = if j = k then 1 else 0 := by
    rw [dotProduct_comm]
    exact orthonormal_iff_ite.mp hu j k
  have wi (j k : Fin 2) : star (w j) ⬝ᵥ w k = if j = k then 1 else 0 := by
    rw [dotProduct_comm]
    exact orthonormal_iff_ite.mp hw j k
  let t (j : Fin 2) : Fin 2 × Fin 2 → ℂ := fun p => u j p.1 * w j p.2
  have ti (j k : Fin 2) : star (t j) ⬝ᵥ t k = if j = k then 1 else 0 := by
    have he : star (t j) ⬝ᵥ t k = (star (u j) ⬝ᵥ u k) * (star (w j) ⬝ᵥ w k) := by
      simp only [t, dotProduct, Pi.star_apply, star_mul, Fintype.sum_prod_type,
        Finset.sum_mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro l hl
      ring
    rw [he, ui, wi]
    split_ifs <;> norm_num
  have hcR : (2 : ℝ) ^ (-(1 / 2 : ℝ)) * (2 : ℝ) ^ (-(1 / 2 : ℝ)) = 1 / 2 := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    norm_num [Real.rpow_neg_one]
  have hc : (Real.rpow 2 (-(1 / 2 : ℝ)) : ℂ) *
      (Real.rpow 2 (-(1 / 2 : ℝ)) : ℂ) = 1 / 2 := by
    simpa only [Real.rpow_eq_pow, Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_one,
      Complex.ofReal_ofNat] using congrArg Complex.ofReal hcR
  rw [hΩ]
  change star (∑ j : Fin 2, (Real.rpow 2 (-(1 / 2 : ℝ)) : ℂ) • t j) ⬝ᵥ
    (∑ j : Fin 2, (Real.rpow 2 (-(1 / 2 : ℝ)) : ℂ) • t j) = 1
  simp only [Fin.sum_univ_two, star_add, star_smul, add_dotProduct, dotProduct_add,
    smul_dotProduct, dotProduct_smul, smul_eq_mul, ti]
  norm_num only [Complex.star_def, Complex.conj_ofReal, if_pos, if_false,
    Fin.zero_ne_one, one_ne_zero, one_mul, zero_mul, mul_zero, add_zero, zero_add]
  linear_combination 2 * hc

private theorem shifted_expectation (z : Fin 2 × Fin 2 → ℂ) :
    star z ⬝ᵥ ((counterexample + (2 : ℂ) • (1 : Matrix (Fin 2 × Fin 2)
      (Fin 2 × Fin 2) ℂ)) *ᵥ z) =
    ((2 * Complex.normSq (z (0, 0) - z (1, 1)) +
      3 * Complex.normSq (z (0, 1)) + 6 * Complex.normSq (z (1, 0)) : ℝ) : ℂ) := by
  rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    dotProduct_add, dotProduct_smul, smul_eq_mul]
  simp only [counterexample, Matrix.mulVec, dotProduct,
    Fintype.sum_prod_type, Fin.sum_univ_two, Pi.star_apply]
  norm_num [finProdFinEquiv, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons]
  simp only [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_ofNat,
    Complex.normSq_eq_conj_mul_self, Complex.star_def, map_sub]
  ring

private theorem no_trace : ¬ traceCriterion counterexample := by
  unfold traceCriterion
  rintro ⟨Ω, hΩ, he⟩
  have hn := maximal_unit hΩ
  have hp : 0 ≤ (star Ω ⬝ᵥ ((counterexample + (2 : ℂ) •
      (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)) *ᵥ Ω)).re := by
    rw [shifted_expectation]
    simp only [Complex.ofReal_re]
    exact add_nonneg (add_nonneg (mul_nonneg (by norm_num) (Complex.normSq_nonneg _))
      (mul_nonneg (by norm_num) (Complex.normSq_nonneg _)))
      (mul_nonneg (by norm_num) (Complex.normSq_nonneg _))
  have ht : counterexample.trace = 5 := by
    simp only [counterexample, Matrix.trace, Matrix.diag_apply, Fintype.sum_prod_type,
      Fin.sum_univ_two]
    norm_num [finProdFinEquiv, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.head_cons, Matrix.tail_cons]
  rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    dotProduct_add, dotProduct_smul, smul_eq_mul, hn, he, ht] at hp
  norm_num at hp

/-- A two-qubit witness separates the kernel and trace criteria. -/
theorem result : ¬ claim := by
  intro h
  exact no_trace ((h 2 2 counterexample witness).mp kernel)

#print axioms result

end D5.S3.Quantum.Entanglement.WitnessKernelTraceCriteriaRefutation
