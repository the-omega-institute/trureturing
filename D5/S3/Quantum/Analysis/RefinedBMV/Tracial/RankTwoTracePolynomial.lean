/- GID: D5/S3/Quantum/Analysis/RefinedBMV/Tracial/RankTwoTracePolynomial
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Nonnegative spectral trace polynomial for a signed rank-two compression. -/

import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Basic.Complex.BigOperators
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-! Trace powers of a signed two-column compression and their spectral coefficients. -/

namespace RefinedBMV.Tracial

open Matrix MvPolynomial
open scoped BigOperators

/-- The trace recurrence with trace parameter `t` and negative determinant parameter `d`. -/
def tracePowerPolynomial {R : Type*} [CommSemiring R] (t d : R) : ℕ → R
  | 0 => 2
  | 1 => t
  | n + 2 => t * tracePowerPolynomial t d (n + 1) + d * tracePowerPolynomial t d n

private theorem tracePowerPolynomial_map {R S : Type*} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (t d : R) :
    ∀ n, f (tracePowerPolynomial t d n) = tracePowerPolynomial (f t) (f d) n
  | 0 => map_ofNat f 2
  | 1 => rfl
  | n + 2 => by
    simp only [tracePowerPolynomial, map_add, map_mul, tracePowerPolynomial_map f t d n,
      tracePowerPolynomial_map f t d (n + 1)]

/-- Reflecting the trace parameter preserves even powers and reverses odd powers. -/
theorem tracePowerPolynomial_neg_left {R : Type*} [CommRing R] (t d : R) :
    ∀ n, tracePowerPolynomial (-t) d n = (-1) ^ n * tracePowerPolynomial t d n
  | 0 => by simp [tracePowerPolynomial]
  | 1 => by simp [tracePowerPolynomial]
  | n + 2 => by
    simp only [tracePowerPolynomial, tracePowerPolynomial_neg_left t d n,
      tracePowerPolynomial_neg_left t d (n + 1), pow_add, pow_one]
    ring

private theorem finTwo_square {R : Type*} [CommRing R] (M : Matrix (Fin 2) (Fin 2) R) :
    M ^ 2 = M.trace • M - M.det • 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_two, mul_apply, Fin.sum_univ_two, trace_fin_two, det_fin_two] <;>
    ring

/-- Cayley–Hamilton determines all trace powers of a two-dimensional matrix. -/
theorem trace_finTwo_pow {R : Type*} [CommRing R] (M : Matrix (Fin 2) (Fin 2) R) :
    ∀ n, (M ^ n).trace = tracePowerPolynomial M.trace (-M.det) n
  | 0 => by simp [tracePowerPolynomial]
  | 1 => by simp [tracePowerPolynomial]
  | n + 2 => by
    have h : (M ^ (n + 2)).trace = M.trace * (M ^ (n + 1)).trace - M.det * (M ^ n).trace := by
      rw [pow_add, finTwo_square, mul_sub, Matrix.mul_smul, Matrix.mul_smul, mul_one,
        trace_sub, trace_smul, trace_smul, ← pow_succ]
      rfl
    rw [h, trace_finTwo_pow M (n + 1), trace_finTwo_pow M n]
    simp [tracePowerPolynomial, sub_eq_add_neg]

/-- The fourth trace power in trace and determinant coordinates. -/
theorem trace_finTwo_fourth {R : Type*} [CommRing R] (M : Matrix (Fin 2) (Fin 2) R) :
    (M ^ 4).trace = M.trace ^ 4 - 4 * M.trace ^ 2 * M.det + 2 * M.det ^ 2 := by
  rw [trace_finTwo_pow]
  norm_num [tracePowerPolynomial]
  ring

private theorem rectPow {R ι κ : Type*} [CommSemiring R] [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (X : Matrix ι κ R) (Y : Matrix κ ι R) (n : ℕ) :
    (X * Y) ^ (n + 1) = X * (Y * X) ^ n * Y := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ' (X * Y), ih, pow_succ' (Y * X)]
    simp only [Matrix.mul_assoc]

/-- Positive trace powers pass between the two products of rectangular factors. -/
theorem trace_rectangular_pow {R ι κ : Type*} [CommSemiring R] [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (X : Matrix ι κ R) (Y : Matrix κ ι R) (n : ℕ) :
    ((X * Y) ^ (n + 1)).trace = ((Y * X) ^ (n + 1)).trace := by
  rw [rectPow X Y, Matrix.mul_assoc, trace_mul_comm X, Matrix.mul_assoc, ← pow_succ]

private def signature : Matrix (Fin 2) (Fin 2) ℂ :=
  diagonal fun i ↦ if i = 0 then 1 else -1

private theorem signature_det : signature.det = -1 := by
  norm_num [signature, det_fin_two]

section Compression

variable {ι σ : Type*} [Fintype ι] [DecidableEq ι]

private def weightedGram (V : Matrix ι (Fin 2) ℂ) (x : ι → ℝ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  Vᴴ * diagonal (fun i ↦ (x i : ℂ)) * V

private theorem weightedGram_apply (V : Matrix ι (Fin 2) ℂ) (x : ι → ℝ) (r s : Fin 2) :
    weightedGram V x r s = ∑ i, (x i : ℂ) * (star (V i r) * V i s) := by
  rw [weightedGram, Matrix.mul_assoc, mul_apply]
  simp only [diagonal_mul, conjTranspose_apply]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The trace contribution at a spectral coordinate is the two-column signed mass. -/
def signedRowMass (V : Matrix ι (Fin 2) ℂ) (i : ι) : ℝ :=
  Complex.normSq (V i 0) - Complex.normSq (V i 1)

/-- Half the squared two-row minor. The two orderings count the same determinant term. -/
noncomputable def rowMinorMass (V : Matrix ι (Fin 2) ℂ) (i j : ι) : ℝ :=
  Complex.normSq (V i 0 * V j 1 - V i 1 * V j 0) / 2

private theorem weightedGram_trace (V : Matrix ι (Fin 2) ℂ) (x : ι → ℝ) :
    ((weightedGram V x) * signature).trace = ((∑ i, signedRowMass V i * x i : ℝ) : ℂ) := by
  simp only [signature, trace_fin_two, mul_diagonal]
  norm_num
  rw [weightedGram_apply, weightedGram_apply, ← sub_eq_add_neg, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [signedRowMass, Complex.ofReal_sub, Complex.normSq_eq_conj_mul_self]
  change _ = (star (V i 0) * V i 0 - star (V i 1) * V i 1) * _
  ring

private theorem weightedGram_det (V : Matrix ι (Fin 2) ℂ) (x : ι → ℝ) :
    (weightedGram V x).det = ((∑ i, ∑ j, rowMinorMass V i j * x i * x j : ℝ) : ℂ) := by
  let q (i j : ι) : ℂ :=
    (x i : ℂ) * (star (V i 0) * V i 0) * ((x j : ℂ) * (star (V j 1) * V j 1)) -
      (x i : ℂ) * (star (V i 0) * V i 1) * ((x j : ℂ) * (star (V j 1) * V j 0))
  have hswap : (∑ i, ∑ j, q j i) = ∑ i, ∑ j, q i j := Finset.sum_comm
  calc
    (weightedGram V x).det = ∑ i, ∑ j, q i j := by
      simp only [det_fin_two, weightedGram_apply, Finset.sum_mul, Finset.mul_sum,
        ← Finset.sum_sub_distrib, q]
      exact hswap
    _ = (∑ i, ∑ j, (q i j + q j i) / 2) := by
      simp only [div_eq_mul_inv, ← Finset.sum_mul, Finset.sum_add_distrib, hswap]
      ring
    _ = ((∑ i, ∑ j, rowMinorMass V i j * x i * x j : ℝ) : ℂ) := by
      push_cast
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      simp only [q, rowMinorMass, Complex.ofReal_div,
        Complex.ofReal_ofNat, Complex.normSq_eq_conj_mul_self]
      change _ = (star (V i 0 * V j 1 - V i 1 * V j 0) *
        (V i 0 * V j 1 - V i 1 * V j 0)) / 2 * _ * _
      simp only [star_sub, star_mul]
      ring

/-- The matrix with one positive and one negative column weight. -/
def signedRankTwo (V : Matrix ι (Fin 2) ℂ) : Matrix ι ι ℂ :=
  V * signature * Vᴴ

/-- Compress a positive trace power to two dimensions and evaluate the minor formula. -/
theorem signedRankTwo_trace_pow (V : Matrix ι (Fin 2) ℂ) (x : ι → ℝ) (n : ℕ) :
    (((diagonal fun i ↦ (x i : ℂ)) * signedRankTwo V) ^ (n + 1)).trace =
      ((tracePowerPolynomial (∑ i, signedRowMass V i * x i)
        (∑ i, ∑ j, rowMinorMass V i j * x i * x j) (n + 1) : ℝ) : ℂ) := by
  let X := (diagonal fun i ↦ (x i : ℂ)) * V * signature
  have hX : X * Vᴴ = (diagonal fun i ↦ (x i : ℂ)) * signedRankTwo V := by
    simp only [X, signedRankTwo, Matrix.mul_assoc]
  have hY : Vᴴ * X = weightedGram V x * signature := by
    simp only [X, weightedGram, Matrix.mul_assoc]
  rw [← hX, trace_rectangular_pow, hY, trace_finTwo_pow, weightedGram_trace, det_mul,
    signature_det, mul_neg_one, neg_neg, weightedGram_det]
  exact (tracePowerPolynomial_map Complex.ofRealHom _ _ (n + 1)).symm

/-- The grouped linear coefficient is the trace against the spectral projection. -/
theorem signedRankTwoTrace_block_trace [DecidableEq σ]
    (V : Matrix ι (Fin 2) ℂ) (label : ι → σ) (s : σ) :
    (diagonal (fun i ↦ if label i = s then 1 else 0) * signedRankTwo V).trace =
      ((∑ i ∈ Finset.univ.filter (fun i ↦ label i = s), signedRowMass V i : ℝ) : ℂ) := by
  simpa [tracePowerPolynomial, Finset.sum_filter, mul_ite, apply_ite] using
    (signedRankTwo_trace_pow V (fun i ↦ if label i = s then 1 else 0) 0)

/-- The linear trace polynomial, with equal spectral coordinates grouped. -/
noncomputable def signedRankTwoTraceLinear [Fintype σ] [DecidableEq σ]
    (V : Matrix ι (Fin 2) ℂ) (label : ι → σ) : MvPolynomial σ ℝ :=
  ∑ s, C (∑ i ∈ Finset.univ.filter (fun i ↦ label i = s), signedRowMass V i) * X s

/-- The negative determinant polynomial expressed as squared minors. -/
noncomputable def signedRankTwoTraceQuadratic
    (V : Matrix ι (Fin 2) ℂ) (label : ι → σ) : MvPolynomial σ ℝ :=
  ∑ i, ∑ j, C (rowMinorMass V i j) * X (label i) * X (label j)

private theorem coeff_mul_nonneg {P Q : MvPolynomial σ ℝ}
    (hP : ∀ m, 0 ≤ P.coeff m) (hQ : ∀ m, 0 ≤ Q.coeff m) (m : σ →₀ ℕ) :
    0 ≤ (P * Q).coeff m := by
  classical
  rw [coeff_mul]
  exact Finset.sum_nonneg fun _ _ ↦ mul_nonneg (hP _) (hQ _)

private theorem coeff_X_nonneg (s : σ) (m : σ →₀ ℕ) :
    0 ≤ (X s : MvPolynomial σ ℝ).coeff m := by
  classical
  rw [coeff_X]
  split <;> norm_num

private theorem coeff_tracePowerPolynomial_nonneg (P Q : MvPolynomial σ ℝ)
    (hP : ∀ m, 0 ≤ P.coeff m) (hQ : ∀ m, 0 ≤ Q.coeff m) :
    ∀ n m, 0 ≤ (tracePowerPolynomial P Q n).coeff m
  | 0, m => by
    classical
    simp only [tracePowerPolynomial, ← map_ofNat C, coeff_C]
    split <;> norm_num
  | 1, m => hP m
  | n + 2, m => by
    change 0 ≤ (coeffAddMonoidHom m)
      (P * tracePowerPolynomial P Q (n + 1) + Q * tracePowerPolynomial P Q n)
    rw [map_add]
    exact add_nonneg
      (coeff_mul_nonneg hP (coeff_tracePowerPolynomial_nonneg P Q hP hQ (n + 1)) m)
      (coeff_mul_nonneg hQ (coeff_tracePowerPolynomial_nonneg P Q hP hQ n) m)

omit [DecidableEq ι] in
private theorem coeff_quadratic_nonneg (V : Matrix ι (Fin 2) ℂ) (label : ι → σ)
    (d : σ →₀ ℕ) : 0 ≤ (signedRankTwoTraceQuadratic V label).coeff d := by
  simp only [signedRankTwoTraceQuadratic, coeff_sum]
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  exact coeff_mul_nonneg (fun u ↦ by
    rw [coeff_C_mul]
    exact mul_nonneg (div_nonneg (Complex.normSq_nonneg _) (by norm_num))
      (coeff_X_nonneg _ u)) (coeff_X_nonneg _) d

omit [DecidableEq ι] in
/-- Nonnegative spectral block traces give a polynomial with nonnegative coefficients. -/
theorem signedRankTwoTrace_coeff_nonneg [Fintype σ] [DecidableEq σ]
    (V : Matrix ι (Fin 2) ℂ) (label : ι → σ)
    (h : ∀ s, 0 ≤ ∑ i ∈ Finset.univ.filter (fun i ↦ label i = s), signedRowMass V i)
    (n : ℕ) (m : σ →₀ ℕ) :
    0 ≤ (tracePowerPolynomial (signedRankTwoTraceLinear V label)
      (signedRankTwoTraceQuadratic V label) n).coeff m := by
  apply coeff_tracePowerPolynomial_nonneg
  · intro d
    simp only [signedRankTwoTraceLinear, coeff_sum, coeff_C_mul]
    exact Finset.sum_nonneg fun s _ ↦ mul_nonneg (h s) (coeff_X_nonneg s d)
  · exact coeff_quadratic_nonneg V label

/-- The positive-coefficient polynomial evaluates to the actual weighted trace power. -/
theorem signedRankTwoTrace_eval [Fintype σ] [DecidableEq σ]
    (V : Matrix ι (Fin 2) ℂ) (label : ι → σ) (z : σ → ℝ) (n : ℕ) :
    (((diagonal fun i ↦ (z (label i) : ℂ)) * signedRankTwo V) ^ (n + 1)).trace =
      ((eval z (tracePowerPolynomial (signedRankTwoTraceLinear V label)
        (signedRankTwoTraceQuadratic V label) (n + 1)) : ℝ) : ℂ) := by
  rw [tracePowerPolynomial_map, signedRankTwo_trace_pow]
  congr 2
  · simp only [signedRankTwoTraceLinear, map_sum, map_mul, eval_C, eval_X, Finset.sum_mul]
    rw [← Finset.sum_fiberwise Finset.univ label (fun i ↦ signedRowMass V i * z (label i))]
    apply Finset.sum_congr rfl
    intro s _
    apply Finset.sum_congr rfl
    intro i hi
    rw [(Finset.mem_filter.mp hi).2]
  · simp only [signedRankTwoTraceQuadratic, map_sum, map_mul, eval_C, eval_X]

/-- Uniformly nonpositive spectral traces also give a nonnegative coefficient
representation in every positive even degree. -/
theorem signedRankTwoTrace_even_nonpos_eval [Finite σ] [DecidableEq σ]
    (V : Matrix ι (Fin 2) ℂ) (label : ι → σ)
    (h : ∀ s, (∑ i ∈ Finset.univ.filter (fun i ↦ label i = s), signedRowMass V i) ≤ 0)
    (n : ℕ) (hn : Even (n + 1)) :
    ∃ P : MvPolynomial σ ℝ, (∀ m, 0 ≤ P.coeff m) ∧ ∀ z : σ → ℝ,
      (((diagonal fun i ↦ (z (label i) : ℂ)) * signedRankTwo V) ^ (n + 1)).trace =
        ((eval z P : ℝ) : ℂ) := by
  let _ := Fintype.ofFinite σ
  let L := signedRankTwoTraceLinear V label
  let Q := signedRankTwoTraceQuadratic V label
  refine ⟨tracePowerPolynomial (-L) Q (n + 1), ?_, ?_⟩
  · apply coeff_tracePowerPolynomial_nonneg
    · intro m
      change 0 ≤ (coeffAddMonoidHom m) (-L)
      rw [map_neg, neg_nonneg]
      simp only [L, signedRankTwoTraceLinear, coeffAddMonoidHom_apply, coeff_sum, coeff_C_mul]
      exact Finset.sum_nonpos fun s _ ↦ mul_nonpos_of_nonpos_of_nonneg (h s) (coeff_X_nonneg s m)
    · exact coeff_quadratic_nonneg V label
  · intro z
    rw [tracePowerPolynomial_neg_left, hn.neg_one_pow, one_mul]
    exact signedRankTwoTrace_eval V label z n

end Compression

end RefinedBMV.Tracial
