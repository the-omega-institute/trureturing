/- GID: D5/S3/Zeros/CriticalPoints/RankOneTraceBound
   generality: G
   mirror-B: D5/B/S3/Zeros/CriticalPoints/RankOneTraceBound
   mirror-E: none(waiver:open-problem-resolution)
   anchors: [mathlib/module/Mathlib.Analysis.InnerProductSpace.PiL2]
   utility: none
   digest: Rank-one trace bounds and phase rigidity for nonorthogonal vectors. -/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.Ring

/-! Finite weighted rank-one sums, with no positivity assumption on the operator. -/

open scoped BigOperators ComplexConjugate
open Matrix

namespace D5.S3.Zeros.CriticalPoints.RankOneTraceBound

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℂ E]

private theorem norm_sum_inner_le (r : ι → E) (a : ι → ℝ) (γ : ι → ℂ)
    (ha : ∀ j, 0 ≤ a j) (hγ : ∀ j, ‖γ j‖ = 1) (V : E →ₗᵢ[ℂ] E) :
    ‖∑ j, (a j : ℂ) * γ j * inner ℂ (r j) (V (r j))‖ ≤
      ∑ j, a j * ‖r j‖ ^ 2 := by
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  simp only [norm_mul, Complex.norm_real, Real.norm_of_nonneg (ha j), hγ j,
    mul_one]
  calc
    a j * ‖inner ℂ (r j) (V (r j))‖ ≤ a j * (‖r j‖ * ‖V (r j)‖) :=
      mul_le_mul_of_nonneg_left (norm_inner_le_norm _ _) (ha j)
    _ = a j * ‖r j‖ ^ 2 := by rw [V.norm_map, pow_two]

private theorem phases_eq_of_norm_sum_inner_eq (r : ι → E) (a : ι → ℝ)
    (γ : ι → ℂ) (ha : ∀ j, 0 < a j) (hγ : ∀ j, ‖γ j‖ = 1)
    (V : E →ₗᵢ[ℂ] E) (hr : ∀ i j, inner ℂ (r i) (r j) ≠ 0)
    (heq : ‖∑ j, (a j : ℂ) * γ j * inner ℂ (r j) (V (r j))‖ =
      ∑ j, a j * ‖r j‖ ^ 2) : ∀ i j, γ i = γ j := by
  classical
  let S : ℂ := ∑ j, (a j : ℂ) * γ j * inner ℂ (r j) (V (r j))
  obtain ⟨α, hα, hS⟩ := Complex.exists_norm_eq_mul_self S
  have hαγ (j : ι) : ‖α * γ j‖ = 1 := by rw [norm_mul, hα, hγ, one_mul]
  have hbound (j : ι) :
      ((α * γ j) * inner ℂ (r j) (V (r j))).re ≤ ‖r j‖ ^ 2 := by
    calc
      _ ≤ ‖(α * γ j) * inner ℂ (r j) (V (r j))‖ := Complex.re_le_norm _
      _ = ‖inner ℂ (r j) (V (r j))‖ := by rw [norm_mul, hαγ, one_mul]
      _ ≤ ‖r j‖ * ‖V (r j)‖ := norm_inner_le_norm _ _
      _ = ‖r j‖ ^ 2 := by rw [V.norm_map, pow_two]
  have hsum :
      ∑ j, a j * ((α * γ j) * inner ℂ (r j) (V (r j))).re =
        ∑ j, a j * ‖r j‖ ^ 2 := by
    have hmul : α * S =
        ∑ j, (a j : ℂ) * ((α * γ j) * inner ℂ (r j) (V (r j))) := by
      dsimp [S]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    have hreal := congrArg Complex.re (hS.trans hmul)
    simpa only [Complex.ofReal_re, Complex.re_sum, Complex.re_ofReal_mul] using
      hreal.symm.trans heq
  have hterm (j : ι) :
      ((α * γ j) * inner ℂ (r j) (V (r j))).re = ‖r j‖ ^ 2 := by
    have h := (Finset.sum_eq_sum_iff_of_le
      (fun k (_ : k ∈ (Finset.univ : Finset ι)) =>
        mul_le_mul_of_nonneg_left (hbound k) (ha k).le)).mp hsum j (Finset.mem_univ j)
    exact (mul_left_cancel₀ (ha j).ne' h)
  have hvec (j : ι) : (α * γ j) • V (r j) = r j := by
    apply eq_of_norm_le_re_inner_eq_norm_sq (𝕜 := ℂ)
    · simp only [norm_smul, hαγ, V.norm_map, one_mul, le_refl]
    · rw [← inner_re_symm, inner_smul_right]
      exact hterm j
  intro i j
  have hmul : star (α * γ i) * (α * γ j) = 1 := by
    have h : inner ℂ ((α * γ i) • V (r i)) ((α * γ j) • V (r j)) =
        inner ℂ (r i) (r j) := by rw [hvec i, hvec j]
    simp only [inner_smul_left, inner_smul_right, V.inner_map_map] at h
    apply mul_right_cancel₀ (hr i j)
    simp only [Complex.star_def]
    convert h using 1 <;> ring
  have hself : star (α * γ i) * (α * γ i) = 1 := by
    simpa only [Complex.star_def, hαγ, Complex.ofReal_one, one_pow] using
      Complex.conj_mul' (α * γ i)
  have hα0 : α ≠ 0 := by intro h; simp [h] at hα
  have hstar0 : star (α * γ i) ≠ 0 := by
    intro h
    rw [h, zero_mul] at hself
    exact zero_ne_one hself
  exact mul_left_cancel₀ hα0 (mul_left_cancel₀ hstar0 (hself.trans hmul.symm))

section Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

private noncomputable def unitary_isometry (V : Matrix n n ℂ)
    (hV : V ∈ Matrix.unitaryGroup n ℂ) :
    EuclideanSpace ℂ n →ₗᵢ[ℂ] EuclideanSpace ℂ n :=
  V.toEuclideanLin.isometryOfInner fun x y => by
    have hVV : Vᴴ * V = 1 := by
      simpa only [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff'.mp hV
    rw [EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.inner_eq_star_dotProduct]
    change (V *ᵥ y.ofLp) ⬝ᵥ star (V *ᵥ x.ofLp) = y.ofLp ⬝ᵥ star x.ofLp
    rw [dotProduct_comm, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec,
      Matrix.mulVec_mulVec, hVV, Matrix.one_mulVec,
      dotProduct_comm]

private theorem trace_rank_one_sum (r : ι → EuclideanSpace ℂ n) (a : ι → ℝ)
    (γ : ι → ℂ) (V : Matrix n n ℂ) :
    Matrix.trace (V * ∑ j, ((a j : ℂ) * γ j) •
      Matrix.vecMulVec (r j).ofLp (star (r j).ofLp)) =
        ∑ j, (a j : ℂ) * γ j * inner ℂ (r j) (V.toEuclideanLin (r j)) := by
  simp only [Matrix.mul_sum, Matrix.trace_sum, Matrix.mul_smul, Matrix.trace_smul,
    Matrix.mul_vecMulVec, Matrix.trace_vecMulVec, smul_eq_mul,
    EuclideanSpace.inner_eq_star_dotProduct]
  rfl

/-- The unitary trace bound for finite sums of complex rank-one operators. -/
theorem norm_trace_rank_one_sum_le (r : ι → EuclideanSpace ℂ n) (a : ι → ℝ)
    (γ : ι → ℂ) (ha : ∀ j, 0 ≤ a j) (hγ : ∀ j, ‖γ j‖ = 1)
    (V : Matrix n n ℂ) (hV : V ∈ Matrix.unitaryGroup n ℂ) :
    ‖Matrix.trace (V * ∑ j, ((a j : ℂ) * γ j) •
      Matrix.vecMulVec (r j).ofLp (star (r j).ofLp))‖ ≤
        ∑ j, a j * ‖r j‖ ^ 2 := by
  rw [trace_rank_one_sum]
  exact norm_sum_inner_le r a γ ha hγ (unitary_isometry V hV)

/-- Nonzero pairwise inner products force a common phase whenever the trace bound is sharp. -/
theorem phases_eq_of_norm_trace_rank_one_sum_eq (r : ι → EuclideanSpace ℂ n)
    (a : ι → ℝ) (γ : ι → ℂ) (ha : ∀ j, 0 < a j) (hγ : ∀ j, ‖γ j‖ = 1)
    (V : Matrix n n ℂ) (hV : V ∈ Matrix.unitaryGroup n ℂ)
    (hr : ∀ i j, inner ℂ (r i) (r j) ≠ 0)
    (heq : ‖Matrix.trace (V * ∑ j, ((a j : ℂ) * γ j) •
      Matrix.vecMulVec (r j).ofLp (star (r j).ofLp))‖ =
        ∑ j, a j * ‖r j‖ ^ 2) : ∀ i j, γ i = γ j := by
  rw [trace_rank_one_sum] at heq
  exact phases_eq_of_norm_sum_inner_eq r a γ ha hγ (unitary_isometry V hV) hr heq

end Matrix

end D5.S3.Zeros.CriticalPoints.RankOneTraceBound
