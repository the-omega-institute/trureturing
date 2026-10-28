/- GID: D5/S3/QuadraticForms/BarczyPalesJensenConverse
   generality: S
   mirror-B: D5/B/S3/QuadraticForms/BarczyPalesJensenConverse
   mirror-E: none(waiver:probe-only)
   anchors: []
   utility: none
   digest: A signed quadratic norm counterexample to the rank-only Jensen converse. -/

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Analysis.Convex.DoublyStochasticMatrix
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Real.Sqrt
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic

/-
The original target is Barczy–Páles, arXiv:2510.03715v1, Remark 2.2(i),
equation (2.1) and Definition 1.1. Admission: external open problem #23083.
The subject is an indefinite rational quadratic form transported to the reals.
The quadratic field, its genuine scalar action and linear splitting are upstream.
The new content is finite norm cancellation and its full quantified application.
-/

noncomputable section
open scoped BigOperators
open Matrix

namespace BarczyPalesJensenConverse

private instance nonsquare : Fact (¬ IsSquare (3 : ℚ)) := by
  constructor
  rw [Rat.isSquare_natCast_iff]
  norm_num

private abbrev K := QuadraticAlgebra ℚ 3 0

private def embedding : K →ₐ[ℚ] ℝ :=
  QuadraticAlgebra.lift ⟨Real.sqrt 3, by
    simpa [Algebra.smul_def, pow_two] using Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)⟩

private instance realAlgebra : Algebra K ℝ := embedding.toRingHom.toAlgebra

private def projection : ℝ →ₗ[K] K := (Algebra.linearMap K ℝ).leftInverse

private theorem projection_embedding (z : K) : projection (embedding z) = z := by
  exact LinearMap.leftInverse_apply_of_inj
    (LinearMap.ker_eq_bot.mpr (algebraMap K ℝ).injective) z

private theorem projection_scalar (c : K) (x : ℝ) :
    projection (embedding c * x) = c * projection x := by
  exact projection.map_smul c x

private def omega : K := ⟨0, 1⟩

private theorem embedding_omega : embedding omega = Real.sqrt 3 := by
  simp [embedding, QuadraticAlgebra.lift, omega, Algebra.smul_def]

private def counterFunction (x : ℝ) : ℝ := (QuadraticAlgebra.norm (projection x) : ℚ)

private theorem norm_cancellation (a b : K) :
    QuadraticAlgebra.norm (a + b) +
      QuadraticAlgebra.norm (a + (omega - 2) * b) +
      QuadraticAlgebra.norm (a + (1 - omega) * b) =
      3 * QuadraticAlgebra.norm a := by
  simp [QuadraticAlgebra.norm_def, omega, QuadraticAlgebra.re_mul,
    QuadraticAlgebra.im_mul]
  <;> ring

private def counterMatrix : Matrix (Fin 3) (Fin 3) ℝ :=
  !![5/12, 3/12, 4/12;
     (Real.sqrt 3+2)/12, (6-Real.sqrt 3)/12, 4/12;
     (5-Real.sqrt 3)/12, (3+Real.sqrt 3)/12, 4/12]

private theorem sqrt_bounds : 1 < Real.sqrt 3 ∧ Real.sqrt 3 < 2 := by
  have h := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)
  have h0 := Real.sqrt_nonneg (3:ℝ)
  constructor <;> nlinarith

private theorem matrix_stochastic : counterMatrix ∈ doublyStochastic ℝ (Fin 3) := by
  rw [mem_doublyStochastic_iff_sum]
  obtain ⟨h1,h2⟩ := sqrt_bounds
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    fin_cases i <;> fin_cases j <;> norm_num [counterMatrix] <;> linarith
  · intro i
    fin_cases i <;> simp [counterMatrix, Fin.sum_univ_succ] <;> ring
  · intro j
    fin_cases j <;> simp [counterMatrix, Fin.sum_univ_succ] <;> ring

private theorem matrix_rank : 2 ≤ counterMatrix.rank := by
  let e : Fin 2 → Fin 3 := fun i => ⟨i.val, by omega⟩
  have hdet : (counterMatrix.submatrix e e).det ≠ 0 := by
    obtain ⟨h1,h2⟩ := sqrt_bounds
    simp [Matrix.det_fin_two, Matrix.submatrix, counterMatrix, e]
    nlinarith
  have hr := Matrix.rank_of_det_ne_zero hdet
  have hl := Matrix.rank_submatrix_le counterMatrix e e
  simpa [hr] using hl

end BarczyPalesJensenConverse
