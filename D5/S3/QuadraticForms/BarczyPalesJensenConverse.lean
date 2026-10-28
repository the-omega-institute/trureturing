/- GID: D5/S3/QuadraticForms/BarczyPalesJensenConverse
   generality: I
   mirror-B: D5/B/S3/QuadraticForms/BarczyPalesJensenConverse
   mirror-E: none(waiver:noncomputable-witness)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/QuadraticForms/BarczyPalesJensenConverse.claim; result=D5/S3/QuadraticForms/BarczyPalesJensenConverse.result; claim=D5/S3/QuadraticForms/BarczyPalesJensenConverse.claim
   digest: A signed quadratic norm counterexample to the rank-only Jensen converse. -/

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Analysis.Convex.DoublyStochasticMatrix
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Real.Sqrt
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic

/-!
The original target is Barczy–Páles, arXiv:2510.03715v1, Remark 2.2(i),
equation (2.1) and Definition 1.1. Admission: external open problem #23083.
The subject is an indefinite rational quadratic form transported to the reals.
The quadratic field, its genuine scalar action and linear splitting are upstream.
The witness composition uses finite norm cancellation in the full quantified application.

Per-declaration proof shape: bind-only; escape_witness: none.
Admission_basis: open-problem-resolution (#23083); result is the full external
question's negation. Algebraic normalization and upstream existence theorems
are not claimed as new general mathematics. All support declarations are consumed:
  nonsquare -> realAlgebra, projection;
  K -> embedding, projection, omega, norm_cancellation;
  embedding -> realAlgebra, projection_embedding, projection_scalar, embedding_omega;
  realAlgebra -> projection, projection_embedding, projection_scalar;
  projection -> counterFunction, projection_embedding, projection_scalar;
  projection_embedding -> midpoint_failure;
  projection_scalar -> all_input_identity;
  omega -> embedding_omega, norm_cancellation, midpoint_failure;
  embedding_omega -> all_input_identity, midpoint_failure;
  counterFunction -> all_input_identity, midpoint_failure, result;
  norm_cancellation -> all_input_identity;
  counterMatrix -> matrix_stochastic, matrix_rank, all_input_identity, result;
  sqrt_bounds -> matrix_stochastic, matrix_rank;
  matrix_stochastic, matrix_rank, all_input_identity, midpoint_failure -> result;
  intervalCombination -> intervalMean, intervalRow;
  intervalMean, intervalRow -> claim, result;
  claim -> result.
There are no direct frozen D5 dependencies. Public inventory: claim, result.
-/

noncomputable section
open scoped BigOperators QuadraticAlgebra
open Matrix

namespace D5.S3.QuadraticForms.BarczyPalesJensenConverse

private instance nonsquare : Fact (¬ IsSquare (3 : ℚ)) := by
  refine ⟨?_⟩
  intro h
  exact Nat.prime_three.not_isSquare ((Rat.isSquare_natCast_iff (n := 3)).mp h)

private def embedding : QuadraticAlgebra ℚ 3 0 →ₐ[ℚ] ℝ :=
  QuadraticAlgebra.lift ⟨Real.sqrt 3, by
    simp [Algebra.smul_def, pow_two]⟩

private instance realAlgebra : Algebra (QuadraticAlgebra ℚ 3 0) ℝ := embedding.toRingHom.toAlgebra

private def projection : ℝ →ₗ[QuadraticAlgebra ℚ 3 0] (QuadraticAlgebra ℚ 3 0) :=
  (Algebra.linearMap (QuadraticAlgebra ℚ 3 0) ℝ).leftInverse

private theorem projection_embedding (z : QuadraticAlgebra ℚ 3 0) : projection (embedding z) = z := by
  exact LinearMap.leftInverse_apply_of_inj
    (LinearMap.ker_eq_bot.mpr (algebraMap (QuadraticAlgebra ℚ 3 0) ℝ).injective) z

private theorem projection_scalar (c : QuadraticAlgebra ℚ 3 0) (x : ℝ) :
    projection (embedding c * x) = c * projection x := by
  exact projection.map_smul c x

private def omega : QuadraticAlgebra ℚ 3 0 := ⟨0, 1⟩

private theorem embedding_omega : embedding omega = Real.sqrt 3 := by
  simp [embedding, QuadraticAlgebra.lift, omega, Algebra.smul_def]

private def counterFunction (x : ℝ) : ℝ := (QuadraticAlgebra.norm (projection x) : ℚ)

private theorem norm_cancellation (a b : QuadraticAlgebra ℚ 3 0) :
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

private theorem all_input_identity (x : Fin 3 → ℝ) :
    ∑ i, counterFunction ((counterMatrix *ᵥ x) i) =
      3 * counterFunction ((∑ j, x j) / 3) := by
  let m := (∑ j, x j) / 3
  let t := (x 0 - x 1) / 12
  have hrow : counterMatrix *ᵥ x =
      ![m + t, m + (Real.sqrt 3 - 2) * t, m + (1 - Real.sqrt 3) * t] := by
    ext i
    fin_cases i <;> simp [counterMatrix, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, m, t] <;> ring
  have htwo : embedding (omega - 2) = Real.sqrt 3 - 2 := by
    simp [embedding_omega, map_ofNat]
  have hthree : embedding (1 - omega) = 1 - Real.sqrt 3 := by
    simp [embedding_omega, map_ofNat]
  change (∑ i, counterFunction ((counterMatrix *ᵥ x) i)) = 3 * counterFunction m
  rw [hrow]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, counterFunction, map_add]
  rw [← htwo, ← hthree, projection_scalar, projection_scalar]
  have hc := congrArg (fun q : ℚ => (q : ℝ))
    (norm_cancellation (projection m) (projection t))
  push_cast at hc
  exact hc

private theorem midpoint_failure :
    ¬ counterFunction ((Real.sqrt 3 + -Real.sqrt 3) / 2) ≤
      (counterFunction (Real.sqrt 3) + counterFunction (-Real.sqrt 3)) / 2 := by
  have hroot : projection (Real.sqrt 3) = omega := by
    rw [← embedding_omega, projection_embedding]
  norm_num [counterFunction, map_neg, hroot, QuadraticAlgebra.norm_def, omega]

/-- A finite convex combination in the original interval subtype. -/
private def intervalCombination {I : Set ℝ} (hI : Convex ℝ I) {n : ℕ}
    (w : Fin n → ℝ) (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1)
    (x : Fin n → I) : I :=
  ⟨∑ i, w i * (x i : ℝ), by
    simpa only [smul_eq_mul] using hI.sum_mem
      (fun i _ => hw0 i) hw1 (fun i _ => (x i).property)⟩

/-- The arithmetic mean, with membership proved in the original interval. -/
private def intervalMean {I : Set ℝ} (hI : Convex ℝ I) {n : ℕ} (hn : 0 < n)
    (x : Fin n → I) : I :=
  intervalCombination hI (fun _ => (n : ℝ)⁻¹)
    (fun _ => inv_nonneg.mpr (Nat.cast_nonneg n))
    (by simp [ne_of_gt hn]) x

/-- An actual matrix row output in the original interval. -/
private def intervalRow {I : Set ℝ} (hI : Convex ℝ I) {n : ℕ}
    (P : Matrix (Fin n) (Fin n) ℝ) (hP : P ∈ doublyStochastic ℝ (Fin n))
    (x : Fin n → I) (i : Fin n) : I :=
  intervalCombination hI (P i)
    (fun j => (mem_doublyStochastic_iff_sum.mp hP).1 i j)
    ((mem_doublyStochastic_iff_sum.mp hP).2.1 i) x

/-- The original universal rank-only converse, with arbitrary subtype functions.
Nonempty open convex subsets of the real line are exactly the intervals in scope.
No regularity of the function or former column-span assumption is imposed. -/
def claim : Prop :=
  ∀ (n : ℕ) (hn : 0 < n) (I : Set ℝ), I.Nonempty → IsOpen I →
    ∀ (hI : Convex ℝ I) (f : I → ℝ)
      (P : Matrix (Fin n) (Fin n) ℝ) (hP : P ∈ doublyStochastic ℝ (Fin n)),
      2 ≤ P.rank →
      (∀ x : Fin n → I,
        f (intervalMean hI hn x) ≤ (∑ i, f (intervalRow hI P hP x i)) / n) →
      ∀ u v : I,
        f (intervalMean hI (by norm_num : 0 < 2) ![u, v]) ≤ (f u + f v) / 2

theorem result : ¬ claim := by
  intro h
  let f : ↥(Set.univ : Set ℝ) → ℝ := fun x => counterFunction x
  have hj := h 3 (by norm_num) Set.univ Set.univ_nonempty isOpen_univ
    convex_univ f counterMatrix matrix_stochastic matrix_rank
  have hi : ∀ x : Fin 3 → ↥(Set.univ : Set ℝ),
      f (intervalMean convex_univ (by norm_num : 0 < 3) x) ≤
        (∑ i, f (intervalRow convex_univ counterMatrix matrix_stochastic x i)) / 3 := by
    intro x
    have he := all_input_identity (fun i => (x i : ℝ))
    change counterFunction (∑ i, (3:ℝ)⁻¹ * (x i : ℝ)) ≤
      (∑ i, counterFunction (∑ j, counterMatrix i j * (x j : ℝ))) / 3
    have hm : (∑ i, (3:ℝ)⁻¹ * (x i : ℝ)) = (∑ i, (x i : ℝ)) / 3 := by
      rw [← Finset.mul_sum]
      ring
    rw [hm]
    change counterFunction ((∑ i, (x i : ℝ)) / 3) ≤
      (∑ i, counterFunction ((counterMatrix *ᵥ fun j => (x j : ℝ)) i)) / 3
    rw [he]
    linarith
  have hm := hj hi ⟨Real.sqrt 3, Set.mem_univ _⟩ ⟨-Real.sqrt 3, Set.mem_univ _⟩
  apply midpoint_failure
  convert hm using 1 <;>
    simp [f, intervalMean, intervalCombination, Fin.sum_univ_succ] <;> ring

end D5.S3.QuadraticForms.BarczyPalesJensenConverse
