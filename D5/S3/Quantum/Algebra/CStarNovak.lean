/- GID: D5/S3/Quantum/Algebra/CStarNovak
   generality: I
   mirror-B: D5/B/S3/Quantum/Algebra/CStarNovak
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Algebra/CStarNovak.claim; result=D5/S3/Quantum/Algebra/CStarNovak.result; claim=D5/S3/Quantum/Algebra/CStarNovak.claim
   digest: A self-adjoint matrix witness refutes the C*-algebraic Novak conjecture. -/

/-
admission_basis: open-problem-resolution (#14974; Refuted)
proof_shape: ncos_hasSum: bind-only (consumer: ncos_of_sq)
proof_shape: ncos_of_sq: bind-only (consumer: cosine_diff)
proof_shape: a_selfAdjoint: bind-only (consumer: result)
proof_shape: square_diff: bind-only (consumer: cosine_diff)
proof_shape: cosine_diff: bind-only (consumer: witness_entry)
proof_shape: witness_entry: bind-only (consumer: witness_quadratic)
proof_shape: witness_quadratic: bind-only (consumer: result)
proof_shape: negative_one_not_nonneg: bind-only (consumer: result)
proof_shape: result: bind-only
escape_witness: none
Direct frozen dependencies: none (Mathlib-only imports).
The algebra quantified by claim is in Type, restricting the source universe range.
This weakens the claim, so its negation refutes the source statement.
The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9).
The series helpers instantiate Mathlib's exponential and cosine summation theorems,
reindex the sum into even and odd fibers, and normalize the scalar-square relation.
The witness helpers normalize explicit matrix entries. The result settles the
external conjecture under the stated unital C*-algebra and compatible-order conventions.
-/

import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder
noncomputable section
namespace D5.S3.Quantum.Algebra.CStarNovak

def ncos {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] (x : A) : A :=
  (2 : ℂ)⁻¹ • (NormedSpace.exp (Complex.I • x) +
    NormedSpace.exp (-(Complex.I • x)))

def novakEntry {A : Type*} [CStarAlgebra A] (n d : ℕ)
    (x : Fin n → Fin d → A) (j k : Fin n) : A :=
  (List.ofFn fun l => (2 : ℂ)⁻¹ • (1 + ncos (x j l - x k l))).prod -
    ((n : ℂ)⁻¹) • 1

def IsPositiveMatrix {A : Type*} [CStarAlgebra A] [PartialOrder A]
    {n : ℕ} (M : Fin n → Fin n → A) : Prop :=
  (∀ j k, star (M j k) = M k j) ∧
    ∀ v : Fin n → A, 0 ≤ ∑ j, ∑ k, M j k * v k * star (v j)

def claim : Prop :=
  ∀ (A : Type) [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (n d : ℕ), 2 ≤ n → 2 ≤ d → ∀ x : Fin n → Fin d → A,
    (∀ j l, IsSelfAdjoint (x j l)) → IsPositiveMatrix (novakEntry n d x)


section Cosine
variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

set_option backward.defeqAttrib.useBackward true in
private theorem ncos_hasSum (x : A) :
    HasSum (fun n : ℕ => ((Nat.factorial (2 * n) : ℂ)⁻¹) •
      (Complex.I • x) ^ (2 * n)) (ncos x) := by
  have h := ((NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) (Complex.I • x)).add
    (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) (-(Complex.I • x)))).const_smul
      ((2 : ℂ)⁻¹)
  replace h := (Nat.divModEquiv 2).symm.hasSum_iff.mpr h
  dsimp [Function.comp_def] at h
  refine h.prod_fiberwise fun n => ?_
  convert hasSum_fintype (_ : Fin 2 → A) using 1
  rw [Fin.sum_univ_two]
  simp only [Fin.val_zero, Fin.val_one, add_zero, mul_comm n 2]
  change ((Nat.factorial (2 * n) : ℂ)⁻¹) • (Complex.I • x) ^ (2 * n) =
    (2 : ℂ)⁻¹ • (((Nat.factorial (2 * n) : ℂ)⁻¹) • (Complex.I • x) ^ (2 * n) +
      ((Nat.factorial (2 * n) : ℂ)⁻¹) • (-(Complex.I • x)) ^ (2 * n)) +
    (2 : ℂ)⁻¹ • (((Nat.factorial (2 * n + 1) : ℂ)⁻¹) •
      (Complex.I • x) ^ (2 * n + 1) + ((Nat.factorial (2 * n + 1) : ℂ)⁻¹) •
      (-(Complex.I • x)) ^ (2 * n + 1))
  simp only [Even.neg_pow (even_two_mul n), Odd.neg_pow (odd_two_mul_add_one n),
    smul_neg, add_neg_cancel, smul_zero, add_zero, ← two_smul ℂ, smul_smul]
  norm_num
  congr 1
  ring

private theorem ncos_of_sq (x : A) (c : ℝ)
    (hx : x * x = (c : ℂ) ^ 2 • (1 : A)) :
    ncos x = (Real.cos c : ℂ) • (1 : A) := by
  have hpow (n : ℕ) : x ^ (2 * n) = (c : ℂ) ^ (2 * n) • (1 : A) := by
    rw [pow_mul, pow_two, hx, smul_pow, one_pow, ← pow_mul]
  have h := (Complex.hasSum_cos' (c : ℂ)).smul_const (1 : A)
  rw [← Complex.ofReal_cos] at h
  apply (ncos_hasSum x).unique
  convert h using 1
  ext n
  rw [smul_pow, hpow, smul_smul, smul_smul]
  congr 1
  simp [mul_pow, div_eq_mul_inv]
  ring

end Cosine

private def a : Fin 3 → Matrix (Fin 2) (Fin 2) ℂ :=
  ![(((3 * Real.pi : ℝ) : ℂ)) • 1,
    (Real.pi : ℂ) • Matrix.diagonal ![5, 1],
    (((Real.pi / 4 : ℝ) : ℂ)) •
      !![19, (Real.sqrt 15 : ℂ); (Real.sqrt 15 : ℂ), 5]]

private def radius : Fin 3 → Fin 3 → ℝ :=
  !![0, 2 * Real.pi, 2 * Real.pi;
    2 * Real.pi, 0, Real.pi;
    2 * Real.pi, Real.pi, 0]

private theorem a_selfAdjoint (j : Fin 3) : IsSelfAdjoint (a j) := by
  change star (a j) = a j
  ext r s
  fin_cases j <;> fin_cases r <;> fin_cases s <;>
    simp [a, Matrix.smul_apply]

private theorem square_diff (j k : Fin 3) :
    (a j - a k) * (a j - a k) = (radius j k : ℂ) ^ 2 • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  have hs : (Real.sqrt 15 : ℂ) ^ 2 = 15 := by
    norm_cast
    exact Real.sq_sqrt (by norm_num)
  ext r s
  fin_cases j <;> fin_cases k <;> fin_cases r <;> fin_cases s <;>
    simp [a, radius, Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply,
      Matrix.one_apply] <;> push_cast <;> ring_nf <;> simp [hs] <;> ring

private theorem cosine_diff (j k : Fin 3) :
    ncos (a j - a k) =
      (if (j = 1 ∧ k = 2) ∨ (j = 2 ∧ k = 1) then (-1 : ℂ) else 1) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [ncos_of_sq _ (radius j k) (square_diff j k)]
  fin_cases j <;> fin_cases k <;> simp [radius, Real.cos_two_pi, Real.cos_pi]


private def coeff (j k : Fin 3) : ℂ :=
  (3 : ℂ)⁻¹ * (!![2, 2, 2; 2, 2, -1; 2, -1, 2] : Matrix (Fin 3) (Fin 3) ℂ) j k

private theorem witness_entry (j k : Fin 3) :
    novakEntry 3 2 (fun j _ => a j) j k = coeff j k • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  simp only [novakEntry, cosine_diff]
  fin_cases j <;> fin_cases k <;> ext r s <;> fin_cases r <;> fin_cases s <;>
    norm_num [coeff, Pi.smul_apply, Fin.ext_iff, List.ofFn_succ, Matrix.mul_apply,
      Fin.sum_univ_two, Matrix.smul_apply, Matrix.one_apply, Matrix.ofNat_apply]

private def v : Fin 3 → Matrix (Fin 2) (Fin 2) ℂ := ![(-2 : ℂ) • 1, 1, 1]

private theorem witness_quadratic :
    (∑ j, ∑ k, novakEntry 3 2 (fun j _ => a j) j k * v k * star (v j)) =
      (-2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  simp_rw [witness_entry]
  ext r s
  fin_cases r <;> fin_cases s <;>
    norm_num [coeff, Pi.smul_apply, v, Fin.sum_univ_succ, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.smul_apply, Matrix.one_apply, Matrix.ofNat_apply]

private theorem negative_one_not_nonneg : ¬ (0 : Matrix (Fin 2) (Fin 2) ℂ) ≤ (-2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  intro h
  have hd := (Matrix.nonneg_iff_posSemidef.mp h).diag_nonneg (i := 0)
  norm_num [Matrix.smul_apply, Matrix.one_apply, Complex.nonneg_iff] at hd

theorem result : ¬ claim := by
  intro h
  have hp := h (Matrix (Fin 2) (Fin 2) ℂ) 3 2 (by norm_num) (by norm_num) (fun j _ => a j)
    (fun j _ => a_selfAdjoint j)
  have hq := hp.2 v
  rw [witness_quadratic] at hq
  exact negative_one_not_nonneg hq

end D5.S3.Quantum.Algebra.CStarNovak
