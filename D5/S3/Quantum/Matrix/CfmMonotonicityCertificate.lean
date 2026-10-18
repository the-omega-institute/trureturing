/- GID: D5/S3/Quantum/Matrix/CfmMonotonicityCertificate
   generality: G
   mirror-B: D5/B/S3/Quantum/Matrix/CfmMonotonicityCertificate
   mirror-E: none(waiver:open-problem-resolution)
   anchors: [mathlib/module/Mathlib.Analysis.Matrix.Order]
   utility: none
   digest: Scalar and matrix rational functions agree under positive definite functional calculus. -/

/-
admission_basis: open-problem-resolution
resolution_result: CzerwinskaFrancoMerinoCounterexample.result
proof_shape: cfc_rationalFunction: bind-only
consumers: CzerwinskaFrancoMerinoCounterexample.cayley_functional_calculus,
  CzerwinskaFrancoMerinoCounterexample.not_matrix_monotone
The content basis is the endpoint-factorization, interpolation and endpoint-positivity argument.
All declarations here are definitions or a dimension-uniform functional-calculus identity;
none certifies a concrete instance or performs bounded enumeration, checking or numeric reduction.
-/

import D5.S3.Quantum.Matrix.RadialConvexity
import Mathlib.Analysis.Matrix.Order
import Mathlib.Tactic

/-!
The scalar rational function and its matrix expression agree on every positive definite
complex matrix by the continuous functional calculus identities for sums, products and inverses.
-/

set_option autoImplicit false

noncomputable section
open Matrix
open scoped MatrixOrder ComplexOrder

namespace D5.S3.Quantum.Matrix.CfmMonotonicityCertificate

/-- The real scalar function in the counterexample. -/
def scalarFunction (t : ℝ) : ℝ :=
  (t + 1) / (t + 3) + (t + 1) / (2 * t + 4) -
    (1 / 20000 : ℝ) * ((t + 1) / (3 * t + 5))

/-- The rational matrix expression for the proposed scalar counterexample. -/
def rationalFunction {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  (A + 1) * (A + 3)⁻¹ + (A + 1) * ((2 : ℝ) • A + 4)⁻¹ -
    (1 / 20000 : ℝ) • ((A + 1) * ((3 : ℝ) • A + 5)⁻¹)

/-- The smaller positive definite matrix in the finite counterexample. -/
def lowerMatrix : Matrix (Fin 3) (Fin 3) ℂ := diagonal ![1 / 3, 1, 3]

/-- The larger positive definite matrix in the finite counterexample. -/
def upperMatrix : Matrix (Fin 3) (Fin 3) ℂ :=
  (1 / 25 : ℝ) • !![11, 4, 8; 4, 31, 12; 8, 12, 99]

/-- A vector detecting the failure of Loewner positivity. -/
def testVector : Fin 3 → ℂ := ![-35, 48, -15]

/-- The real Hermitian quadratic form at the separating vector. -/
def quadraticReadout (X : Matrix (Fin 3) (Fin 3) ℂ) : ℝ :=
  (star testVector ⬝ᵥ (X *ᵥ testVector)).re

private theorem cfc_rational_term {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.PosDef) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 < b) :
    cfc (fun t : ℝ => (t + 1) / (a * t + b)) A =
      (A + 1) * (a • A + b • (1 : Matrix (Fin n) (Fin n) ℂ))⁻¹ := by
  have hs : (spectrum ℝ A).Finite := by
    rw [hA.isHermitian.spectrum_real_eq_range_eigenvalues]
    exact Set.finite_range _
  have hc (g : ℝ → ℝ) : ContinuousOn g (spectrum ℝ A) := hs.continuousOn _
  have hn : ∀ x ∈ spectrum ℝ A, a * x + b ≠ 0 := by
    intro x hx
    exact ne_of_gt (add_pos_of_nonneg_of_pos
      (mul_nonneg ha (spectrum_nonneg_of_nonneg hA.posSemidef.nonneg hx)) hb)
  rw [cfc_map_div (p := IsSelfAdjoint) (fun t : ℝ => t + 1)
      (fun t : ℝ => a * t + b) A hn (hc _) (hc _) hA.isHermitian.isSelfAdjoint,
    cfc_add_const (p := IsSelfAdjoint) 1 (fun t : ℝ => t) A (hc _) hA.isHermitian.isSelfAdjoint,
    cfc_id' (p := IsSelfAdjoint) ℝ A hA.isHermitian.isSelfAdjoint,
    cfc_add_const (p := IsSelfAdjoint) b (fun t : ℝ => a * t) A (hc _) hA.isHermitian.isSelfAdjoint,
    cfc_const_mul_id (p := IsSelfAdjoint) a A hA.isHermitian.isSelfAdjoint,
    ← Matrix.nonsing_inv_eq_ringInverse]
  simp only [map_one, Algebra.algebraMap_eq_smul_one]

/-- Positive definite spectral functional calculus equals the rational matrix expression.
Consumed bind-only auxiliary for `CzerwinskaFrancoMerinoCounterexample.cayley_functional_calculus`
and `CzerwinskaFrancoMerinoCounterexample.not_matrix_monotone`. -/
theorem cfc_rationalFunction {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.PosDef) : cfc scalarFunction A = rationalFunction A := by
  have hs : (spectrum ℝ A).Finite := by
    rw [hA.isHermitian.spectrum_real_eq_range_eigenvalues]
    exact Set.finite_range _
  have hc (g : ℝ → ℝ) : ContinuousOn g (spectrum ℝ A) := hs.continuousOn _
  unfold scalarFunction
  rw [cfc_sub _ _ A (hc _) (hc _), cfc_add A _ _ (hc _) (hc _),
    cfc_const_mul _ _ A (hc _)]
  rw [show (fun t : ℝ => (t + 1) / (t + 3)) =
      (fun t : ℝ => (t + 1) / (1 * t + 3)) by ext; simp]
  rw [cfc_rational_term hA 1 3 (by norm_num) (by norm_num),
    cfc_rational_term hA 2 4 (by norm_num) (by norm_num),
    cfc_rational_term hA 3 5 (by norm_num) (by norm_num)]
  simp only [rationalFunction, one_smul, ← Algebra.algebraMap_eq_smul_one, map_ofNat]


end D5.S3.Quantum.Matrix.CfmMonotonicityCertificate
