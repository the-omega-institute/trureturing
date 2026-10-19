/- GID: D5/S3/Quantum/Matrix/WassersteinMean
   generality: G
   mirror-B: D5/B/S3/Quantum/Matrix/WassersteinMean
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: [mathlib/module/Mathlib.Analysis.Matrix.HermitianFunctionalCalculus, mathlib/module/Mathlib.Analysis.Matrix.Order]
   utility: none
   digest: Wasserstein means, real spectral powers and weak log-majorization. -/

import D5.S3.Quantum.Matrix.SpectralPower
import D5.S3.Quantum.Hiai.PsiMeanTraceConcavity
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic

/-! Spectral definitions for the binary Wasserstein mean. -/

noncomputable section
open Matrix Filter Topology
open scoped MatrixOrder ComplexOrder
namespace D5.S3.Quantum.Matrix.WassersteinMean
open D5.S3.Quantum.Matrix.SpectralPower (mpow)
open D5.S3.Quantum.Hiai.PsiMeanTraceConcavity (geometricMean)

/-- The binary Wasserstein mean in the explicit formula of Gan and Kim. -/
def wassersteinMean {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) :
    Matrix (Fin n) (Fin n) ℂ :=
  ((1 - t) ^ 2) • A + (t ^ 2) • B +
    (t * (1 - t)) • (A * geometricMean (1 / 2) A⁻¹ B + geometricMean (1 / 2) A⁻¹ B * A)

/-- The family (A^p diamond_t B^p)^(1/p). -/
def powerMean {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) (t p : ℝ) :
    Matrix (Fin n) (Fin n) ℂ :=
  mpow (wassersteinMean (mpow A p) (mpow B p) t) (1 / p)

/-- All prefix products of the decreasingly sorted Hermitian eigenvalues are compared.
The empty product is included and imposes only 1 ≤ 1. -/
def weakLogMajorization {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∃ hA : A.IsHermitian, ∃ hB : B.IsHermitian, ∀ k : ℕ, k ≤ n →
    (∏ i : Fin (Fintype.card (Fin n)), if i.val < k then hA.eigenvalues₀ i else 1) ≤
    (∏ i : Fin (Fintype.card (Fin n)), if i.val < k then hB.eigenvalues₀ i else 1)

/-- The last prefix in weak log-majorization compares the determinants. -/
theorem weakLogMajorization_det_le {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℂ}
    (h : weakLogMajorization A B) : A.det.re ≤ B.det.re := by
  classical
  obtain ⟨hA, hB, h⟩ := h
  have hp := h n le_rfl
  have hi (i : Fin (Fintype.card (Fin n))) : i.val < n := by simpa using i.isLt
  simp_rw [if_pos (hi _)] at hp
  have det_prod (M : Matrix (Fin n) (Fin n) ℂ) (hM : M.IsHermitian) :
      M.det.re = ∏ i, hM.eigenvalues₀ i := by
    rw [hM.det_eq_prod_eigenvalues]
    simp only [RCLike.ofReal_eq_complex_ofReal, ← Complex.ofReal_prod, Complex.ofReal_re]
    exact (Equiv.prod_comp (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin n)))).symm
      hM.eigenvalues₀)
  rw [det_prod A hA, det_prod B hB]
  exact hp

end D5.S3.Quantum.Matrix.WassersteinMean
