/- GID: D5/S3/Quantum/Matrix/TaylorMajorization/Defs
   generality: G
   mirror-B: D5/B/S3/Quantum/Matrix/TaylorMajorization/Defs
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib]
   utility: none
   digest: Taylor coefficients and sorted spectral weak majorization for Hermitian matrices. -/

import Mathlib

noncomputable section
open Matrix BigOperators

namespace D5.S3.Quantum.Matrix.TaylorMajorization.Defs

variable {n : ℕ}

/-- The ordered binomial coefficient of the product of two matrix exponentials. -/
noncomputable def taylorQ (A B : Matrix (Fin n) (Fin n) ℂ) (k : ℕ) :
    Matrix (Fin n) (Fin n) ℂ :=
  ∑ p ∈ Finset.range (k + 1), ((k.choose p : ℕ) : ℂ) • (A ^ p * B ^ (k - p))

/-- The Hermitian part of the ordered Taylor coefficient. -/
noncomputable def taylorR (A B : Matrix (Fin n) (Fin n) ℂ) (k : ℕ) :
    Matrix (Fin n) (Fin n) ℂ :=
  (1 / 2 : ℂ) • (taylorQ A B k + (taylorQ A B k)ᴴ)

/-- Hermitian symmetrization gives a Hermitian matrix at every order. -/
theorem taylorR_isHermitian (A B : Matrix (Fin n) (Fin n) ℂ) (k : ℕ) :
    (taylorR A B k).IsHermitian := by
  exact (isHermitian_add_transpose_self _).smul (by simp [IsSelfAdjoint])

/-- All initial sums of the eigenvalues in nonincreasing order are compared. -/
def weakMaj {X Y : Matrix (Fin n) (Fin n) ℂ} (hX : X.IsHermitian)
    (hY : Y.IsHermitian) : Prop :=
  ∀ r : ℕ, r ≤ n →
    (∑ i : Fin (Fintype.card (Fin n)), if i.val < r then hX.eigenvalues₀ i else 0) ≤
    ∑ i : Fin (Fintype.card (Fin n)), if i.val < r then hY.eigenvalues₀ i else 0

/-- The proposed comparison at every dimension and order at least five. -/
def claim : Prop :=
  ∀ (n : ℕ), 1 ≤ n →
    ∀ (A B : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian) (hB : B.IsHermitian)
      (k : ℕ), 5 ≤ k →
      weakMaj ((hA.add hB).pow k) (taylorR_isHermitian A B k)

/-- The real trace defect of the proposed inequality. -/
def defect (A B : Matrix (Fin n) (Fin n) ℂ) (k : ℕ) : ℝ :=
  (taylorR A B k).trace.re - ((A + B) ^ k).trace.re

/-- The full sorted sum in weak majorization is the trace. -/
theorem weakMaj_trace {X Y : Matrix (Fin n) (Fin n) ℂ}
    {hX : X.IsHermitian} {hY : Y.IsHermitian} (h : weakMaj hX hY) :
    X.trace.re ≤ Y.trace.re := by
  have hs (M : Matrix (Fin n) (Fin n) ℂ) (hM : M.IsHermitian) :
      M.trace.re = ∑ i, hM.eigenvalues₀ i := by
    rw [hM.trace_eq_sum_eigenvalues, Complex.re_sum]
    simp only [Matrix.IsHermitian.eigenvalues]
    exact (Equiv.sum_comp (Fintype.equivOfCardEq (Fintype.card_fin _)).symm _)
  rw [hs X hX, hs Y hY]
  simpa only [show ∀ i : Fin (Fintype.card (Fin n)), i.val < n from
    fun i => by simpa using i.isLt, ite_true] using h n le_rfl

end D5.S3.Quantum.Matrix.TaylorMajorization.Defs
