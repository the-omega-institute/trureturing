/- GID: D5/S3/ConceptDynamics/Algebra/PositiveInvariantMetricSelection
   generality: I
   mirror-B: D5/B/S3/ConceptDynamics/Algebra/PositiveInvariantMetricSelection
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Zero real drift, unit spectrum, and a positive invariant metric are equivalent. -/

import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Eigenspace.Matrix
import Mathlib.Data.List.TFAE
import Mathlib.Tactic

/- Library-search audit trail (2026-09-02):
   * Repository searches for positive invariant metrics, unit-circle spectra,
     and conjugate-transpose invariance found no theorem with this equivalence.
   * Pinned Mathlib provides `Matrix.PosDef.one`, `Matrix.PosDef.diag_pos`,
     `spectrum_diagonal`, `Complex.norm_exp`, and `Real.exp_eq_one_iff`; these
     canonical primitives are used directly.
   * Ecosystem searches for positive invariant metrics and the displayed
     conjugate-transpose equation found no exact Lean theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Algebra.PositiveInvariantMetricSelection

open Complex Matrix
open scoped ComplexConjugate ComplexOrder

/-- For the canonical two-mode diagonal complex flow over a positive period,
zero real drift, unit-modulus spectrum, and preservation of a positive metric
are equivalent. -/
theorem positive_invariant_metric_selection
    (delta gamma period : Real) (hperiod : 0 < period) :
    let forward : Complex :=
      Complex.exp (((delta : Complex) + Complex.I * (gamma : Complex)) * (period : Complex))
    let backward : Complex :=
      Complex.exp (-(((delta : Complex) + Complex.I * (gamma : Complex)) * (period : Complex)))
    let monodromy : Matrix (Fin 2) (Fin 2) Complex := diagonal ![forward, backward]
    List.TFAE [
      delta = 0,
      ∀ lambda ∈ spectrum Complex monodromy, ‖lambda‖ = 1,
      ∃ H : Matrix (Fin 2) (Fin 2) Complex,
        H.PosDef ∧ monodromyᴴ * H * monodromy = H] := by
  dsimp only
  tfae_have 1 → 2 := by
    intro hdelta
    subst delta
    intro lambda hlambda
    rw [spectrum_diagonal] at hlambda
    obtain ⟨i, rfl⟩ := hlambda
    fin_cases i <;> simp [Complex.norm_exp]
  tfae_have 2 → 1 := by
    intro hspectrum
    have hforward := hspectrum
      (Complex.exp
        (((delta : Complex) + Complex.I * (gamma : Complex)) * (period : Complex)))
      (by
        rw [spectrum_diagonal]
        exact ⟨0, rfl⟩)
    rw [Complex.norm_exp] at hforward
    have hreal : Real.exp (delta * period) = 1 := by
      simpa using hforward
    have hproduct : delta * period = 0 := by
      exact (Real.exp_eq_one_iff _).mp hreal
    exact (mul_eq_zero.mp hproduct).resolve_right (ne_of_gt hperiod)
  tfae_have 1 → 3 := by
    intro hdelta
    subst delta
    refine ⟨1, Matrix.PosDef.one, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
      change conj (Complex.exp _) * Complex.exp _ = 1 <;>
      rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq,
        Complex.norm_exp] <;>
      norm_num
  tfae_have 3 → 1 := by
    rintro ⟨H, hH, hInvariant⟩
    have hEntry := congrFun (congrFun hInvariant (0 : Fin 2)) (0 : Fin 2)
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply,
      Matrix.diagonal_apply, Fin.isValue] at hEntry
    simp at hEntry
    have hH00 : H 0 0 ≠ 0 := ne_of_gt hH.diag_pos
    have hModulus :
        star (Complex.exp
          (((delta : Complex) + Complex.I * (gamma : Complex)) * (period : Complex))) *
          Complex.exp
            (((delta : Complex) + Complex.I * (gamma : Complex)) * (period : Complex)) = 1 := by
      apply mul_right_cancel₀ hH00
      calc
        (star (Complex.exp
              (((delta : Complex) + Complex.I * (gamma : Complex)) * (period : Complex))) *
            Complex.exp
              (((delta : Complex) + Complex.I * (gamma : Complex)) * (period : Complex))) *
            H 0 0 =
            star (Complex.exp
              (((delta : Complex) + Complex.I * (gamma : Complex)) * (period : Complex))) *
              H 0 0 *
                Complex.exp
                  (((delta : Complex) + Complex.I * (gamma : Complex)) * (period : Complex)) := by
                    ring
        _ = H 0 0 := hEntry
        _ = 1 * H 0 0 := by ring
    have hNormSqComplex :
        ((Complex.normSq
          (Complex.exp
            (((delta : Complex) + Complex.I * (gamma : Complex)) * (period : Complex))) :
            Real) : Complex) = 1 := by
      rw [Complex.normSq_eq_conj_mul_self]
      simpa [RCLike.star_def] using hModulus
    have hNormSq :
        Complex.normSq
          (Complex.exp
            (((delta : Complex) + Complex.I * (gamma : Complex)) * (period : Complex))) = 1 := by
      exact Complex.ofReal_injective hNormSqComplex
    have hNorm :
        ‖Complex.exp
          (((delta : Complex) + Complex.I * (gamma : Complex)) * (period : Complex))‖ = 1 := by
      rw [Complex.normSq_eq_norm_sq] at hNormSq
      nlinarith [norm_nonneg
        (Complex.exp
          (((delta : Complex) + Complex.I * (gamma : Complex)) * (period : Complex)))]
    rw [Complex.norm_exp] at hNorm
    have hreal : Real.exp (delta * period) = 1 := by
      simpa using hNorm
    have hproduct : delta * period = 0 := by
      exact (Real.exp_eq_one_iff _).mp hreal
    exact (mul_eq_zero.mp hproduct).resolve_right (ne_of_gt hperiod)
  tfae_finish

#print axioms positive_invariant_metric_selection

end D5.S3.ConceptDynamics.Algebra.PositiveInvariantMetricSelection
