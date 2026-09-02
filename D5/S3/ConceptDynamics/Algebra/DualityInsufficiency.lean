/- GID: D5/S3/ConceptDynamics/Algebra/DualityInsufficiency
   generality: I
   mirror-B: D5/B/S3/ConceptDynamics/Algebra/DualityInsufficiency
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Reciprocal split duality does not force a two-mode flow onto its unitary boundary. -/

import D5.S3.ConceptDynamics.Algebra.PositiveInvariantMetricSelection
import D5.S3.Quantum.FiniteDimensional
import D5.S3.Zeros.Symmetry.ZetaConjugationCovariance

/- Library-search audit trail (2026-09-02):
   * Repository searches for reciprocal two-mode monodromy, split-form
     preservation, and positive invariant metrics found
     `positive_invariant_metric_selection`, which supplies the exact positive
     metric obstruction used below. `OfflineZeroGeometricMonodromy` has only a
     real golden-period specialization and cannot cover the free positive
     observation period or the complex phase in this theorem.
   * Pinned Mathlib provides diagonal determinants, matrix inversion, complex
     exponential norms, and finite two-by-two matrix simplification, but no
     theorem combining all displayed duality and positivity clauses.
   * Searches of the installed admissible packages found no exact result with
     the source's reflection, reciprocal, split-form, and positivity clauses. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.ConceptDynamics.Algebra.DualityInsufficiency

open Complex Matrix
open scoped ComplexConjugate ComplexOrder
open D5.S3.ConceptDynamics.Algebra.PositiveInvariantMetricSelection
open D5.S3.Quantum.FiniteDimensional
open D5.S3.Zeros.CompletedZeta

/-- For every nonzero real drift and positive observation period, the
canonical reciprocal two-mode flow has determinant one, reflection and branch
exchange duality, nonunit stable/unstable multipliers, and a preserved split
form, but it admits no positive invariant Hermitian metric and its duality does
not force the drift to vanish. -/
theorem duality_insufficiency
    (delta gamma period : Real) (hperiod : 0 < period) (hdelta : delta ≠ 0) :
    let exponent : Complex :=
      ((delta : Complex) + Complex.I * (gamma : Complex)) * (period : Complex)
    let forward : Complex := Complex.exp exponent
    let backward : Complex := Complex.exp (-exponent)
    let monodromy : Matrix (Fin 2) (Fin 2) Complex := diagonal ![forward, backward]
    let rho : Complex := (1 / 2 : Complex) + delta + Complex.I * gamma
    let dualityClosed : Prop :=
      xiReading (1 - rho) = xiReading rho ∧
        Matrix.det monodromy = 1 ∧
        qubitX * monodromy * qubitX = monodromy⁻¹ ∧
        forward * backward = 1 ∧
        ‖forward‖ ≠ 1 ∧ ‖backward‖ ≠ 1 ∧
        monodromy.transpose * qubitX * monodromy = qubitX
    dualityClosed ∧
      ¬(dualityClosed → delta = 0) ∧
      ¬∃ H : Matrix (Fin 2) (Fin 2) Complex,
        H.PosDef ∧ monodromyᴴ * H * monodromy = H := by
  dsimp only
  let exponent : Complex :=
    ((delta : Complex) + Complex.I * (gamma : Complex)) * (period : Complex)
  let forward : Complex := Complex.exp exponent
  let backward : Complex := Complex.exp (-exponent)
  let monodromy : Matrix (Fin 2) (Fin 2) Complex := diagonal ![forward, backward]
  let rho : Complex := (1 / 2 : Complex) + delta + Complex.I * gamma
  change
    (xiReading (1 - rho) = xiReading rho ∧
      Matrix.det monodromy = 1 ∧
      qubitX * monodromy * qubitX = monodromy⁻¹ ∧
      forward * backward = 1 ∧
      ‖forward‖ ≠ 1 ∧ ‖backward‖ ≠ 1 ∧
      monodromy.transpose * qubitX * monodromy = qubitX) ∧
    ¬((xiReading (1 - rho) = xiReading rho ∧
      Matrix.det monodromy = 1 ∧
      qubitX * monodromy * qubitX = monodromy⁻¹ ∧
      forward * backward = 1 ∧
      ‖forward‖ ≠ 1 ∧ ‖backward‖ ≠ 1 ∧
      monodromy.transpose * qubitX * monodromy = qubitX) → delta = 0) ∧
    ¬∃ H : Matrix (Fin 2) (Fin 2) Complex,
      H.PosDef ∧ monodromyᴴ * H * monodromy = H
  have hreciprocal : forward * backward = 1 := by
    simp [forward, backward, ← Complex.exp_add]
  have hdet : Matrix.det monodromy = 1 := by
    rw [Matrix.det_fin_two]
    simpa [monodromy] using hreciprocal
  have hreciprocal_rev : backward * forward = 1 := by
    simpa [mul_comm] using hreciprocal
  have hswap :
      qubitX * monodromy * qubitX = diagonal ![backward, forward] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [monodromy, qubitX, Matrix.mul_apply, Matrix.vecMul_diagonal,
        Fin.sum_univ_two]
  have hleft : (qubitX * monodromy * qubitX) * monodromy = 1 := by
    rw [hswap]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [monodromy, Matrix.mul_apply, Fin.sum_univ_two,
        hreciprocal, hreciprocal_rev]
  have hinverse : qubitX * monodromy * qubitX = monodromy⁻¹ := by
    apply Matrix.left_inv_eq_left_inv hleft
    exact Matrix.nonsing_inv_mul monodromy (by rw [hdet]; exact isUnit_one)
  have hforwardNorm : ‖forward‖ ≠ 1 := by
    have hproduct : delta * period ≠ 0 :=
      mul_ne_zero hdelta (ne_of_gt hperiod)
    have hexp : Real.exp (delta * period) ≠ 1 := by
      intro h
      exact hproduct ((Real.exp_eq_one_iff _).mp h)
    simpa [forward, exponent, Complex.norm_exp] using hexp
  have hbackwardNorm : ‖backward‖ ≠ 1 := by
    have hproduct : -(delta * period) ≠ 0 :=
      neg_ne_zero.mpr (mul_ne_zero hdelta (ne_of_gt hperiod))
    have hexp : Real.exp (-(delta * period)) ≠ 1 := by
      intro h
      exact hproduct ((Real.exp_eq_one_iff _).mp h)
    simpa [backward, exponent, Complex.norm_exp] using hexp
  have hsplit : monodromy.transpose * qubitX * monodromy = qubitX := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [monodromy, qubitX, Matrix.mul_apply, Fin.sum_univ_two,
        hreciprocal, hreciprocal_rev]
  have hreflection : xiReading (1 - rho) = xiReading rho :=
    xi_reading_reflection rho
  have hclosed :
      xiReading (1 - rho) = xiReading rho ∧
        Matrix.det monodromy = 1 ∧
        qubitX * monodromy * qubitX = monodromy⁻¹ ∧
        forward * backward = 1 ∧
        ‖forward‖ ≠ 1 ∧ ‖backward‖ ≠ 1 ∧
        monodromy.transpose * qubitX * monodromy = qubitX :=
    ⟨hreflection, hdet, hinverse, hreciprocal, hforwardNorm, hbackwardNorm, hsplit⟩
  refine ⟨hclosed, ?_, ?_⟩
  · intro hforces
    exact hdelta (hforces hclosed)
  · intro hmetric
    apply hdelta
    exact
      ((positive_invariant_metric_selection delta gamma period hperiod).out 2 0).mp
        (by simpa [exponent, forward, backward, monodromy] using hmetric)

#print axioms duality_insufficiency

end D5.S3.ConceptDynamics.Algebra.DualityInsufficiency
