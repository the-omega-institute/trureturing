/- GID: D5/S3/Quantum/Tomography/HadamardSquaredMinorSeparation
   generality: G
   mirror-B: D5/B/S3/Quantum/Tomography/HadamardSquaredMinorSeparation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Nonzero squared minors separate a Hadamard matrix from every monomial equivalent of a matrix with an ER row or column pair. -/

import D5.S3.Quantum.Tomography.MUBHadamardCompatibility
import Mathlib.Tactic.LinearCombination

/- Reuse audit (2026-09-05): consumes the existing HadamardEquivalent.
   No duplicate equivalence relation, Fourier matrix, or Hadamard predicate
   is introduced. The 30 rational interval witnesses in the X-patch checker
   supply the minor-separation hypotheses; their numerical centres are not
   taken as proofs. The public theorem handles arbitrary monomial gauges.
-/

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Tomography.HadamardSquaredMinorSeparation

open Matrix
open D5.S3.Quantum.Tomography.MUBHadamardCompatibility

private theorem phase_ne_zero (z : ℂ) (hz : Complex.normSq z = 1) : z ≠ 0 := by
  intro h
  simpa [h] using hz

private theorem no_equivalence_to_squared_row_pair
    {n : Type*} (H K : ComplexSquare n)
    (hSep : ∀ i j, i ≠ j → ∃ p q,
      (H i p) ^ 2 * (H j q) ^ 2 ≠ (H i q) ^ 2 * (H j p) ^ 2)
    (hPair : ∃ i j, i ≠ j ∧ ∀ p q,
      (K i p) ^ 2 * (K j q) ^ 2 = (K i q) ^ 2 * (K j p) ^ 2) :
    ¬ HadamardEquivalent H K := by
  rintro ⟨σ, τ, r, c, hr, hc, hEq⟩
  obtain ⟨i, j, hij, hPair⟩ := hPair
  obtain ⟨p, q, hpq⟩ := hSep (σ i) (σ j) (σ.injective.ne hij)
  let v : ℂ := r i * r j * c (τ.symm p) * c (τ.symm q)
  have hv : v ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero
      (phase_ne_zero (r i) (hr i)) (phase_ne_zero (r j) (hr j)))
      (phase_ne_zero (c (τ.symm p)) (hc (τ.symm p))))
      (phase_ne_zero (c (τ.symm q)) (hc (τ.symm q)))
  have h := hPair (τ.symm p) (τ.symm q)
  simp only [hEq, Equiv.apply_symm_apply] at h
  have hScaled : v ^ 2 * ((H (σ i) p) ^ 2 * (H (σ j) q) ^ 2) =
      v ^ 2 * ((H (σ i) q) ^ 2 * (H (σ j) p) ^ 2) := by
    dsimp [v]
    linear_combination h
  exact hpq (mul_left_cancel₀ (pow_ne_zero 2 hv) hScaled)

private theorem equivalence_transpose {n : Type*} {H K : ComplexSquare n}
    (h : HadamardEquivalent H K) : HadamardEquivalent Hᵀ Kᵀ := by
  obtain ⟨σ, τ, r, c, hr, hc, hEq⟩ := h
  refine ⟨τ, σ, c, r, hc, hr, ?_⟩
  intro i j
  change K j i = c i * H (σ j) (τ i) * r j
  rw [hEq]
  ring

/-- If every pair of rows and every pair of columns of the entrywise-squared
matrix of H has a nonzero two-by-two minor, then H is not Hadamard-equivalent
to any K having a proportional squared-row or squared-column pair.

Every standard order-six Fourier-family matrix has such an ER pair on one
side. Its transpose has one on the other side. The interval certificate
checks the 30 separation hypotheses for the entire stated X parameter patch.
This theorem proves the gauge-invariant consumer, not the interval replay. -/
theorem not_hadamardEquivalent_of_squared_minor_separation
    {n : Type*} (H K : ComplexSquare n)
    (hRows : ∀ i j, i ≠ j → ∃ p q,
      (H i p) ^ 2 * (H j q) ^ 2 ≠ (H i q) ^ 2 * (H j p) ^ 2)
    (hCols : ∀ i j, i ≠ j → ∃ p q,
      (H p i) ^ 2 * (H q j) ^ 2 ≠ (H q i) ^ 2 * (H p j) ^ 2)
    (hK : (∃ i j, i ≠ j ∧ ∀ p q,
        (K i p) ^ 2 * (K j q) ^ 2 = (K i q) ^ 2 * (K j p) ^ 2) ∨
      (∃ i j, i ≠ j ∧ ∀ p q,
        (K p i) ^ 2 * (K q j) ^ 2 = (K q i) ^ 2 * (K p j) ^ 2)) :
    ¬ HadamardEquivalent H K := by
  rcases hK with hRow | hCol
  · exact no_equivalence_to_squared_row_pair H K hRows hRow
  · intro hEq
    exact no_equivalence_to_squared_row_pair Hᵀ Kᵀ hCols hCol
      (equivalence_transpose hEq)

#print axioms not_hadamardEquivalent_of_squared_minor_separation

end D5.S3.Quantum.Tomography.HadamardSquaredMinorSeparation
