/- GID: D5/S3/Quantum/Tomography/ComplexHadamardTwoSided
   generality: G
   mirror-B: D5/B/S3/Quantum/Tomography/ComplexHadamardTwoSided
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A finite square complex Hadamard has the conjugate column Gram law, and every MUB relative Gram is a scaled complex Hadamard. -/

import D5.S3.Quantum.Tomography.MUBCompletionGluing

/- Library-search audit trail (2026-09-03):
   * Reuses `ComplexSquare`, `EntrywiseUnit`, `IsComplexHadamard`, and
     `HadamardUnbiased`; no second Hadamard or unitary predicate is introduced.
   * Reuses Mathlib's square-matrix inverse-side exchange through
     `Matrix.mul_eq_one_comm`.
   * Reuses the fixed-edge recovery laws from `MUBCompletionGluing`.
   * Repository search found repeated local needs for column Gram equations,
     but no public theorem attached to the new `IsComplexHadamard` carrier.
-/

open scoped BigOperators Matrix

noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Tomography.ComplexHadamardTwoSided

open Matrix
open D5.S3.Quantum.Tomography.MUBHadamardCompatibility
open D5.S3.Quantum.Tomography.MUBCompletionGluing

private theorem card_cast_ne_zero
    {n : Type*} [Fintype n] [Nonempty n] :
    (Fintype.card n : ℂ) ≠ 0 := by
  exact_mod_cast (Nat.ne_of_gt (Fintype.card_pos : 0 < Fintype.card n))

/-- The stored row Gram equation of a finite square complex Hadamard implies
its conjugate column Gram equation. -/
theorem conjTranspose_mul_self_eq_card_smul
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (H : ComplexSquare n)
    (hH : IsComplexHadamard H) :
    Hᴴ * H = (Fintype.card n : ℂ) • (1 : ComplexSquare n) := by
  let d : ℂ := Fintype.card n
  have hd : d ≠ 0 := card_cast_ne_zero
  have hRight : (d⁻¹ • H) * Hᴴ = (1 : ComplexSquare n) := by
    calc
      (d⁻¹ • H) * Hᴴ = d⁻¹ • (H * Hᴴ) := by
        simp [Matrix.smul_mul]
      _ = d⁻¹ • (d • (1 : ComplexSquare n)) := by rw [hH.2]
      _ = 1 := by simp [smul_smul, hd]
  have hLeft : Hᴴ * (d⁻¹ • H) = (1 : ComplexSquare n) :=
    (Matrix.mul_eq_one_comm).mp hRight
  have hScaled : d⁻¹ • (Hᴴ * H) = (1 : ComplexSquare n) := by
    simpa [Matrix.mul_smul] using hLeft
  calc
    Hᴴ * H = d • (d⁻¹ • (Hᴴ * H)) := by
      simp [smul_smul, hd]
    _ = d • (1 : ComplexSquare n) := by rw [hScaled]

/-- The relative Gram of two unnormalized complex Hadamards has row Gram
`d^2 I`. No square-root normalization is needed. -/
theorem relativeGram_mul_conjTranspose_eq_card_sq_smul
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (X X' : ComplexSquare n)
    (hX : IsComplexHadamard X)
    (hX' : IsComplexHadamard X') :
    (Xᴴ * X') * (Xᴴ * X')ᴴ =
      ((Fintype.card n : ℂ) * (Fintype.card n : ℂ)) •
        (1 : ComplexSquare n) := by
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  calc
    (Xᴴ * X') * (X'ᴴ * X) = Xᴴ * (X' * X'ᴴ) * X := by
      simp only [Matrix.mul_assoc]
    _ = Xᴴ * ((Fintype.card n : ℂ) •
        (1 : ComplexSquare n)) * X := by rw [hX'.2]
    _ = (Fintype.card n : ℂ) • (Xᴴ * X) := by simp
    _ = (Fintype.card n : ℂ) •
        ((Fintype.card n : ℂ) • (1 : ComplexSquare n)) := by
      rw [conjTranspose_mul_self_eq_card_smul X hX]
    _ = ((Fintype.card n : ℂ) * (Fintype.card n : ℂ)) •
        (1 : ComplexSquare n) := by rw [smul_smul]

/-- A MUB relative Gram is entrywise of squared modulus `d` and has row Gram
`d^2 I`. This is the exact scaled-Hadamard carrier used by the one-matrix
completion system. -/
theorem relativeGram_scaledHadamard
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (X X' : ComplexSquare n)
    (hX : IsComplexHadamard X)
    (hX' : IsComplexHadamard X')
    (hUnbiased : HadamardUnbiased X X') :
    (∀ i j,
      Complex.normSq ((Xᴴ * X') i j) = (Fintype.card n : ℝ)) ∧
    (Xᴴ * X') * (Xᴴ * X')ᴴ =
      ((Fintype.card n : ℂ) * (Fintype.card n : ℂ)) •
        (1 : ComplexSquare n) := by
  exact ⟨hUnbiased,
    relativeGram_mul_conjTranspose_eq_card_sq_smul X X' hX hX'⟩

/-- The rational recovery law also has a right-inverse certificate: after
recovering `X' = d⁻¹ X P` from `P = Xᴴ X'`, recomputing the relative Gram
returns `P`. -/
theorem relativeGram_of_recovered_factor
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (X P : ComplexSquare n)
    (hX : IsComplexHadamard X) :
    Xᴴ * (((Fintype.card n : ℂ)⁻¹) • (X * P)) = P := by
  let d : ℂ := Fintype.card n
  have hd : d ≠ 0 := card_cast_ne_zero
  calc
    Xᴴ * (d⁻¹ • (X * P)) = d⁻¹ • (Xᴴ * (X * P)) := by simp
    _ = d⁻¹ • ((Xᴴ * X) * P) := by rw [Matrix.mul_assoc]
    _ = d⁻¹ • ((d • (1 : ComplexSquare n)) * P) := by
      rw [conjTranspose_mul_self_eq_card_smul X hX]
    _ = P := by simp [smul_smul, hd]

#print axioms conjTranspose_mul_self_eq_card_smul
#print axioms relativeGram_mul_conjTranspose_eq_card_sq_smul
#print axioms relativeGram_scaledHadamard
#print axioms relativeGram_of_recovered_factor

end D5.S3.Quantum.Tomography.ComplexHadamardTwoSided
