/- GID: D5/S3/Quantum/Tomography/ComplexHadamardRelativeGramCocycle
   generality: G
   mirror-B: D5/B/S3/Quantum/Tomography/ComplexHadamardRelativeGramCocycle
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Relative Grams of finite complex Hadamards form a square-root-free scaled transition cocycle. -/

import D5.S3.Quantum.Tomography.ComplexHadamardTwoSided

/- Library-search audit trail (2026-09-03):
   * Reuses the generic Hadamard carrier and its two-sided Gram theorem.
   * Reuses Matrix conjugate transpose and associativity. No graph, category,
     or duplicate transition structure is introduced at this stage.
-/

open scoped BigOperators Matrix

noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Tomography.ComplexHadamardRelativeGramCocycle

open Matrix
open D5.S3.Quantum.Tomography.MUBHadamardCompatibility
open D5.S3.Quantum.Tomography.ComplexHadamardTwoSided

/-- The relative Gram from a complex Hadamard to itself is `d I`. -/
theorem relativeGram_refl
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (H : ComplexSquare n)
    (hH : IsComplexHadamard H) :
    Hᴴ * H = (Fintype.card n : ℂ) • (1 : ComplexSquare n) :=
  conjTranspose_mul_self_eq_card_smul H hH

/-- Reversing a relative transition is conjugate transpose. -/
theorem relativeGram_reverse
    {n : Type*} [Fintype n]
    (H K : ComplexSquare n) :
    (Hᴴ * K)ᴴ = Kᴴ * H := by
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]

/-- Square-root-free cocycle law for relative Grams.

If `G_ab = H_aᴴ H_b`, then `G_ab G_bc = d G_ac`. This is the coherent
vertex-gauge relation that independently selected Hadamard class
representatives need not preserve. -/
theorem relativeGram_cocycle
    {n : Type*} [Fintype n] [DecidableEq n]
    (H K L : ComplexSquare n)
    (hK : IsComplexHadamard K) :
    (Hᴴ * K) * (Kᴴ * L) =
      (Fintype.card n : ℂ) • (Hᴴ * L) := by
  calc
    (Hᴴ * K) * (Kᴴ * L) = Hᴴ * (K * Kᴴ) * L := by
      simp only [Matrix.mul_assoc]
    _ = Hᴴ *
        ((Fintype.card n : ℂ) • (1 : ComplexSquare n)) * L := by
      rw [hK.2]
    _ = (Fintype.card n : ℂ) • (Hᴴ * L) := by simp

/-- The three pairwise relative Grams of a Hadamard triple satisfy all cyclic
composition laws. -/
theorem relativeGram_triangle
    {n : Type*} [Fintype n] [DecidableEq n]
    (H : Fin 3 → ComplexSquare n)
    (hH : ∀ r, IsComplexHadamard (H r)) :
    ∀ a b c,
      ((H a)ᴴ * H b) * ((H b)ᴴ * H c) =
        (Fintype.card n : ℂ) • ((H a)ᴴ * H c) := by
  intro a b c
  exact relativeGram_cocycle (H a) (H b) (H c) (hH b)

/-- Every off-diagonal edge of a normalized four-MUB Hadamard witness is a
scaled complex Hadamard, and the edges obey the scaled cocycle law. -/
theorem fourMUBWitness_relativeGram_edges
    (w : FourMUBHadamardWitness) :
    (∀ a b, a ≠ b →
      (∀ i j,
        Complex.normSq (((w.matrix a)ᴴ * w.matrix b) i j) = 6) ∧
      ((w.matrix a)ᴴ * w.matrix b) *
          (((w.matrix a)ᴴ * w.matrix b)ᴴ) =
        (36 : ℂ) • (1 : Mat6)) ∧
    (∀ a b c,
      (((w.matrix a)ᴴ * w.matrix b) *
          ((w.matrix b)ᴴ * w.matrix c)) =
        (6 : ℂ) • ((w.matrix a)ᴴ * w.matrix c)) := by
  constructor
  · intro a b hab
    refine ⟨w.unbiased a b hab, ?_⟩
    simpa using
      relativeGram_mul_conjTranspose_eq_card_sq_smul
        (w.matrix a) (w.matrix b)
        (w.hadamard a) (w.hadamard b)
  · intro a b c
    simpa using
      relativeGram_cocycle
        (w.matrix a) (w.matrix b) (w.matrix c)
        (w.hadamard b)

#print axioms relativeGram_refl
#print axioms relativeGram_reverse
#print axioms relativeGram_cocycle
#print axioms relativeGram_triangle
#print axioms fourMUBWitness_relativeGram_edges

end D5.S3.Quantum.Tomography.ComplexHadamardRelativeGramCocycle
