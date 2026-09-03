/- GID: D5/S3/Quantum/Tomography/ComplexHadamardCocycleGauge
   generality: G
   mirror-B: D5/B/S3/Quantum/Tomography/ComplexHadamardCocycleGauge
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Coherent vertex-unitary gauges preserve scaled relative-Gram cocycles and arise from right gauges on Hadamard representatives. -/

import D5.S3.Quantum.Tomography.ComplexHadamardRelativeGramCocycle

/- Library-search audit trail (2026-09-03):
   * Reuses `ComplexSquare` and the relative-Gram cocycle.
   * Reuses matrix conjugate transpose and associativity.
   * This module proves only cocycle covariance. Entrywise flatness under
     monomial gauges remains the responsibility of the existing
     `HadamardEquivalent` interface.
-/

open scoped BigOperators Matrix

noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Tomography.ComplexHadamardCocycleGauge

open Matrix
open D5.S3.Quantum.Tomography.MUBHadamardCompatibility
open D5.S3.Quantum.Tomography.ComplexHadamardRelativeGramCocycle

/-- Right vertex gauges on Hadamard representatives induce the coherent
left/right action on every relative Gram edge. -/
theorem relativeGram_right_vertexGauge
    {v n : Type*} [Fintype n]
    (H M : v → ComplexSquare n)
    (a b : v) :
    ((H a * M a)ᴴ * (H b * M b)) =
      (M a)ᴴ * ((H a)ᴴ * H b) * M b := by
  rw [Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]

/-- A coherent vertex-unitary gauge preserves every scaled cocycle equation.
The middle vertex gauge cancels exactly. -/
theorem scaledCocycle_vertexGauge
    {v n : Type*} [Fintype n]
    (G : v → v → ComplexSquare n)
    (M : v → ComplexSquare n)
    (scale : ℂ)
    (hM : ∀ b, M b * (M b)ᴴ = (1 : ComplexSquare n))
    (hCocycle : ∀ a b c,
      G a b * G b c = scale • G a c) :
    ∀ a b c,
      (((M a)ᴴ * G a b) * M b) *
          (((M b)ᴴ * G b c) * M c) =
        scale • (((M a)ᴴ * G a c) * M c) := by
  intro a b c
  calc
    (((M a)ᴴ * G a b) * M b) *
        (((M b)ᴴ * G b c) * M c) =
      (M a)ᴴ * (G a b * (M b * (M b)ᴴ) * G b c) * M c := by
        simp only [Matrix.mul_assoc]
    _ = (M a)ᴴ * (G a b * G b c) * M c := by
      rw [hM b]
      simp
    _ = (M a)ᴴ * (scale • G a c) * M c := by
      rw [hCocycle a b c]
    _ = scale • (((M a)ᴴ * G a c) * M c) := by simp

/-- The scaled relative-Gram cocycle of a Hadamard family remains a cocycle
after any coherent unitary right gauge on its vertices. -/
theorem relativeGram_cocycle_after_vertexGauge
    {v n : Type*} [Fintype n] [DecidableEq n]
    (H M : v → ComplexSquare n)
    (hH : ∀ b, IsComplexHadamard (H b))
    (hM : ∀ b, M b * (M b)ᴴ = (1 : ComplexSquare n)) :
    ∀ a b c,
      ((((H a * M a)ᴴ) * (H b * M b)) *
          (((H b * M b)ᴴ) * (H c * M c))) =
        (Fintype.card n : ℂ) •
          (((H a * M a)ᴴ) * (H c * M c)) := by
  intro a b c
  rw [relativeGram_right_vertexGauge H M a b]
  rw [relativeGram_right_vertexGauge H M b c]
  rw [relativeGram_right_vertexGauge H M a c]
  exact scaledCocycle_vertexGauge
    (fun x y ↦ (H x)ᴴ * H y) M (Fintype.card n : ℂ)
    hM (fun x y z ↦ relativeGram_cocycle
      (H x) (H y) (H z) (hH y)) a b c

#print axioms relativeGram_right_vertexGauge
#print axioms scaledCocycle_vertexGauge
#print axioms relativeGram_cocycle_after_vertexGauge

end D5.S3.Quantum.Tomography.ComplexHadamardCocycleGauge
