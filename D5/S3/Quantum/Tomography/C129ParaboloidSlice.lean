/- GID: D5/S3/Quantum/Tomography/C129ParaboloidSlice
   generality: G
   mirror-B: D5/B/S3/Quantum/Tomography/C129ParaboloidSlice
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The two-by-two positive region is a paraboloid with a nonnegative orthogonal residual. -/

import Mathlib

open scoped BigOperators ComplexOrder InnerProductSpace Matrix

noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Tomography.C129ParaboloidSlice

/-- The scalar positivity conditions for a Hermitian two-by-two Gram block. -/
def twoByTwoPositive (p q : ℝ) (b : ℂ) : Prop :=
  0 ≤ p ∧ 0 ≤ q ∧ Complex.normSq b ≤ p * q

/-- The Schur residual above the old one-dimensional direction. -/
def residual (p q : ℝ) (b : ℂ) : ℝ :=
  q - Complex.normSq b / p

/-- The real coordinate of the new cross term after normalizing the old diagonal. -/
def xCoord (p : ℝ) (b : ℂ) : ℝ :=
  b.re / Real.sqrt p

/-- The imaginary coordinate of the new cross term after normalizing the old diagonal. -/
def yCoord (p : ℝ) (b : ℂ) : ℝ :=
  b.im / Real.sqrt p

/--
For a positive old diagonal, the two-by-two positive region is exactly the
nonnegative Schur residual, and its scalar coordinates lie on the paraboloid
`q = x^2 + y^2 + residual`.  At a zero old diagonal, positivity forces the
cross term to vanish while retaining a nonnegative new diagonal.
-/
theorem paraboloid_slice (p q : ℝ) (b : ℂ) :
    (0 < p →
      (twoByTwoPositive p q b ↔ 0 ≤ residual p q b) ∧
      q = xCoord p b ^ 2 + yCoord p b ^ 2 + residual p q b) ∧
    (p = 0 → twoByTwoPositive p q b → b = 0 ∧ 0 ≤ q) := by
  constructor
  · intro hp
    constructor
    · rw [twoByTwoPositive, residual]
      have hp0 : p ≠ 0 := ne_of_gt hp
      constructor
      · rintro ⟨_, hq, hdet⟩
        have hdiv : Complex.normSq b / p ≤ q :=
          (div_le_iff₀ hp).mpr (by nlinarith)
        linarith
      · intro h
        have hdiv : Complex.normSq b / p ≤ q := by linarith
        have hmul : Complex.normSq b ≤ q * p :=
          (div_le_iff₀ hp).mp hdiv
        exact ⟨hp.le, by
          have hnorm : 0 ≤ Complex.normSq b := Complex.normSq_nonneg b
          nlinarith, by nlinarith⟩
    · rw [xCoord, yCoord, residual]
      have hp0 : p ≠ 0 := ne_of_gt hp
      have hsqrt : Real.sqrt p ^ 2 = p := Real.sq_sqrt hp.le
      have hnorm : Complex.normSq b = b.re ^ 2 + b.im ^ 2 := by
        rw [Complex.normSq_apply]
        ring
      rw [hnorm]
      field_simp [hp0]
      nlinarith
  · intro hp0 hpos
    rcases hpos with ⟨_, hq, hdet⟩
    have hnorm_zero : Complex.normSq b = 0 := by
      have hnonneg : 0 ≤ Complex.normSq b := Complex.normSq_nonneg b
      simpa [hp0] using (le_antisymm (by nlinarith) hnonneg)
    exact ⟨Complex.normSq_eq_zero.mp hnorm_zero, hq⟩

#print axioms twoByTwoPositive
#print axioms residual
#print axioms xCoord
#print axioms yCoord
#print axioms paraboloid_slice

end D5.S3.Quantum.Tomography.C129ParaboloidSlice
