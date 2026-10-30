/- GID: D5/S3/Arith/CharacterSums/PrimitiveGaussSum
   generality: G
   mirror-B: D5/B/S3/Arith/CharacterSums/PrimitiveGaussSum
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Nonzero primitive Gauss sums follow from Fourier injectivity. -/

import Mathlib.Analysis.Fourier.ZMod

open scoped BigOperators

namespace D5.S3.Arith.CharacterSums

noncomputable section

/-- A primitive Dirichlet character has a nonzero Gauss sum for the standard
additive character.  The proof isolates the analytic input in the Fourier
transform formula and finishes by injectivity of the finite Fourier transform. -/
theorem primitive_gaussSum_ne_zero
    {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N}
    (hχ : χ.IsPrimitive) :
    gaussSum χ (ZMod.stdAddChar (N := N)) ≠ 0 := by
  intro hτ
  have hF : ZMod.dft (χ : ZMod N → ℂ) = 0 := by
    funext k
    rw [hχ.fourierTransform_eq_inv_mul_gaussSum]
    simp [hτ]
  have hzero : (χ : ZMod N → ℂ) = 0 := by
    apply ZMod.dft.injective
    simpa using hF
  have hone : (1 : ℂ) = 0 := by
    simpa using congrFun hzero (1 : ZMod N)
  exact one_ne_zero hone

end
end D5.S3.Arith.CharacterSums
