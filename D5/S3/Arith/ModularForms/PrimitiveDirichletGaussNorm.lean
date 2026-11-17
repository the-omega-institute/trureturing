/- GID: D5/S3/Arith/ModularForms/PrimitiveDirichletGaussNorm
   generality: G
   mirror-B: D5/B/S3/Arith/ModularForms/PrimitiveDirichletGaussNorm
   mirror-E: none(waiver:primitive-dirichlet-gauss-bridge)
   anchors: []
   utility: none
   digest: Primitive Dirichlet characters modulo a prime have Gauss norm square equal to the prime. -/

import Mathlib.NumberTheory.DirichletCharacter.GaussSum
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar

/-!
# Primitive Dirichlet Gauss norm

This file bridges primitive Dirichlet characters modulo a prime to the
finite-field Gauss-sum magnitude identity used by primitive modular twists.
-/

open AddChar MulChar

namespace D5.S3.Arith.ModularForms

noncomputable section

/-- A primitive Dirichlet character modulo a prime has Gauss sum of squared
complex modulus equal to the prime.  This is the coefficient-normalization
bridge needed by primitive twists of modular forms. -/
theorem primitive_dirichlet_gauss_normSq
    {p : ℕ} [NeZero p] (hp : p.Prime) (χ : DirichletCharacter ℂ p)
    (hχ : χ.IsPrimitive) :
    Complex.normSq (gaussSum χ (ZMod.stdAddChar (N := p))) = p := by
  letI : Fact p.Prime := ⟨hp⟩
  have hχ_ne : χ ≠ 1 := by
    intro h
    have hc : χ.conductor = 1 :=
      (DirichletCharacter.eq_one_iff_conductor_eq_one).1 h
    have hp1 : p = 1 := hχ.symm.trans hc
    exact hp.ne_one hp1
  have hψ : AddChar.IsPrimitive (ZMod.stdAddChar (N := p)) :=
    ZMod.isPrimitive_stdAddChar p
  have hprod := gaussSum_mul_gaussSum_eq_card hχ_ne hψ
  have hstar := star_gaussSum_eq χ (ZMod.stdAddChar (N := p))
  have hnorm :
      (Complex.normSq (gaussSum χ (ZMod.stdAddChar (N := p))) : ℂ) =
        gaussSum χ (ZMod.stdAddChar (N := p)) *
          star (gaussSum χ (ZMod.stdAddChar (N := p))) := by
    rw [Complex.star_def]
    exact (Complex.mul_conj _).symm
  rw [← hstar] at hprod
  have hc := hnorm.trans hprod
  simpa [ZMod.card] using congrArg Complex.re hc

end

end D5.S3.Arith.ModularForms
