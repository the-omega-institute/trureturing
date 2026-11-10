/- GID: D5/S3/Arith/CharacterSums/SexticGaussNorm
   generality: G
   mirror-B: D5/B/S3/Arith/CharacterSums/SexticGaussNorm
   mirror-E: none(waiver:open-sextic-equidistribution)
   anchors: []
   utility: none
   digest: Order-six Gauss sums have norm square equal to the field cardinality. -/

import Mathlib.NumberTheory.GaussSum

/-!
This file isolates the pointwise unit-circle constraint for order-six Gauss
sums. It is the algebraic prerequisite for the open family-level phase
equidistribution conjecture, rather than a claim of equidistribution itself.
-/

open AddChar MulChar

namespace D5.S3.Arith.CharacterSums

noncomputable section

/-- The squared complex modulus of a primitive order-six Gauss sum is the
cardinality of the finite field.  This is the unit-circle input needed before
any family-level equidistribution argument. -/
theorem sextic_gauss_normSq {F : Type*} [Field F] [Fintype F]
    (χ : MulChar F ℂ) (hχ : orderOf χ = 6)
    {ψ : AddChar F ℂ} (hψ : IsPrimitive ψ) :
    Complex.normSq (gaussSum χ ψ) = Fintype.card F := by
  have hn : χ ≠ 1 := by
    intro h
    subst χ
    norm_num at hχ
  have hprod := gaussSum_mul_gaussSum_eq_card hn hψ
  have hstar := star_gaussSum_eq χ ψ
  have hnorm : (Complex.normSq (gaussSum χ ψ) : ℂ) =
      gaussSum χ ψ * star (gaussSum χ ψ) := by
    rw [Complex.star_def]
    exact (Complex.mul_conj _).symm
  rw [← hstar] at hprod
  have hc := hnorm.trans hprod
  simpa using congrArg Complex.re hc

/-- The square of the normalized sextic Gauss sum lies on the unit circle.
This is the exact pointwise constraint behind the family-level phase
equidistribution conjecture; it does not assert equidistribution. -/
theorem sextic_gauss_square_div_card_normSq {F : Type*} [Field F] [Fintype F]
    (χ : MulChar F ℂ) (hχ : orderOf χ = 6)
    {ψ : AddChar F ℂ} (hψ : IsPrimitive ψ) :
    Complex.normSq
        ((gaussSum χ ψ) ^ 2 / (Fintype.card F : ℂ)) = 1 := by
  have hcard : (Fintype.card F : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero (α := F))
  have hcardC : (Fintype.card F : ℂ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero (α := F))
  rw [Complex.normSq_div, pow_two, Complex.normSq_mul, sextic_gauss_normSq χ hχ hψ,
    Complex.normSq_natCast]
  norm_num [hcard, hcardC]

end

end D5.S3.Arith.CharacterSums
