/- GID: D5/S3/Arith/ModularForms/GeneralDirichletGaussNorm
   generality: G
   mirror-B: none(waiver:general-dirichlet-gauss-fourier-bridge)
   mirror-E: none(waiver:general-dirichlet-gauss-fourier-bridge)
   anchors: []
   utility: none
   digest: Primitive Dirichlet characters at arbitrary nonzero modulus have Gauss norm square equal to the modulus. -/

module

public import Mathlib.Analysis.Fourier.ZMod

/-!
# General primitive Dirichlet Gauss norm

The finite Fourier inversion identity for `ZMod N` extends the primitive Dirichlet
Gauss norm formula from prime moduli to every nonzero modulus.
-/

open AddChar MulChar
open scoped ZMod BigOperators

namespace D5.S3.Arith.ModularForms

noncomputable section

variable {N : ℕ} [NeZero N]

/-- Fourier inversion evaluates the primitive Gauss product at the negative unit. -/
theorem primitive_gauss_product_fourier
    (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive) :
    gaussSum χ (ZMod.stdAddChar (N := N)) *
      gaussSum χ⁻¹ (ZMod.stdAddChar (N := N))⁻¹ = (N : ℂ) := by
  have hF : 𝓕 χ = fun k : ZMod N => χ⁻¹ (-k) * gaussSum χ (ZMod.stdAddChar (N := N)) := by
    funext k
    exact DirichletCharacter.IsPrimitive.fourierTransform_eq_inv_mul_gaussSum hχ k
  have hdouble := congr_fun (ZMod.dft_dft χ) (-1 : ZMod N)
  rw [hF] at hdouble
  rw [ZMod.dft_apply] at hdouble
  simp only [smul_eq_mul] at hdouble
  have hsum :
      (∑ x : ZMod N,
        ZMod.stdAddChar (-(x * (-1 : ZMod N))) *
          (χ⁻¹ (-x) * gaussSum χ (ZMod.stdAddChar (N := N)))) =
        gaussSum χ (ZMod.stdAddChar (N := N)) *
          gaussSum χ⁻¹ (ZMod.stdAddChar (N := N))⁻¹ := by
    calc
      _ = ∑ x : ZMod N,
          ZMod.stdAddChar x *
            (χ⁻¹ (-x) * gaussSum χ (ZMod.stdAddChar (N := N))) := by
        apply Finset.sum_congr rfl
        intro x _
        congr 1
        ring
      _ = gaussSum χ (ZMod.stdAddChar (N := N)) *
          ∑ x : ZMod N, χ⁻¹ (-x) * ZMod.stdAddChar x := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _
        ring
      _ = gaussSum χ (ZMod.stdAddChar (N := N)) *
          ∑ x : ZMod N, χ⁻¹ x * ZMod.stdAddChar (-x) := by
        congr 1
        simpa only [Equiv.neg_apply, neg_neg] using
          (Equiv.sum_comp (Equiv.neg (ZMod N))
            (fun x : ZMod N => χ⁻¹ x * ZMod.stdAddChar (-x)))
      _ = _ := by
        simp only [gaussSum, AddChar.inv_apply]
  rw [hsum] at hdouble
  simpa [ZMod.card] using hdouble

/-- Primitive Dirichlet characters have Gauss norm square equal to the modulus. -/
theorem primitive_dirichlet_gauss_normSq_general
    (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive) :
    Complex.normSq (gaussSum χ (ZMod.stdAddChar (N := N))) = N := by
  have hprod := primitive_gauss_product_fourier χ hχ
  have hstar := star_gaussSum_eq χ (ZMod.stdAddChar (N := N))
  have hnorm :
      (Complex.normSq (gaussSum χ (ZMod.stdAddChar (N := N))) : ℂ) =
        gaussSum χ (ZMod.stdAddChar (N := N)) *
          star (gaussSum χ (ZMod.stdAddChar (N := N))) := by
    rw [Complex.star_def]
    exact (Complex.mul_conj _).symm
  rw [← hstar] at hprod
  have hc := hnorm.trans hprod
  simpa [ZMod.card] using congrArg Complex.re hc

end
end D5.S3.Arith.ModularForms
