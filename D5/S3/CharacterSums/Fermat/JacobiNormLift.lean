/- GID: D5/S3/CharacterSums/Fermat/JacobiNormLift
   generality: G
   mirror-B: D5/B/S3/CharacterSums/Fermat/JacobiNormLift
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Negative Jacobi sums lift by finite-field norm and trace pullback.
-/

import D5.S3.Arith.CharacterSums.LanglandsFirstMainLemma.FiniteField.HasseDavenportLift
import Mathlib.NumberTheory.JacobiSum.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open scoped BigOperators

namespace D5.S3.CharacterSums.Fermat.JacobiNormLift

open LanglandsFirstMainLemma

private theorem normMulChar_mul
    {k K : Type*} [Field k] [Field K] [Finite K] [Algebra k K]
    (χ φ : FiniteMulChar k) :
    normMulChar k K (χ * φ) = normMulChar k K χ * normMulChar k K φ := by
  ext x
  simp [normMulChar]

private theorem normMulChar_inv_inv
    {k K : Type*} [Field k] [Field K] [Finite K] [Algebra k K]
    (χ : FiniteMulChar k) :
    (normMulChar k K χ⁻¹)⁻¹ = normMulChar k K χ := by
  rw [normMulChar_inv]
  simp

private theorem negative_gauss_norm_lift
    {k K : Type*} [Field k] [Fintype k] [Field K] [Fintype K] [Algebra k K]
    (χ : FiniteMulChar k) (ψ : FiniteAddChar k) (hψ : ψ ≠ 1) :
    -gaussSum (normMulChar k K χ) (traceAddChar k K ψ) =
      (-gaussSum χ ψ) ^ Module.finrank k K := by
  have h := hasseDavenportLift (k := k) (K := K) (χ := χ⁻¹) ψ hψ
  simpa [langlandsGaussSum, normMulChar_inv_inv] using h

/-- Davenport--Hasse's extension-field identity in the Jacobi normalization.

The negative sign is essential: ordinary Jacobi sums satisfy
`J_K = (-1)^(r-1) J_k^r`, while the displayed form is uniform in the
extension degree and is the form that enters diagonal point counts.
-/
theorem neg_jacobiSum_norm_lift
    {k K : Type*} [Field k] [Fintype k] [Field K] [Fintype K] [Algebra k K]
    (χ φ : FiniteMulChar k) (ψ : FiniteAddChar k)
    (hψ : ψ ≠ 1) (hχφ : χ * φ ≠ 1) :
    -jacobiSum (normMulChar k K χ) (normMulChar k K φ) =
      (-jacobiSum χ φ) ^ Module.finrank k K := by
  let χK := normMulChar k K χ
  let φK := normMulChar k K φ
  let ψK := traceAddChar k K ψ
  have hχφK : χK * φK ≠ 1 := by
    rw [show χK * φK = normMulChar k K (χ * φ) by
      dsimp [χK, φK]
      exact normMulChar_mul χ φ]
    exact (normMulChar_ne_one_iff k K (χ * φ)).mpr hχφ
  have hχφK' : normMulChar k K χ * normMulChar k K φ ≠ 1 := by
    simpa [χK, φK] using hχφK
  have hψK : ψK ≠ 1 :=
    (traceAddChar_ne_one_iff k K ψ).mpr hψ
  have hcardK : (Fintype.card K : ℂ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card K ≠ 0)
  have hcardk : (Fintype.card k : ℂ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card k ≠ 0)
  have hJ_K := jacobiSum_eq_gaussSum_mul_gaussSum_div_gaussSum
    (F := K) (F' := ℂ) hcardK hχφK' (AddChar.IsPrimitive.of_ne_one hψK)
  have hJ_k := jacobiSum_eq_gaussSum_mul_gaussSum_div_gaussSum
    (F := k) (F' := ℂ) hcardk hχφ (AddChar.IsPrimitive.of_ne_one hψ)
  have hχ := negative_gauss_norm_lift χ ψ hψ
  have hφ := negative_gauss_norm_lift φ ψ hψ
  have hprodLift := negative_gauss_norm_lift (χ * φ) ψ hψ
  have hJ_K_neg :
      -jacobiSum χK φK =
        (-gaussSum χK ψK) * (-gaussSum φK ψK) /
          (-gaussSum (χK * φK) ψK) := by
    rw [hJ_K]
    ring
  have hJ_k_neg :
      -jacobiSum χ φ =
        (-gaussSum χ ψ) * (-gaussSum φ ψ) /
          (-gaussSum (χ * φ) ψ) := by
    rw [hJ_k]
    ring
  rw [hJ_K_neg, hJ_k_neg]
  rw [show χK = normMulChar k K χ by rfl,
    show φK = normMulChar k K φ by rfl,
    show ψK = traceAddChar k K ψ by rfl,
    hχ, hφ]
  have hprodLift' :
      -gaussSum (normMulChar k K (χ * φ)) (traceAddChar k K ψ) =
        (-gaussSum (χ * φ) ψ) ^ Module.finrank k K := hprodLift
  rw [show normMulChar k K χ * normMulChar k K φ = normMulChar k K (χ * φ) by
    exact (normMulChar_mul χ φ).symm, hprodLift']
  rw [div_pow, mul_pow]

end D5.S3.CharacterSums.Fermat.JacobiNormLift
