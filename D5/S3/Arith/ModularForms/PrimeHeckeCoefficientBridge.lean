/- GID: D5/S3/Arith/ModularForms/PrimeHeckeCoefficientBridge
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:registration-audit-pending)
   anchors: []
   utility: none
   digest: Outward coefficient and finite Fourier bridges for prime Hecke and primitive twists. -/

import D5.S3.Arith.ModularForms.ActualPrimeHecke
import D5.S3.Arith.ModularForms.PrimitiveDirichletTwistMatrix

open UpperHalfPlane ModularForm ModularFormClass MatrixGroups
open scoped BigOperators ModularForm MatrixGroups CongruenceSubgroup Pointwise

namespace D5.S3.Arith.ModularForms

noncomputable section

/-- A normalized prime-Hecke eigenform has eigenvalue equal to its `p`-th q-expansion coefficient.

This is the outward Fourier-coefficient bridge for the actual analytic Hecke operator. -/
theorem primeHecke_eigenvalue_eq_qExpansion_coeff
    (p : ℕ) [Fact p.Prime] (k : ℤ) (f : CuspForm 𝒮ℒ k)
    (hnorm : (qExpansion 1 f).coeff 1 = 1) {lam : ℂ}
    (heig : primeHecke p k f = lam • f) :
    lam = (qExpansion 1 f).coeff p := by
  have hp₁ : ¬ p ∣ 1 := (Fact.out : Nat.Prime p).not_dvd_one
  have h := primeHecke_qExpansion_coeff p k f 1
  rw [heig, FunLike.coe_smul,
      ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL lam f,
      PowerSeries.coeff_smul, smul_eq_mul, hnorm] at h
  simpa [hp₁] using h

/-- The finite Fourier weight in the primitive twist is the character value times its
Gauss sum.  This is the algebraic half of the future q-expansion coefficient theorem. -/
theorem primitive_inv_gauss_weight
    (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ.IsPrimitive) (n : ℕ) :
    ∑ u : ZMod N, (χ⁻¹ u) * ZMod.stdAddChar ((n : ZMod N) * u) =
      χ (n : ZMod N) * gaussSum χ⁻¹ (ZMod.stdAddChar (N := N)) := by
  have hχi : (χ⁻¹).IsPrimitive := by
    simpa [DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_inv] using hχ
  simpa [gaussSum, AddChar.mulShift_apply, inv_inv] using
    (gaussSum_mulShift_of_isPrimitive
      (e := ZMod.stdAddChar (N := N)) hχi (n : ZMod N))

end

end D5.S3.Arith.ModularForms

#print axioms D5.S3.Arith.ModularForms.primeHecke_eigenvalue_eq_qExpansion_coeff
#print axioms D5.S3.Arith.ModularForms.primitive_inv_gauss_weight
