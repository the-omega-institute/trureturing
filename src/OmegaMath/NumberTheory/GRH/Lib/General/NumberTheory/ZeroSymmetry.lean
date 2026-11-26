import OmegaMath.NumberTheory.GRH.Lib.General.Algebra.SumOverUnits
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! General lemmas of algebraic number theory (textbook or folklore).

This file: Symmetry of zeros of Dirichlet L-functions from the functional equation, imprimitive
characters included. -/

open Complex DirichletCharacter CharZero Nat.Prime
variable {N} [NeZero N] (χ : DirichletCharacter ℂ N)

omit [NeZero N] in
/-- For a Dirichlet character χ, a natural number M and Re s ≠ 0, the product of the Euler
factors 1 − χ(p)p^{−s} over the primes p dividing M is not zero. -/
lemma prod_euler_factor_ne_zero {M : ℕ} {s : ℂ} (h0 : s.re ≠ 0) :
    ∏ p ∈ M.primeFactors, (1 - χ p * p ^ (-s)) ≠ 0 := Finset.prod_ne_zero_iff.2 fun p h e ↦ by
  obtain := congr(Real.logb p ‖$(χ.star_apply' p)‖), show χ p = p ^ s by grind [cpow_neg]
  simp_all [norm_natCast_cpow_of_pos, χ.inv_apply_eq_inv', pos, ne_one]

/-- Every complex Dirichlet character χ mod N, with N ≥ 1, is induced by a primitive character ψ
mod M for some divisor M ≥ 1 of N. -/
lemma exists_isPrimitive_changeLevel_eq : ∃ M f ψ, NeZero M ∧ IsPrimitive ψ ∧
  changeLevel (f : M ∣ N) ψ = χ := ⟨_,
  _, _, ⟨χ.conductor_ne_zero⟩, χ.primitiveCharacter_isPrimitive, χ.changeLevel_primitiveCharacter⟩

/-- Symmetry of the zeros: if L(s, χ) = 0, re s ≠ 0 and s ≠ 1, then either s is a pole of the
gamma factor of χ (where Mathlib gives it the value 0), or L(1 − s, χ⁻¹) = 0. -/
lemma LFunction_one_sub_eq_zero s (h0 : s.re ≠ 0) (h1 : s ≠ 1)
    (hs : LFunction χ s = 0) : χ.gammaFactor s = 0 ∨ LFunction χ⁻¹ (1 - s) = 0 := by
  obtain ⟨M, f, ψ, _, h, rfl⟩ := exists_isPrimitive_changeLevel_eq χ
  have := ψ.changeLevel_eq_cast_of_dvd f (-1)
  simp_all [LFunction_changeLevel, ← map_inv, gammaFactor, prod_euler_factor_ne_zero, s.ext_iff,
    @LFunction_eq_completed_div_gammaFactor M, @eq_comm ℂ 1, DirichletCharacter.Even,
    IsPrimitive.completedLFunction_one_sub (ψ.conductor_inv.trans h)]; lia
