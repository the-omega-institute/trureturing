/- GID: D5/S3/Arith/PrimitiveRoot/Erdos985
   generality: I
   mirror-B: D5/B/S3/Arith/PrimitiveRoot/Erdos985
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Erdős #985 under finite-height Dirichlet zero exclusion with an
   unconditional principal term and a kernel-certified finite range. -/

import D5.S3.Arith.PrimitiveRoot.SieveThresholdUnconditional
import D5.S3.Arith.PrimitiveRoot.PrincipalTriangleLower
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.FiniteRangeExtended
import D5.S3.CharacterSums.DirichletTriangleBound
import D5.S3.CharacterSums.DirichletTrianglePerron
import D5.S3.Weil.Mertens.IntegratedExplicit.TriangleRampZeta

/-! Conditional prime primitive roots from triangular character estimates. -/

namespace D5.S3.Arith.PrimitiveRoot.Erdos985

open scoped BigOperators
open Complex
open D5.S3.Arith.PrimitiveRoot.CharacterSieve
open D5.S3.Arith.PrimitiveRoot.SieveThresholdUnconditional
open D5.S3.Arith.PrimitiveRoot.PrincipalTriangleLower
open D5.S3.CharacterSums.DirichletTriangleBound
open D5.S3.CharacterSums.DirichletTrianglePerron
open D5.S3.Weil.Mertens.IntegratedExplicit.TriangleRampZeta

/-- A nonprincipal character modulo a prime has conductor equal to that prime. -/
private theorem isPrimitive_of_prime_of_ne_one {p : ℕ} [Fact p.Prime]
    [NeZero p] (χ : DirichletCharacter ℂ p) (hχ : χ ≠ 1) : χ.IsPrimitive := by
  rw [DirichletCharacter.isPrimitive_def]
  rcases (Nat.dvd_prime (Fact.out : p.Prime)).mp χ.conductor_dvd_level with h | h
  · exact False.elim (hχ ((DirichletCharacter.eq_one_iff_conductor_eq_one).mpr h))
  · exact h

/-- The large-prime part under the weakest finite-height zero exclusion used by
the triangular estimate. -/
theorem erdos985_large_prime (p : ℕ) [Fact p.Prime] (hp : 5000000 ≤ p)
    (hL : ∀ χ : DirichletCharacter ℂ p, χ ≠ 1 →
      orderOf χ ∣ ∏ r ∈ (p - 1).primeFactors, r →
      ∀ s : ℂ, 1 / 2 < s.re → |s.im| ≤ 4 * Real.sqrt p → χ.LFunction s ≠ 0) :
    ∃ q : ℕ, q.Prime ∧ q < p ∧ orderOf (q : ZMod p) = p - 1 := by
  let : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  apply exists_prime_primitiveRoot p hp
  · intro χ hχ horder
    have hprim : χ.IsPrimitive := isPrimitive_of_prime_of_ne_one χ hχ
    have hbound := characterTriangle_prime_bound p χ hprim (by omega)
      (hL χ hχ horder)
    rw [← characterTriangle_nat p χ]
    have hre := (abs_re_le_norm (characterTriangle χ p)).trans hbound
    have hnonneg : 0 ≤ 1 / (p : ℝ) := by positivity
    linarith
  · exact principal_smoothedCharacterSum_large (Fact.out : p.Prime) hp

/-- Conditional Erdős #985, including the kernel-certified finite prime range. -/
theorem erdos985_of_finiteHeight
    (hL : ∀ (p : ℕ) (hp : p.Prime),
      letI : NeZero p := ⟨hp.ne_zero⟩;
      5000000 ≤ p → ∀ χ : DirichletCharacter ℂ p, χ ≠ 1 →
      orderOf χ ∣ ∏ r ∈ (p - 1).primeFactors, r →
      ∀ s : ℂ, 1 / 2 < s.re → |s.im| ≤ 4 * Real.sqrt p → χ.LFunction s ≠ 0) :
    ∀ p, p.Prime → p ≠ 2 →
      ∃ q, q.Prime ∧ q < p ∧ orderOf (q : ZMod p) = p - 1 := by
  intro p hp hne
  by_cases hlarge : 5000000 ≤ p
  · let : Fact p.Prime := ⟨hp⟩
    exact erdos985_large_prime p hlarge (hL p hp hlarge)
  · have hp2 := hp.two_le
    exact SmallPrimes.small_prime_primitiveRoot_extended p (by omega) (by omega) hp

#print axioms erdos985_large_prime
#print axioms erdos985_of_finiteHeight

end D5.S3.Arith.PrimitiveRoot.Erdos985
