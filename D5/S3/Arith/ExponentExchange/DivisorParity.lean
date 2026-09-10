/- GID: D5/S3/Arith/ExponentExchange/DivisorParity
   generality: G
   mirror-B: D5/B/S3/Arith/ExponentExchange/DivisorParity
   mirror-E: none(waiver:algebraically-proved)
   anchors: [mathlib/module/Mathlib.NumberTheory.ArithmeticFunction.Misc]
   utility: none
   digest: Prime-factor parity determines the commutation sign of divisor reflection. -/

import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.LinearAlgebra.Pi
import Mathlib.Data.Complex.Basic

/-!
Admission basis: rule-11-upstream-wrapper; proof_shape: bind-only.
Upstream: ArithmeticFunction.cardFactors_mul,
Mathlib/NumberTheory/ArithmeticFunction/Misc.lean:290,
at Mathlib db584cd6d46c92f209a44c0f1c829460d327499d (Lean v4.33.0).
Necessary atom clause (verbatim):
\Gamma R
=
(-1)^{\Omega(N)}R\Gamma.

The atom requires an equality of divisor operators; the upstream statement is
additivity of the prime-factor count. Extensionality, divisor cancellation,
pow_add and the square of a sign are the entire proof. No new lemma is needed.
The coefficient-space reflection is precomposition with d -> N/d. For N nonzero,
Nat.div_div_self makes this permutation involutive, so it sends |d> to |N/d>.
The nonzero premise makes every divisor and complementary divisor positive.
The repository prime-word reversal interfaces have a different carrier.
Direct frozen prerequisites: none. No finite enumeration is introduced.
Utility is none for Divisors (a symbolic type), factorParity and
complementReflection (symbolic linear maps), and the sole theorem (arbitrary N).
None is a bounded enumeration, certified instance, checker or numerical reduction.
-/

noncomputable section

open scoped ArithmeticFunction.Omega

namespace D5.S3.Arith.ExponentExchange.DivisorParity

/-- Divisors of N, positive whenever N is nonzero. -/
abbrev Divisors (N : ℕ) := {d : ℕ // d ∣ N}

/-- Diagonal prime-factor parity on divisor coefficients. -/
def factorParity (N : ℕ) : Module.End ℂ (Divisors N → ℂ) :=
  LinearMap.pi fun d => ((-1 : ℂ) ^ Ω d.val) • LinearMap.proj d

/-- Complementary-divisor reflection on coefficients. -/
def complementReflection (N : ℕ) : Module.End ℂ (Divisors N → ℂ) :=
  LinearMap.pi fun d => LinearMap.proj ⟨N / d.val, Nat.div_dvd_of_dvd d.property⟩

/-- The total prime-factor count controls the commutation sign. -/
theorem factor_parity_reflection (N : ℕ) (hN : N ≠ 0) :
    factorParity N * complementReflection N =
      ((-1 : ℂ) ^ Ω N) • (complementReflection N * factorParity N) := by
  ext f d
  change (-1 : ℂ) ^ Ω d.val * f ⟨N / d.val, Nat.div_dvd_of_dvd d.property⟩ =
    (-1 : ℂ) ^ Ω N *
      ((-1 : ℂ) ^ Ω (N / d.val) * f ⟨N / d.val, Nat.div_dvd_of_dvd d.property⟩)
  have hcount := ArithmeticFunction.cardFactors_mul
    (ne_zero_of_dvd_ne_zero hN d.property)
    (ne_zero_of_dvd_ne_zero hN (Nat.div_dvd_of_dvd d.property))
  rw [Nat.mul_div_cancel' d.property] at hcount
  rw [hcount, pow_add, mul_assoc, ← mul_assoc ((-1 : ℂ) ^ Ω (N / d.val)),
    ← mul_pow]
  simp

#print axioms factor_parity_reflection

end D5.S3.Arith.ExponentExchange.DivisorParity
