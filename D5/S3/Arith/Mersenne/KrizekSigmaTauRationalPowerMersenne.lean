/- GID: D5/S3/Arith/Mersenne/KrizekSigmaTauRationalPowerMersenne
   generality: I
   mirror-B: D5/B/S3/Arith/Mersenne/KrizekSigmaTauRationalPowerMersenne
   mirror-E: none(waiver:symbolic-proof-no-numeric-artifact)
   anchors: [mathlib/module/Mathlib.FieldTheory.Finite.Basic, mathlib/module/Mathlib.NumberTheory.ArithmeticFunction.Misc, mathlib/module/Mathlib.NumberTheory.Multiplicity, mathlib/module/Mathlib.Tactic.NormNum, mathlib/module/Mathlib.Tactic.Ring]
   utility: none
   digest: Krizek's sigma-tau rational powers are exactly squarefree Mersenne-prime products. -/

import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Multiplicity
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ring

namespace D5.S3.Arith.Mersenne.KrizekSigmaTauRationalPowerMersenne

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Products of distinct primes one less than a positive power of two. -/
def isMersenneProduct (n : ℕ) : Prop :=
  ∃ S : Finset ℕ,
    n = ∏ p ∈ S, p ∧
      ∀ p ∈ S, p.Prime ∧ ∃ k : ℕ, 0 < k ∧ p + 1 = 2 ^ k

/-- The integer-power form of `sigma(n) = tau(n)^(a/b)`. -/
def ratPow (n : ℕ) : Prop :=
  ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ (σ 1 n) ^ b = (σ 0 n) ^ a

private theorem prime_support_eq_of_pow_eq_pow {x y a b : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hpow : x ^ b = y ^ a) (r : ℕ) (hr : r.Prime) :
    r ∣ x ↔ r ∣ y := by
  constructor
  · intro hx
    apply hr.dvd_of_dvd_pow
    rw [← hpow]
    exact hx.trans (dvd_pow (dvd_refl x) hb.ne')
  · intro hy
    apply hr.dvd_of_dvd_pow
    rw [hpow]
    exact hy.trans (dvd_pow (dvd_refl y) ha.ne')

#print axioms isMersenneProduct
#print axioms ratPow

end D5.S3.Arith.Mersenne.KrizekSigmaTauRationalPowerMersenne
