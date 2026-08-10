/- GID: D5/S3/Factorization/FreeCommMonoid
   generality: G
   mirror-B: D5/B/S3/Factorization/FreeCommMonoid
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Positive naturals under multiplication form the free commutative monoid on the primes. -/

import Mathlib.Data.PNat.Factors
import Mathlib.Data.Nat.Factorization.Defs

/- Provenance: Monoid-isomorphism and universal-property upgrade over pinned
   mathlib factorization API (`PNat.factorMultisetEquiv`, `PNat.factorMultiset_mul`,
   `Nat.factorization_mul`). -/

namespace D5.S3.Factorization

open Multiplicative

/--
Freeness witness: prime factorization is a monoid isomorphism from the
positive naturals under multiplication to the multiset monoid over the
primes written multiplicatively.  The underlying equivalence is mathlib's
`PNat.factorMultisetEquiv`; multiplicativity is `PNat.factorMultiset_mul`.
-/
def primeFactorMulEquiv : ℕ+ ≃* Multiplicative (Multiset Nat.Primes) :=
  { (PNat.factorMultisetEquiv : ℕ+ ≃ Multiset Nat.Primes).trans Multiplicative.ofAdd with
    map_mul' := fun m n => by
      change ofAdd ((PNat.factorMultisetEquiv : ℕ+ ≃ Multiset Nat.Primes) (m * n)) =
        ofAdd ((PNat.factorMultisetEquiv : ℕ+ ≃ Multiset Nat.Primes) m) *
          ofAdd ((PNat.factorMultisetEquiv : ℕ+ ≃ Multiset Nat.Primes) n)
      rw [← ofAdd_add]
      exact congrArg ofAdd (PNat.factorMultiset_mul m n) }

/--
The canonical extension of a prime-indexed family in a commutative monoid to
a monoid homomorphism out of the multiplicatively written multiset monoid on
the primes: map the primes of the multiset and take the product.
-/
def primeLift {M : Type*} [CommMonoid M] (f : Nat.Primes → M) :
    Multiplicative (Multiset Nat.Primes) →* M where
  toFun s := ((toAdd s).map f).prod
  map_one' := by simp
  map_mul' s t := by
    change (((toAdd s + toAdd t : Multiset Nat.Primes)).map f).prod = _
    rw [Multiset.map_add, Multiset.prod_add]

@[simp] theorem primeLift_ofAdd_singleton {M : Type*} [CommMonoid M]
    (f : Nat.Primes → M) (p : Nat.Primes) :
    primeLift f (ofAdd ({p} : Multiset Nat.Primes)) = f p := by
  change ((({p} : Multiset Nat.Primes)).map f).prod = f p
  simp

/-- The extension along the prime generators is unique among monoid homs. -/
theorem primeLift_unique {M : Type*} [CommMonoid M] (f : Nat.Primes → M)
    (g : Multiplicative (Multiset Nat.Primes) →* M)
    (hg : ∀ p : Nat.Primes, g (ofAdd ({p} : Multiset Nat.Primes)) = f p) :
    g = primeLift f := by
  refine MonoidHom.ext fun s => ?_
  have key : ∀ u : Multiset Nat.Primes, g (ofAdd u) = primeLift f (ofAdd u) := by
    intro u
    induction u using Multiset.induction_on with
    | empty => rw [ofAdd_zero, map_one, map_one]
    | cons p t ih =>
        have hsplit : (ofAdd (p ::ₘ t) : Multiplicative (Multiset Nat.Primes)) =
            ofAdd ({p} : Multiset Nat.Primes) * ofAdd t := by
          rw [← ofAdd_add, Multiset.singleton_add]
        rw [hsplit, map_mul, map_mul, hg, primeLift_ofAdd_singleton, ih]
  exact key (toAdd s)

/--
The prime-exponent readout is additive under multiplication: each prime axis
of a product of positive naturals carries the sum of the exponents of the
factors.  This is mathlib's `Nat.factorization_mul` read on `ℕ+`, where no
nonzeroness side condition remains.
-/
theorem factorization_coe_mul (m n : ℕ+) (p : ℕ) :
    ((m * n : ℕ+) : ℕ).factorization p =
      ((m : ℕ)).factorization p + ((n : ℕ)).factorization p := by
  rw [PNat.mul_coe, Nat.factorization_mul m.pos.ne' n.pos.ne', Finsupp.add_apply]

/--
Freeness of the positive naturals over the prime axes: prime factorization
is a bijective monoid map onto the multiset monoid over the primes, that
monoid has the universal property of the free commutative monoid on the
primes, and the prime-exponent readouts add under multiplication.
-/
theorem pnat_free_comm_monoid_on_primes :
    Function.Bijective primeFactorMulEquiv ∧
      (∀ m n : ℕ+, primeFactorMulEquiv (m * n) =
        primeFactorMulEquiv m * primeFactorMulEquiv n) ∧
      (∀ (M : Type*) [CommMonoid M] (f : Nat.Primes → M),
        ∃! g : Multiplicative (Multiset Nat.Primes) →* M,
          ∀ p : Nat.Primes, g (ofAdd ({p} : Multiset Nat.Primes)) = f p) ∧
      (∀ (m n : ℕ+) (p : ℕ),
        ((m * n : ℕ+) : ℕ).factorization p =
          ((m : ℕ)).factorization p + ((n : ℕ)).factorization p) := by
  refine ⟨primeFactorMulEquiv.bijective,
    fun m n => map_mul primeFactorMulEquiv m n, ?_, factorization_coe_mul⟩
  intro M _ f
  exact ⟨primeLift f, fun p => primeLift_ofAdd_singleton f p,
    fun g hg => primeLift_unique f g hg⟩

end D5.S3.Factorization
