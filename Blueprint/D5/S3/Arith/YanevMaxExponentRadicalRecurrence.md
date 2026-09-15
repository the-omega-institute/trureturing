# Yanev's Maximum Exponent Radical Recurrence

## Abstract

The maximum prime exponent drops by one when a positive integer greater than one is divided by its radical.

N denotes the natural numbers including zero; all arithmetic and the variables n and p are natural-valued. The finite set primeFactors(n) contains the distinct prime divisors of n, and factorization(n,p) is the exponent of p, zero outside that support. Mathlib takes both the prime-factor set and factorization of zero to be empty. The named operator sup takes a finite set and a natural-valued function and returns its maximum, with value zero on the empty set. The expression (p:N ↦ factorization(n,p)) denotes a function of p and makes explicit the function underlying Lean's finitely supported factorization. The value a(n) is the maximum exponent. The radical is the frozen primeRadical of D5/S1/Deficit/AlmostAdditivity (A007947), the product of distinct prime divisors, rendered as the named operator primeRadical. The operator div means natural-number division, not field division.

OEIS A051903 defines a by the maximum prime exponent. A007947 is primeRadical, and A003557(n) is n / primeRadical(n). The literature note yanev2017a051903 records Labos Elemer's entry and Velin Yanev's September 2, 2017 conjecture.

**Definition 1.1 (The maximum prime exponent).**

$$\forall n: \mathbb{N}, \operatorname{a}\left(n\right) = \operatorname{sup}\left(\operatorname{primeFactors}\left(n\right), (p: \mathbb{N} \mapsto \operatorname{factorization}\left(n, p\right))\right)$$

*Formalization.* `D5/S3/Arith/YanevMaxExponentRadicalRecurrence.a` (`✓ std3`).

*Citation.* Labos Elemer; Velin Yanev (2017). *OEIS A051903, maximum exponent in the prime factorization of n*. URL: <https://oeis.org/A051903>.

*Commentary.*

The defining finite supremum is zero when the prime-factor set is empty. In particular, a 0 = 0 is an out-of-range extension of the positive-index OEIS sequence; a 1 = 0 is its stated base value.

**Theorem 1.2 (The A051903 base value, Yanev recurrence, and determination).**

$$(\operatorname{a}\left(1\right) = 0) \land ((\forall n: \mathbb{N}, (1 < n) \implies (\operatorname{a}\left(n\right) = \operatorname{a}\left(\operatorname{div}\left(n, \operatorname{primeRadical}\left(n\right)\right)\right) + 1)) \land (\forall b: (\mathbb{N} \to \mathbb{N}), (b\left(1\right) = 0) \implies ((\forall n: \mathbb{N}, (1 < n) \implies (b\left(n\right) = b\left(\operatorname{div}\left(n, \operatorname{primeRadical}\left(n\right)\right)\right) + 1)) \implies (\forall n: \mathbb{N}, (0 < n) \implies (b\left(n\right) = \operatorname{a}\left(n\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/YanevMaxExponentRadicalRecurrence.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a051903-yanev-max-exponent-radical-recurrence` (proved) by `D5/S3/Arith/YanevMaxExponentRadicalRecurrence.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a051903-yanev-max-exponent-radical-recurrence","declaration_gid":"D5/S3/Arith/YanevMaxExponentRadicalRecurrence.result","resolution_kind":"proved"} -->

*Citation.* Labos Elemer; Velin Yanev (2017). *OEIS A051903, maximum exponent in the prime factorization of n*. URL: <https://oeis.org/A051903>.

*Commentary.*

The first conjunct gives a 1 = 0. The radical is the frozen primeRadical of D5/S1/Deficit/AlmostAdditivity (A007947), rendered as the named operator primeRadical. For n > 1, division by this radical subtracts one from every positive prime exponent. Extending the quotient's factorization by zero to the original prime support preserves its supremum; addition by one commutes with that nonempty supremum. This gives the second conjunct for every natural n with 1 < n. The third conjunct states that the relation together with a(1) = 0 determines the sequence on positive indices: every function b:N → N with b(1) = 0 and the same recurrence agrees with a at every n > 0. For n > 1, the radical divides n and is greater than one, so its quotient is positive and strictly smaller than n. Strong induction then gives agreement from the base value and the two recurrences.

## References

- Truth anchor: `D5/S3/Arith/YanevMaxExponentRadicalRecurrence.a`
- Truth anchor: `D5/S3/Arith/YanevMaxExponentRadicalRecurrence.result`
- Dependency: [D5/S1/Deficit/AlmostAdditivity](../../S1/Deficit/AlmostAdditivity.md)
