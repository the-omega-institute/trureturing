# Tebni's A364822 congruence at powers of two

## Abstract

Hyperbolic EGF coefficients have residue one at every power of two.

The function D5.S1.Recurrence.Residue.TebniA364822.a is n! times the nth ordinary coefficient of cosh(x)/(1-2 sinh(x)). The exponent m is natural and includes zero; Int.ModEq uses the integer cast of 2^m. The integer z is cast to Q in the coefficient equality.

**Definition 1.1 (The power-of-two conjecture).**

$$\operatorname{claim} \iff (\forall m: \mathbb{N}, \exists z: \mathbb{Z}, ((z: \mathbb{Q}) = \operatorname{D5}.\operatorname{S1}.\operatorname{Recurrence}.\operatorname{Residue}.\operatorname{TebniA364822}.\operatorname{a}\left(2^{m}\right)) \land (\operatorname{Int}.\operatorname{ModEq}\left((2^{m}: \mathbb{Z}), z, 1\right)))$$

*Formalization.* `D5/S1/Recurrence/Residue/TebniA364822PowerOfTwo.claim` (`✓ std3`).

*Citation.* M. Tebni (2023). *OEIS A364822, Expansion of e.g.f. cosh(x) / (1 - 2*sinh(x))*. URL: <https://oeis.org/A364822>.

*Commentary.*

OEIS A364822, Comments (unpaginated): "For n = 2^m (m natural number), a(n) == 1 (mod n)." At m=0 the modulus is one. At positive m the index is even.

**Theorem 1.2 (Odd-index dyadic binomial divisibility).**

$$\forall m: \mathbb{N}, \forall k: \mathbb{N}, (\operatorname{Odd}\left(k\right)) \implies (2^{m} \mid \operatorname{Nat}.\operatorname{choose}\left(2^{m}, k\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Residue/TebniA364822PowerOfTwo.pow_two_dvd_choose_odd` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The adjacent binomial identity makes the product of k and choose(2^m,k) divisible by 2^m. Since odd k is coprime to every power of two, the binomial coefficient itself is divisible by 2^m. The exponent and index are arbitrary naturals.

**Theorem 1.3 (Residue one at every power of two).**

$$\forall m: \mathbb{N}, \exists z: \mathbb{Z}, ((z: \mathbb{Q}) = \operatorname{D5}.\operatorname{S1}.\operatorname{Recurrence}.\operatorname{Residue}.\operatorname{TebniA364822}.\operatorname{a}\left(2^{m}\right)) \land (\operatorname{Int}.\operatorname{ModEq}\left((2^{m}: \mathbb{Z}), z, 1\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Residue/TebniA364822PowerOfTwo.result` (`✓ std3`). ∎

*Resolves.* `Problems/tebni364822-power-of-two-cong` (proved) by `D5/S1/Recurrence/Residue/TebniA364822PowerOfTwo.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"tebni364822-power-of-two-cong","declaration_gid":"D5/S1/Recurrence/Residue/TebniA364822PowerOfTwo.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* M. Tebni (2023). *OEIS A364822, Expansion of e.g.f. cosh(x) / (1 - 2*sinh(x))*. URL: <https://oeis.org/A364822>.

*Commentary.*

For odd k, 2^m divides the binomial coefficient choose(2^m,k), by the adjacent binomial identity and coprimality of k and 2^m. At a positive exponent, all nonzero sinh terms in the integer recurrence have odd k and therefore vanish modulo 2^m. The cosh term is one. The zero exponent has modulus one.

## References

- Truth anchor: `D5/S1/Recurrence/Residue/TebniA364822PowerOfTwo.claim`
- Truth anchor: `D5/S1/Recurrence/Residue/TebniA364822PowerOfTwo.pow_two_dvd_choose_odd`
- Truth anchor: `D5/S1/Recurrence/Residue/TebniA364822PowerOfTwo.result`
- Dependency: [D5/S1/Recurrence/Residue/TebniA364822](TebniA364822.md)
