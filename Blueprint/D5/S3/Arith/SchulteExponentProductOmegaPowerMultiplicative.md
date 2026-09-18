# Schulte's Exponent-Product Multiplicativity Conjecture

## Abstract

Schulte's A322327 exponent-product function is multiplicative with prescribed prime powers.

N denotes the natural numbers including zero and Z denotes the integers. For n in N, primeFactors(n) is the finite set of prime divisors, factorization(n,p), also written v_p(n), is the natural exponent of p in n, and A005361(n) is the product of those exponents. The empty product gives A005361(1)=1. The function omega(n) counts distinct prime divisors, k is an arbitrary integer parameter, and a_k(n) is integer valued. Coprimality means gcd(m,n)=1. Lean's power convention gives 0^0=1. The formal claim covers, for every integer k, multiplicativity on coprime natural arguments and the value k times e at every positive prime-power exponent. The trailing OEIS sequence correspondences are outside the claim.

**Definition 1.1 (The exponent-product function).**

$$\forall k \in \mathbb{Z}, \forall n \in \mathbb{N}, \left(a_{k}\right)\left(n\right) = \prod_{p \in \operatorname{primeFactors}\left(n\right)} \operatorname{intCast}\left(\operatorname{factorization}\left(n, p\right)\right) \cdot k^{\operatorname{omega}\left(n\right)}$$

*Formalization.* `D5/S3/Arith/SchulteExponentProductOmegaPowerMultiplicative.a` (`✓ std3`).

*Citation.* Werner Schulte (2018). *OEIS A322327, A005361(n)·A034444(n), with the conjecture that A005361(n)·k^ω(n) is multiplicative with prime-power values k·e*. URL: <https://oeis.org/A322327>.

*Commentary.*

The finite product is A005361(n); each natural exponent is explicitly cast to an integer before multiplication by the integer power k^omega(n).

**Theorem 1.2 (Schulte's multiplicativity and prime-power formula).**

$$\forall k \in \mathbb{Z}, (\forall m \in \mathbb{N}, \forall n \in \mathbb{N}, (\operatorname{gcd}\left(m, n\right) = 1) \Rightarrow (\left(a_{k}\right)\left(m \cdot n\right) = \left(a_{k}\right)\left(m\right) \cdot \left(a_{k}\right)\left(n\right))) \land (\forall p \in \mathbb{N}, \forall e \in \mathbb{N}, (\operatorname{Prime}\left(p\right)) \Rightarrow ((0 < e) \Rightarrow (\left(a_{k}\right)\left(p^{e}\right) = k \cdot \operatorname{intCast}\left(e\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/SchulteExponentProductOmegaPowerMultiplicative.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a322327-schulte-exponent-product-omega-power-multiplicative` (proved) by `D5/S3/Arith/SchulteExponentProductOmegaPowerMultiplicative.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a322327-schulte-exponent-product-omega-power-multiplicative","declaration_gid":"D5/S3/Arith/SchulteExponentProductOmegaPowerMultiplicative.result","resolution_kind":"proved"} -->

*Citation.* Werner Schulte (2018). *OEIS A322327, A005361(n)·A034444(n), with the conjecture that A005361(n)·k^ω(n) is multiplicative with prime-power values k·e*. URL: <https://oeis.org/A322327>.

*Commentary.*

For every integer k, the first conjunct states multiplicativity on coprime natural arguments and the second gives a_k(p^e)=k times e for prime p and positive e. This settles the two assertions in the OEIS conjecture sentence within the stated scope.

## References

- Truth anchor: `D5/S3/Arith/SchulteExponentProductOmegaPowerMultiplicative.a`
- Truth anchor: `D5/S3/Arith/SchulteExponentProductOmegaPowerMultiplicative.result`
