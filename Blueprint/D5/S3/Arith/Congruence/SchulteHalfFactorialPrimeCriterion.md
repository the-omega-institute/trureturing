# Schulte's A000680 half-factorial primality criterion

## Abstract

Schulte's A000680 half-factorial sequence satisfies his primality criterion.

All variables range over the natural numbers N, including zero. The index is n, a(n) is the A000680 value, factorial is the natural factorial, powers and multiplication are natural-number operations, and the slash denotes exact natural-number division, not a fraction. Prime(x) means that x is prime, and u divides v is the natural divisibility relation. The scope is exactly the OEIS Conjecture sentence: for every n greater than zero, the displayed divisibility is equivalent to primality of 2n+1. The odd-composite factorial divisibility used in the proof is the frozen LaymanOddPowerFactorialResidue theorem, reused here.

**Definition 1.1 (The A000680 half-factorial sequence).**

$$\forall n \in \mathbb{N},\; \operatorname{a}\left(n\right) = (\operatorname{factorial}\left(2 \cdot n\right)) / (2^{n})$$

*Formalization.* `D5/S3/Arith/Congruence/SchulteHalfFactorialPrimeCriterion.a` (`✓ std3`).

*Citation.* Werner Schulte (2025). *OEIS A000680, (2n)!/2^n, with the primality criterion (2n+1) | a(n) + 2^n iff 2n+1 is prime*. URL: <https://oeis.org/A000680>.

*Commentary.*

The sequence value is the exact natural-number quotient of the factorial of 2n by 2 raised to n.

**Theorem 1.2 (Schulte's primality criterion).**

$$\forall n \in \mathbb{N},\; (0 < n) \Rightarrow ((2 \cdot n + 1 \mid \operatorname{a}\left(n\right) + 2^{n}) \Leftrightarrow (\operatorname{Prime}\left(2 \cdot n + 1\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Congruence/SchulteHalfFactorialPrimeCriterion.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a000680-schulte-half-factorial-prime-criterion` (proved) by `D5/S3/Arith/Congruence/SchulteHalfFactorialPrimeCriterion.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a000680-schulte-half-factorial-prime-criterion","declaration_gid":"D5/S3/Arith/Congruence/SchulteHalfFactorialPrimeCriterion.result","resolution_kind":"proved"} -->

*Citation.* Werner Schulte (2025). *OEIS A000680, (2n)!/2^n, with the primality criterion (2n+1) | a(n) + 2^n iff 2n+1 is prime*. URL: <https://oeis.org/A000680>.

*Commentary.*

For every positive natural index, the odd number 2n+1 divides a(n)+2^n exactly when that odd number is prime. The proof uses Wilson's theorem and Fermat's theorem in the prime branch, and the frozen odd-composite factorial divisibility theorem in the converse branch.

## References

- Truth anchor: `D5/S3/Arith/Congruence/SchulteHalfFactorialPrimeCriterion.a`
- Truth anchor: `D5/S3/Arith/Congruence/SchulteHalfFactorialPrimeCriterion.result`
- Dependency: [D5/S3/Arith/Congruence/LaymanOddPowerFactorialResidue](LaymanOddPowerFactorialResidue.md)
