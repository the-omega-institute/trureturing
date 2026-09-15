# The OEIS A260310 Balanced Prime-Divisor Pair Conjecture

## Abstract

The balanced pair (140140, 141601) refutes Wilson's mod-six conjecture for OEIS A260310.

**Definition 1.1 (The distinct prime-divisor sum).**

$$\forall n \in \mathrm{Nat},\; \operatorname{S}\left(n\right) = \sum_{p \in \operatorname{primeFactors}(n)} p$$

*Formalization.* `D5/S3/Arith/Congruence/WilsonBalancedPrimeDivisorPairModSixRefutation.S` (`✓ std3`).

*Citation.* Robert G. Wilson v; Juri-Stepan Gerasimov (2015). *OEIS A260310, Pairs with balanced sums of prime divisors (A008472) and inverse prime divisors (A069359), ordered by larger members*. URL: <https://oeis.org/A260310>.

*Commentary.*

For every natural n, S(n) is the sum of the distinct prime divisors in Nat.primeFactors(n). This is OEIS A008472.

**Definition 1.2 (Balanced pairs).**

$$\forall x \in \mathrm{Nat}, y \in \mathrm{Nat},\; (\operatorname{IsPair}\left(x, y\right)) \Leftrightarrow ((x < y) \land \left((\operatorname{S}\left(x\right) + \operatorname{S}\left(y\right) = \operatorname{squarefreeDeriv}\left(x\right) + \operatorname{squarefreeDeriv}\left(y\right)) \land \left((\operatorname{S}\left(x\right) \ne \operatorname{S}\left(y\right)) \land (\operatorname{S}\left(y\right) \ne \operatorname{squarefreeDeriv}\left(y\right))\right)\right))$$

*Formalization.* `D5/S3/Arith/Congruence/WilsonBalancedPrimeDivisorPairModSixRefutation.IsPair` (`✓ std3`).

*Citation.* Robert G. Wilson v; Juri-Stepan Gerasimov (2015). *OEIS A260310, Pairs with balanced sums of prime divisors (A008472) and inverse prime divisors (A069359), ordered by larger members*. URL: <https://oeis.org/A260310>.

*Commentary.*

The frozen definition D5/S3/PrimeForms/PrimaryPseudoperfectPorts.squarefreeDeriv is the sum, over each distinct prime divisor p of n, of the natural-number quotient n divided by p (OEIS A069359). A pair has its smaller member first, has equal combined S and squarefreeDeriv values, has unequal S values, and excludes the equality S(y) = squarefreeDeriv(y). These are the textual and program filters used by the entry.

**Definition 1.3 (Wilson's mod-six conjecture).**

$$(claim) \Leftrightarrow (\forall x \in \mathrm{Nat}, y \in \mathrm{Nat},\; \operatorname{IsPair}\left(x, y\right) \Rightarrow \left(1 < x \Rightarrow \left(\left(\neg \operatorname{Prime}(x)\right) \Rightarrow 6 \mid x\right)\right))$$

*Formalization.* `D5/S3/Arith/Congruence/WilsonBalancedPrimeDivisorPairModSixRefutation.claim` (`✓ std3`).

*Citation.* Robert G. Wilson v; Juri-Stepan Gerasimov (2015). *OEIS A260310, Pairs with balanced sums of prime divisors (A008472) and inverse prime divisors (A069359), ordered by larger members*. URL: <https://oeis.org/A260310>.

*Commentary.*

For every balanced pair of natural numbers, the conjecture says that a composite smaller member greater than one is divisible by six.

**Theorem 1.4 (The mod-six conjecture fails).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Congruence/WilsonBalancedPrimeDivisorPairModSixRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a260310-balanced-prime-divisor-pair-mod-six-refutation` (refuted) by `D5/S3/Arith/Congruence/WilsonBalancedPrimeDivisorPairModSixRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a260310-balanced-prime-divisor-pair-mod-six-refutation","declaration_gid":"D5/S3/Arith/Congruence/WilsonBalancedPrimeDivisorPairModSixRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Robert G. Wilson v; Juri-Stepan Gerasimov (2015). *OEIS A260310, Pairs with balanced sums of prime divisors (A008472) and inverse prime divisors (A069359), ordered by larger members*. URL: <https://oeis.org/A260310>.

*Commentary.*

The pair is (140140, 141601). Here 140140 = 2^2 * 5 * 7^2 * 11 * 13 and is congruent to 4 modulo 6, while 141601 is prime. The values S(140140) = 38, squarefreeDeriv(140140) = 141638, S(141601) = 141601, and squarefreeDeriv(141601) = 1 establish the balance and filters. Minimality and the prime/composite alternation sentence are not claimed.

## References

- Truth anchor: `D5/S3/Arith/Congruence/WilsonBalancedPrimeDivisorPairModSixRefutation.IsPair`
- Truth anchor: `D5/S3/Arith/Congruence/WilsonBalancedPrimeDivisorPairModSixRefutation.S`
- Truth anchor: `D5/S3/Arith/Congruence/WilsonBalancedPrimeDivisorPairModSixRefutation.claim`
- Truth anchor: `D5/S3/Arith/Congruence/WilsonBalancedPrimeDivisorPairModSixRefutation.result`
- Dependency: [D5/S3/PrimeForms/PrimaryPseudoperfectPorts](../../PrimeForms/PrimaryPseudoperfectPorts.md)
