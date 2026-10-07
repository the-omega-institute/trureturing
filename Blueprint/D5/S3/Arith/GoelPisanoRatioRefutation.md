# Goel's Pisano-Rank Ratio Question Is False

## Abstract

The prime-domain Fibonacci period-to-rank ratios omit every multiple of five, answering Goel's OQ4 in the negative.

The source states on p. 1: “For a prime p, the rank of apparition z(p) is the smallest positive integer k with p | Fₖ; it is well-defined for every prime p [3, 7]. The Pisano period π(n) is the period of (Fₘ mod n).” Here Fₘ is Nat.fib m. The source's z is the existing zeroRank from D5.S3.Arith.FibonacciAtomic.TimeSampling, with exactly the least-positive-zero definition. Natural-number infima use zero for an empty set; the relevant sets are nonempty at prime moduli.

$$
\forall p \in \mathrm{Nat},\; \operatorname{zeroRank}\left(p\right) = \operatorname{sInf}\left(\{k: \mathrm{Nat} \mid (0 < k) \land (p \mid \operatorname{Nat}.\operatorname{fib}\left(k\right))\}\right)
$$

**Definition 1.1 (The least positive Pisano period).**

$$\forall n \in \mathrm{Nat},\; \operatorname{pisanoPeriod}\left(n\right) = \operatorname{sInf}\left(\{k: \mathrm{Nat} \mid (0 < k) \land (\forall m \in \mathrm{Nat},\; \operatorname{Nat}.\operatorname{fib}\left(m + k\right) \bmod n = \operatorname{Nat}.\operatorname{fib}\left(m\right) \bmod n)\}\right)$$

*Formalization.* `D5/S3/Arith/GoelPisanoRatioRefutation.pisanoPeriod` (`✓ std3`).

*Citation.* Aradhya Goel (2026). *Sophie Germain Primes and the Totient of Fibonacci Numbers*. URL: <https://arxiv.org/abs/2604.17847v3>.

*Commentary.*

“The Pisano period π(n) is the period of (Fₘ mod n).” (p. 1). The least positive period is taken over all natural time indices m. The operation mod is Nat.mod, and all arguments have type Nat.

**Definition 1.2 (The standing prime domain).**

$$\forall q \in \mathrm{Nat},\; \operatorname{SophieGermain}\left(q\right) \Leftrightarrow ((\operatorname{Nat}.\operatorname{Prime}\left(q\right)) \land (\operatorname{Nat}.\operatorname{Prime}\left(2 \cdot q + 1\right)))$$

*Formalization.* `D5/S3/Arith/GoelPisanoRatioRefutation.SophieGermain` (`✓ std3`).

*Citation.* Aradhya Goel (2026). *Sophie Germain Primes and the Totient of Fibonacci Numbers*. URL: <https://arxiv.org/abs/2604.17847v3>.

*Commentary.*

A Sophie Germain prime q is a prime for which 2q+1 is also prime. The source defines z at primes and treats q as an odd prime; with q>5 this gives the displayed domain.

**Definition 1.3 (The source question).**

$$claim \Leftrightarrow (\{R: \mathrm{Nat} \mid \exists q \in \mathrm{Nat},\; (\operatorname{Nat}.\operatorname{Prime}\left(q\right)) \land ((\operatorname{Nat}.\operatorname{Prime}\left(2 \cdot q + 1\right)) \land ((5 < q) \land ((\operatorname{zeroRank}\left(2 \cdot q + 1\right) \mid \operatorname{pisanoPeriod}\left(q\right)) \land (R = \operatorname{Nat}.\operatorname{div}\left(\operatorname{pisanoPeriod}\left(q\right), \operatorname{zeroRank}\left(2 \cdot q + 1\right)\right)))))\} = \{R: \mathrm{Nat} \mid \operatorname{Odd}\left(R\right)\})$$

*Formalization.* `D5/S3/Arith/GoelPisanoRatioRefutation.claim` (`✓ std3`).

*Citation.* Aradhya Goel (2026). *Sophie Germain Primes and the Totient of Fibonacci Numbers*. URL: <https://arxiv.org/abs/2604.17847v3>.

*Commentary.*

“OQ4. Values of π(q)/z(2q + 1). Is {π(q)/z(2q + 1) : q > 5 with z(2q + 1) | π(q)} = {odd integers}?” (Section 10, p. 10). The prime hypotheses are the standing domain of Sections 5–7: z(2q+1) is defined at a prime, and q is an odd prime throughout. Every eligible ratio is positive, so the right side is encoded by Odd on Nat, the positive odd integers. The reading over all integers also fails, since it contains negative values. Nat.div is natural-number division; the divisibility hypothesis makes this quotient exact. The two prime conjuncts are expanded here, matching the source domain.

**Theorem 1.4 (Five is never a value).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoelPisanoRatioRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/goel-2026-pisano-rank-ratio-oq4` (refuted) by `D5/S3/Arith/GoelPisanoRatioRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"goel-2026-pisano-rank-ratio-oq4","declaration_gid":"D5/S3/Arith/GoelPisanoRatioRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Aradhya Goel (2026). *Sophie Germain Primes and the Totient of Fibonacci Numbers*. URL: <https://arxiv.org/abs/2604.17847v3>.

*Commentary.*

The value five is odd, but it cannot occur. Set p=2q+1. The prime Fibonacci rank bound and the period bounds first force the quadratic character at p to be negative: a positive character would make zeroRank(p) divide both 2q and q²−1, hence two, whereas p>11 gives zeroRank(p)≥5. A positive character at q would then make zeroRank(p) divide both q−1 and 2(q+1), hence four, the same contradiction. The negative character at q gives q mod 5 equal to two or three and π(q) dividing 2(q+1). Thus five divides neither π(q) nor its exact quotient by zeroRank(p). The argument excludes every multiple of five. It does not assert that all remaining positive odd values occur.

## References

- Truth anchor: `D5/S3/Arith/GoelPisanoRatioRefutation.SophieGermain`
- Truth anchor: `D5/S3/Arith/GoelPisanoRatioRefutation.claim`
- Truth anchor: `D5/S3/Arith/GoelPisanoRatioRefutation.pisanoPeriod`
- Truth anchor: `D5/S3/Arith/GoelPisanoRatioRefutation.result`
- Dependency: [D5/S3/Arith/FibonacciAtomic/GlobalGcdSampling](FibonacciAtomic/GlobalGcdSampling.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/TimeSampling](FibonacciAtomic/TimeSampling.md)
