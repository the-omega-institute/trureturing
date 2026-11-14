# Mathar's A186335 five-term recurrence

## Abstract

The independent source double sum A186335 satisfies Mathar's five-term recurrence.

**Definition 1.1 (The exact finite source sum).**

$$\forall n \in \mathbb{N},\; \operatorname{a}\left(n\right) = \sum_{(k,j)\in\operatorname{sourcePairs}\left(n\right)}(\operatorname{choose}\left(k - j, n - k - j\right):\mathbb{Z}) \cdot (\operatorname{choose}\left(k, j\right):\mathbb{Z}) \cdot (\operatorname{choose}\left(2 \cdot \left(n - k - j\right), n - k - j\right):\mathbb{Z})$$

*Formalization.* `D5/S1/Recurrence/Algebraic/MatharA186335FiveTermRecurrence.a` (`✓ std3`).

*Citation.* Paul Barry; R. J. Mathar; OEIS Foundation Inc. (2015). *OEIS A186335 — five-term recurrence for a central-binomial transform*. URL: <https://oeis.org/A186335>.

*Commentary.*

The domain sourcePairs(n) consists of natural pairs (k,j) in range(n+1) squared with j ≤ k, k+j ≤ n and n-k-j ≤ k-j. Put m=n-k-j. These conditions give 0 ≤ j ≤ k ≤ n and 0 ≤ m ≤ k-j before any natural subtraction is interpreted. Every excluded pair contributes zero. choose is the ordinary nonnegative binomial coefficient; each factor is cast to the integers. No negative central-binomial index is evaluated. The sequence is defined by this sum independently of the recurrence.

**Definition 1.2 (The full source-identified assertion).**

$$claim \Leftrightarrow \left(\forall n \in \mathbb{N},\; 4 \le n \Rightarrow (n:\mathbb{Z}) \cdot \operatorname{a}\left(n\right) + (1 - 2 \cdot (n:\mathbb{Z})) \cdot \operatorname{a}\left(n - 1\right) + 5 \cdot (1 - (n:\mathbb{Z})) \cdot \operatorname{a}\left(n - 2\right) + 3 \cdot (2 \cdot (n:\mathbb{Z}) - 3) \cdot \operatorname{a}\left(n - 3\right) + 5 \cdot ((n:\mathbb{Z}) - 2) \cdot \operatorname{a}\left(n - 4\right) = 0\right)$$

*Formalization.* `D5/S1/Recurrence/Algebraic/MatharA186335FiveTermRecurrence.claim` (`✓ std3`).

*Citation.* Paul Barry; R. J. Mathar; OEIS Foundation Inc. (2015). *OEIS A186335 — five-term recurrence for a central-binomial transform*. URL: <https://oeis.org/A186335>.

*Commentary.*

OEIS A186335 attributes the five terms to R. J. Mathar. Its offset is zero and the recurrence onset is omitted. Here every natural n ≥ 4 is included, so all five indices are nonnegative. Coefficient polynomials and sequence values lie in the integers. This is also the integer-index assertion under the usual identification of nonnegative indices. The support and onset conventions are explicit source interpretation, with no extra hypothesis.

**Theorem 1.3 (The complete recurrence).**

$$\forall n \in \mathbb{N},\; 4 \le n \Rightarrow (n:\mathbb{Z}) \cdot \operatorname{a}\left(n\right) + (1 - 2 \cdot (n:\mathbb{Z})) \cdot \operatorname{a}\left(n - 1\right) + 5 \cdot (1 - (n:\mathbb{Z})) \cdot \operatorname{a}\left(n - 2\right) + 3 \cdot (2 \cdot (n:\mathbb{Z}) - 3) \cdot \operatorname{a}\left(n - 3\right) + 5 \cdot ((n:\mathbb{Z}) - 2) \cdot \operatorname{a}\left(n - 4\right) = 0$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Algebraic/MatharA186335FiveTermRecurrence.result` (`✓ std3`). ∎

*Resolves.* `Problems/mathar-a186335-five-term-recurrence` (proved) by `D5/S1/Recurrence/Algebraic/MatharA186335FiveTermRecurrence.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"mathar-a186335-five-term-recurrence","declaration_gid":"D5/S1/Recurrence/Algebraic/MatharA186335FiveTermRecurrence.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Paul Barry; R. J. Mathar; OEIS Foundation Inc. (2015). *OEIS A186335 — five-term recurrence for a central-binomial transform*. URL: <https://oeis.org/A186335>.

*Commentary.*

Reindex by m=n-k-j and j, with inverse k=n-m-j and support 2m+2j ≤ n. Binomial multiplication and formal coefficient substitution identify the source series with B*C(X²*B), where B=(1-X-X²)^(-1) and C is the central-binomial series. The source-to-series identity is proved from the finite sum. The identity (1-4X)*C'=2*C, inverse differentiation and the chain rule then give P*A'+Q*A=0 with P=1-2X-5X²+6X³+5X⁴ and Q=-1-5X+9X²+10X³. The existing frozen A308815DFiniteRecurrence.euler_coeff and four coefficient shifts yield exactly the displayed integer recurrence. No assumed generating function, finite-prefix check or recurrence-defined substitute is used. This unit makes no claim about another Mathar sequence, global novelty or sibling conjectures.

## References

- Truth anchor: `D5/S1/Recurrence/Algebraic/MatharA186335FiveTermRecurrence.a`
- Truth anchor: `D5/S1/Recurrence/Algebraic/MatharA186335FiveTermRecurrence.claim`
- Truth anchor: `D5/S1/Recurrence/Algebraic/MatharA186335FiveTermRecurrence.result`
- Dependency: [D5/S1/Recurrence/A308815DFiniteRecurrence](../A308815DFiniteRecurrence.md)
