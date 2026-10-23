# Fibonacci numbers are not 2-super-accessible

## Abstract

A rotation coloring gives a kernel-checked refutation of 2-super-accessibility for the Fibonacci numbers.

**Definition 1.1 (The Fibonacci gap set).**

$$\operatorname{fibSet}\left(\right) = \{d : \mathbb{N} \mid \exists n \in \mathbb{N},\; (1 \le n) \land (d = \operatorname{Nat}.\operatorname{fib}\left(n\right))\}$$

*Formalization.* `D5/S3/Arith/Additive/FibonacciSuperAccessibility.fibSet` (`✓ std3`).

*Citation.* Bruce M. Landman, Aaron Robertson, Quinn Robertson (2023). *Ramsey properties for integer sequences with restricted gaps*. DOI: [10.2140/moscow.2023.12.181](https://doi.org/10.2140/moscow.2023.12.181). URL: <https://math.colgate.edu/~aaron/pap/moreDoAFinal.pdf>.

*Commentary.*

The paper writes F = {f_n}_{n≥1} for the set of Fibonacci numbers (author-version PDF p. 2). The encoding is {d | ∃ n, 1 ≤ n ∧ d = Nat.fib n}, so the indexing starts at n=1 and both first Fibonacci occurrences are retained.

**Definition 1.2 (Restricted-gap arithmetic progressions).**

$$\forall S \in \operatorname{Set}\left(\mathbb{N}\right),\; \forall A \in \operatorname{Set}\left(\mathbb{N}\right),\; \forall k \in \mathbb{N},\; \operatorname{HasAP}\left(S, A, k\right) = \left(\exists x \in \mathbb{N},\; \exists d \in \mathbb{N},\; (1 \le x) \land (d \in S) \land (\forall i \in \mathbb{N},\; (i < k) \Rightarrow x + i \cdot d \in A)\right)$$

*Formalization.* `D5/S3/Arith/Additive/FibonacciSuperAccessibility.HasAP` (`✓ std3`).

*Citation.* Bruce M. Landman, Aaron Robertson, Quinn Robertson (2023). *Ramsey properties for integer sequences with restricted gaps*. DOI: [10.2140/moscow.2023.12.181](https://doi.org/10.2140/moscow.2023.12.181). URL: <https://math.colgate.edu/~aaron/pap/moreDoAFinal.pdf>.

*Commentary.*

Definition 1 (author-version PDF p. 1) calls these “arithmetic progressions {x, x+d, x+2d, . . . , x+(k − 1)d where the gap, d, belongs S; such a progression may be called an S-ap.” The encoding uses natural-number carriers and the displayed positive start, gap membership and k-term condition.

**Definition 1.3 (Restricted-gap diffsequences).**

$$\forall S \in \operatorname{Set}\left(\mathbb{N}\right),\; \forall A \in \operatorname{Set}\left(\mathbb{N}\right),\; \forall k \in \mathbb{N},\; \operatorname{HasDiffSeq}\left(S, A, k\right) = \left(\exists x \in \mathbb{N} \to \mathbb{N},\; (1 \le \operatorname{x}\left(0\right)) \land (\forall i \in \mathbb{N},\; (i + 1 < k) \Rightarrow (\operatorname{x}\left(i\right) < \operatorname{x}\left(i + 1\right)) \land (\operatorname{x}\left(i + 1\right) - \operatorname{x}\left(i\right) \in S)) \land (\forall i \in \mathbb{N},\; (i < k) \Rightarrow \operatorname{x}\left(i\right) \in A)\right)$$

*Formalization.* `D5/S3/Arith/Additive/FibonacciSuperAccessibility.HasDiffSeq` (`✓ std3`).

*Citation.* Bruce M. Landman, Aaron Robertson, Quinn Robertson (2023). *Ramsey properties for integer sequences with restricted gaps*. DOI: [10.2140/moscow.2023.12.181](https://doi.org/10.2140/moscow.2023.12.181). URL: <https://math.colgate.edu/~aaron/pap/moreDoAFinal.pdf>.

*Commentary.*

The source states (author-version PDF p. 2): “given a set D ⊆ Z+, a sequence x1 < x2 < . . . < xk is called a D-diffsequence if xi − xi−1 ∈ D for all i ∈ {2, . . . , k}.” The encoding adds color-class membership and a positive first entry on natural-number carriers.

**Definition 1.4 (Super-accessibility).**

$$\forall r \in \mathbb{N},\; \forall S \in \operatorname{Set}\left(\mathbb{N}\right),\; \operatorname{SuperAccessible}\left(r, S\right) = \left(\forall c \in \mathbb{N} \to \mathbb{N},\; (\forall n \in \mathbb{N},\; (1 \le n) \Rightarrow (1 \le \operatorname{c}\left(n\right)) \land (\operatorname{c}\left(n\right) \le r)) \Rightarrow (\forall k \in \mathbb{N},\; \operatorname{HasAP}\left(S, \{n : \mathbb{N} \mid \operatorname{c}\left(n\right) = 1\}, k\right)) \lor (\exists j \in \mathbb{N},\; (2 \le j) \land (j \le r) \land (\forall k \in \mathbb{N},\; \operatorname{HasDiffSeq}\left(S, \{n : \mathbb{N} \mid \operatorname{c}\left(n\right) = j\}, k\right)))\right)$$

*Formalization.* `D5/S3/Arith/Additive/FibonacciSuperAccessibility.SuperAccessible` (`✓ std3`).

*Citation.* Bruce M. Landman, Aaron Robertson, Quinn Robertson (2023). *Ramsey properties for integer sequences with restricted gaps*. DOI: [10.2140/moscow.2023.12.181](https://doi.org/10.2140/moscow.2023.12.181). URL: <https://math.colgate.edu/~aaron/pap/moreDoAFinal.pdf>.

*Commentary.*

Definition 14 (author-version PDF p. 6) states: “For r ∈ Z+, a set S ⊆ Z+ is called r-super-accessible if every r-coloring of Z+, using the colors 1, 2 . . . , r, admits arbitrarily long S-aps of color 1 or arbitrarily long S-diffsequences of color j for some j ∈ {2, 3, . . . , r}.” The encoding uses positive naturals and the literal colors.

**Definition 1.5 (The published question).**

$$\operatorname{claim}\left(\right) = \operatorname{SuperAccessible}\left(2, \operatorname{fibSet}\left(\right)\right)$$

*Formalization.* `D5/S3/Arith/Additive/FibonacciSuperAccessibility.claim` (`✓ std3`).

*Citation.* Bruce M. Landman, Aaron Robertson, Quinn Robertson (2023). *Ramsey properties for integer sequences with restricted gaps*. DOI: [10.2140/moscow.2023.12.181](https://doi.org/10.2140/moscow.2023.12.181). URL: <https://math.colgate.edu/~aaron/pap/moreDoAFinal.pdf>.

*Commentary.*

Section 5, question 3 (author-version PDF p. 16) asks verbatim: “Is the set of Fibonacci numbers 2-super-accessible? We know it is 2-accessible but that it is not 2-large.” The Lean claim is SuperAccessible 2 fibSet.

**Definition 1.6 (The rotation coloring).**

$$\forall n \in \mathbb{N},\; \operatorname{coloring}\left(n\right) = (\operatorname{if} (\operatorname{Int}.\operatorname{fract}\left(\frac{(47 + \operatorname{Real}.\operatorname{sqrt}\left(5\right))}{58} \cdot (\operatorname{Nat}.\operatorname{cast}\left(n\right) : \mathrm{Real})\right) < \frac{1}{16}) \operatorname{then} 2 \operatorname{else} 1)$$

*Formalization.* `D5/S3/Arith/Additive/FibonacciSuperAccessibility.coloring` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* William J. Wesley (2026). *The Fibonacci numbers are not 3-accessible*. URL: <https://arxiv.org/abs/2609.33744>.

*Commentary.*

Color n with 2 when the fractional part of ((47+√5)/58)n is below 1/16, and with 1 otherwise. The modulus-29 phase parameter follows the published construction acknowledged in Wesley's Fibonacci accessibility work.

**Theorem 1.7 (No 42-term color-one Fibonacci progression).**

$$\neg\operatorname{HasAP}\left(\operatorname{fibSet}\left(\right), \{n : \mathbb{N} \mid \operatorname{coloring}\left(n\right) = 1\}, 42\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Additive/FibonacciSuperAccessibility.no_color_one_ap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every Fibonacci-gap arithmetic progression of color 1 has fewer than 42 terms. The proof uses the period-seven residue block, a 29-term hitting lemma for large gaps, and six exact rational certificates for the small gaps.

**Theorem 1.8 (No three-term color-two Fibonacci diffsequence).**

$$\neg\operatorname{HasDiffSeq}\left(\operatorname{fibSet}\left(\right), \{n : \mathbb{N} \mid \operatorname{coloring}\left(n\right) = 2\}, 3\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Additive/FibonacciSuperAccessibility.no_color_two_diffseq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

From a color-two point, every Fibonacci translate advances the fractional phase by more than 1/32 without wrapping. A window of width 1/16 therefore contains no three-term color-two diffsequence.

**Theorem 1.9 (Refutation of 2-super-accessibility).**

$$\neg\operatorname{claim}\left(\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Additive/FibonacciSuperAccessibility.result` (`✓ std3`). ∎

*Resolves.* `Problems/landman-robertson-robertson-2023-fibonacci-super-accessibility` (refuted) by `D5/S3/Arith/Additive/FibonacciSuperAccessibility.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"landman-robertson-robertson-2023-fibonacci-super-accessibility","declaration_gid":"D5/S3/Arith/Additive/FibonacciSuperAccessibility.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Bruce M. Landman, Aaron Robertson, Quinn Robertson (2023). *Ramsey properties for integer sequences with restricted gaps*. DOI: [10.2140/moscow.2023.12.181](https://doi.org/10.2140/moscow.2023.12.181). URL: <https://math.colgate.edu/~aaron/pap/moreDoAFinal.pdf>.

*Commentary.*

The two avoidance theorems contradict the two alternatives in SuperAccessible 2 fibSet for the displayed coloring, proving the negation of the published question.

## References

- Truth anchor: `D5/S3/Arith/Additive/FibonacciSuperAccessibility.HasAP`
- Truth anchor: `D5/S3/Arith/Additive/FibonacciSuperAccessibility.HasDiffSeq`
- Truth anchor: `D5/S3/Arith/Additive/FibonacciSuperAccessibility.SuperAccessible`
- Truth anchor: `D5/S3/Arith/Additive/FibonacciSuperAccessibility.claim`
- Truth anchor: `D5/S3/Arith/Additive/FibonacciSuperAccessibility.coloring`
- Truth anchor: `D5/S3/Arith/Additive/FibonacciSuperAccessibility.fibSet`
- Truth anchor: `D5/S3/Arith/Additive/FibonacciSuperAccessibility.no_color_one_ap`
- Truth anchor: `D5/S3/Arith/Additive/FibonacciSuperAccessibility.no_color_two_diffseq`
- Truth anchor: `D5/S3/Arith/Additive/FibonacciSuperAccessibility.result`
- Dependency: [D5/S1/Words/ReturnWords/GoldenArcFirstReturnCore](../../../S1/Words/ReturnWords/GoldenArcFirstReturnCore.md)
