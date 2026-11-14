# The A116387 Motzkin transform

## Abstract

The six-term recurrence for the native Motzkin transform A116387.

Work in ordinary formal power series over Q. The symbol c denotes Mathlib's natural Catalan generating function mapped coefficientwise to Q. Its application to a series with zero constant coefficient means formal substitution. All coefficient indices are natural numbers; recurrence scalars are evaluated in Q. The square root always has constant coefficient one.

**Definition 1.1 (The native Motzkin generating function).**

$$M = (1 - X)^{-1} \cdot \operatorname{c}\left(X^{2} \cdot (1 - X)^{-2}\right)$$

*Formalization.* `D5/S1/Recurrence/Algebraic/MatharA116387SixTermRecurrence.M` (`✓ std3`).

*Citation.* R. J. Mathar; Paul Barry; OEIS Foundation Inc. (2011). *OEIS A116387 — six-term recurrence for a Motzkin transform*. URL: <https://oeis.org/A116387>.

*Commentary.*

This is the native A001006 formula c(X²/(1-X)²)/(1-X). The inverse exists because 1-X has constant coefficient one, and the substituted series has constant coefficient zero. The Catalan quadratic gives M=1+XM+X²M² and M(0)=1. If m is another solution, (1-X-X²(m+M))(m-M)=0. The first factor has constant coefficient one, so m=M.

**Definition 1.2 (The normalized root).**

$$y = 1 - X - 2 \cdot X^{2} \cdot M$$

*Formalization.* `D5/S1/Recurrence/Algebraic/MatharA116387SixTermRecurrence.y` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. J. Mathar; Paul Barry; OEIS Foundation Inc. (2011). *OEIS A116387 — six-term recurrence for a Motzkin transform*. URL: <https://oeis.org/A116387>.

*Commentary.*

The Motzkin quadratic implies y²=1-2X-3X² and y(0)=1. If z has the same square and constant coefficient, (z+y)(z-y)=0; z+y has constant coefficient two. Thus z=y. The identity 2X²M=1-X-y uses no inverse of X.

**Definition 1.3 (The exact source transform).**

$$F = (y \cdot (2 - M))^{-1}$$

*Formalization.* `D5/S1/Recurrence/Algebraic/MatharA116387SixTermRecurrence.F` (`✓ std3`).

*Citation.* R. J. Mathar; Paul Barry; OEIS Foundation Inc. (2011). *OEIS A116387 — six-term recurrence for a Motzkin transform*. URL: <https://oeis.org/A116387>.

*Commentary.*

OEIS A116387 defines this generating function. Its denominator has constant coefficient one, so the inverse is an actual unit inverse in Q[[X]].

**Definition 1.4 (The offset-zero coefficients).**

$$\forall n \in \mathbb{N},\; \operatorname{a}\left(n\right) = \operatorname{coeff}\left(n, F\right)$$

*Formalization.* `D5/S1/Recurrence/Algebraic/MatharA116387SixTermRecurrence.a` (`✓ std3`).

*Citation.* R. J. Mathar; Paul Barry; OEIS Foundation Inc. (2011). *OEIS A116387 — six-term recurrence for a Motzkin transform*. URL: <https://oeis.org/A116387>.

*Commentary.*

The first coefficient has index zero. Every lagged index below is nonnegative on n≥5.

**Definition 1.5 (The native source characterization).**

$$S \Leftrightarrow \left(\left(\operatorname{constantCoeff}\left(M\right) = 1 \land M = 1 + X \cdot M + X^{2} \cdot M^{2}\right) \land \left(\left(\forall m \in \operatorname{PowerSeries}\left(\mathbb{Q}\right),\; m = 1 + X \cdot m + X^{2} \cdot m^{2} \Rightarrow m = M\right) \land \left(\left(\operatorname{constantCoeff}\left(y\right) = 1 \land y^{2} = 1 - 2 \cdot X - 3 \cdot X^{2}\right) \land \left(\left(\forall z \in \operatorname{PowerSeries}\left(\mathbb{Q}\right),\; \operatorname{constantCoeff}\left(z\right) = 1 \Rightarrow \left(z^{2} = 1 - 2 \cdot X - 3 \cdot X^{2} \Rightarrow z = y\right)\right) \land y \cdot (2 - M) \cdot F = 1\right)\right)\right)\right)$$

*Formalization.* `D5/S1/Recurrence/Algebraic/MatharA116387SixTermRecurrence.native_spec` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. J. Mathar; Paul Barry; OEIS Foundation Inc. (2011). *OEIS A116387 — six-term recurrence for a Motzkin transform*. URL: <https://oeis.org/A116387>.

*Commentary.*

The proposition S includes the constructed Motzkin solution, its uniqueness, the normalized root and its uniqueness, and the inverse equation for F.

**Definition 1.6 (The complete six-term assertion).**

$$claim \Leftrightarrow \left(\left(\left(\operatorname{constantCoeff}\left(M\right) = 1 \land M = 1 + X \cdot M + X^{2} \cdot M^{2}\right) \land \left(\left(\forall m \in \operatorname{PowerSeries}\left(\mathbb{Q}\right),\; m = 1 + X \cdot m + X^{2} \cdot m^{2} \Rightarrow m = M\right) \land \left(\left(\operatorname{constantCoeff}\left(y\right) = 1 \land y^{2} = 1 - 2 \cdot X - 3 \cdot X^{2}\right) \land \left(\left(\forall z \in \operatorname{PowerSeries}\left(\mathbb{Q}\right),\; \operatorname{constantCoeff}\left(z\right) = 1 \Rightarrow \left(z^{2} = 1 - 2 \cdot X - 3 \cdot X^{2} \Rightarrow z = y\right)\right) \land y \cdot (2 - M) \cdot F = 1\right)\right)\right)\right) \land \left(\forall n \in \mathbb{N},\; 5 \le n \Rightarrow (n:\mathbb{Q}) \cdot (17 \cdot (n:\mathbb{Q}) - 142) \cdot \operatorname{a}\left(n\right) + (17 \cdot (n:\mathbb{Q})^{2} + 95 \cdot (n:\mathbb{Q}) + 138) \cdot \operatorname{a}\left(n - 1\right) + (-391 \cdot (n:\mathbb{Q})^{2} + 2488 \cdot (n:\mathbb{Q}) - 2908) \cdot \operatorname{a}\left(n - 2\right) + (-17 \cdot (n:\mathbb{Q})^{2} - 603 \cdot (n:\mathbb{Q}) + 1892) \cdot \operatorname{a}\left(n - 3\right) + 2 \cdot (697 \cdot (n:\mathbb{Q}) - 2021) \cdot ((n:\mathbb{Q}) - 4) \cdot \operatorname{a}\left(n - 4\right) + 60 \cdot (17 \cdot (n:\mathbb{Q}) - 47) \cdot ((n:\mathbb{Q}) - 4) \cdot \operatorname{a}\left(n - 5\right) = 0\right)\right)$$

*Formalization.* `D5/S1/Recurrence/Algebraic/MatharA116387SixTermRecurrence.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. J. Mathar; Paul Barry; OEIS Foundation Inc. (2011). *OEIS A116387 — six-term recurrence for a Motzkin transform*. URL: <https://oeis.org/A116387>.

*Commentary.*

Mathar's printed conjecture gives these six polynomial coefficients in this order. It prints no onset. The range n≥5 is the full well-formed offset-zero interpretation; OFFSET 0,2 does not specify a recurrence onset. The source characterization makes existence and branch normalization explicit.

**Theorem 1.7 (The native six-term recurrence).**

$$\left(\left(\operatorname{constantCoeff}\left(M\right) = 1 \land M = 1 + X \cdot M + X^{2} \cdot M^{2}\right) \land \left(\left(\forall m \in \operatorname{PowerSeries}\left(\mathbb{Q}\right),\; m = 1 + X \cdot m + X^{2} \cdot m^{2} \Rightarrow m = M\right) \land \left(\left(\operatorname{constantCoeff}\left(y\right) = 1 \land y^{2} = 1 - 2 \cdot X - 3 \cdot X^{2}\right) \land \left(\left(\forall z \in \operatorname{PowerSeries}\left(\mathbb{Q}\right),\; \operatorname{constantCoeff}\left(z\right) = 1 \Rightarrow \left(z^{2} = 1 - 2 \cdot X - 3 \cdot X^{2} \Rightarrow z = y\right)\right) \land y \cdot (2 - M) \cdot F = 1\right)\right)\right)\right) \land \left(\forall n \in \mathbb{N},\; 5 \le n \Rightarrow (n:\mathbb{Q}) \cdot (17 \cdot (n:\mathbb{Q}) - 142) \cdot \operatorname{a}\left(n\right) + (17 \cdot (n:\mathbb{Q})^{2} + 95 \cdot (n:\mathbb{Q}) + 138) \cdot \operatorname{a}\left(n - 1\right) + (-391 \cdot (n:\mathbb{Q})^{2} + 2488 \cdot (n:\mathbb{Q}) - 2908) \cdot \operatorname{a}\left(n - 2\right) + (-17 \cdot (n:\mathbb{Q})^{2} - 603 \cdot (n:\mathbb{Q}) + 1892) \cdot \operatorname{a}\left(n - 3\right) + 2 \cdot (697 \cdot (n:\mathbb{Q}) - 2021) \cdot ((n:\mathbb{Q}) - 4) \cdot \operatorname{a}\left(n - 4\right) + 60 \cdot (17 \cdot (n:\mathbb{Q}) - 47) \cdot ((n:\mathbb{Q}) - 4) \cdot \operatorname{a}\left(n - 5\right) = 0\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Algebraic/MatharA116387SixTermRecurrence.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a116387-six-term-recurrence` (proved) by `D5/S1/Recurrence/Algebraic/MatharA116387SixTermRecurrence.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a116387-six-term-recurrence","declaration_gid":"D5/S1/Recurrence/Algebraic/MatharA116387SixTermRecurrence.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* R. J. Mathar; Paul Barry; OEIS Foundation Inc. (2011). *OEIS A116387 — six-term recurrence for a Motzkin transform*. URL: <https://oeis.org/A116387>.

*Commentary.*

Put p=1-X-4X², q=1-2X-4X² and d=1-2X-3X². The native quadratic and inverse equation give 2qyF=y+p. Differentiate this identity and y²=d to obtain DF'-eF=f, where D=pqd, e=2-2X-14X²-14X³+40X⁴+48X⁵ and f=2X-6X²-6X³. For theta=X d/dX let L be the ordered sum of X^j P_j(theta+j), j=0,...,5, with P_j the six displayed polynomials. Multiplying the differentiated equation by w=17X²(5X+1) and the original equation by v=-5X(47X+25) gives pLF=wf'+vf=6pX²(5X-36). Cancel p, whose constant coefficient is one. The forcing has degree three. The Euler coefficient identity and all six shifts therefore give the printed recurrence for every n≥5, including n=5.

## References

- Truth anchor: `D5/S1/Recurrence/Algebraic/MatharA116387SixTermRecurrence.F`
- Truth anchor: `D5/S1/Recurrence/Algebraic/MatharA116387SixTermRecurrence.M`
- Truth anchor: `D5/S1/Recurrence/Algebraic/MatharA116387SixTermRecurrence.a`
- Truth anchor: `D5/S1/Recurrence/Algebraic/MatharA116387SixTermRecurrence.claim`
- Truth anchor: `D5/S1/Recurrence/Algebraic/MatharA116387SixTermRecurrence.native_spec`
- Truth anchor: `D5/S1/Recurrence/Algebraic/MatharA116387SixTermRecurrence.result`
- Truth anchor: `D5/S1/Recurrence/Algebraic/MatharA116387SixTermRecurrence.y`
- Dependency: [D5/S1/Recurrence/A308815DFiniteRecurrence](../A308815DFiniteRecurrence.md)
