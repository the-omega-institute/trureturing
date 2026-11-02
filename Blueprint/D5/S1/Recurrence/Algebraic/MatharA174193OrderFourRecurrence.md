# An order-four recurrence for OEIS A174193

## Abstract

Mathar's order-four recurrence holds for the specified algebraic power series.

All series have rational coefficients. X is the power-series indeterminate. The formal square root is specified by its square and constant coefficient. Every recurrence scalar is rational; n and the arguments n-1 through n-4 are natural, with natural subtraction under the guard 4 ≤ n.

**Definition 1.1 (The radicand).**

$$p = 1 - 4 \cdot X$$

*Formalization.* `D5/S1/Recurrence/Algebraic/MatharA174193OrderFourRecurrence.p` (`✓ std3`).

*Citation.* R. J. Mathar; OEIS Foundation Inc. (2016). *OEIS A174193 — an order-four recurrence for an algebraic generating series*. URL: <https://oeis.org/A174193>.

*Commentary.*

The radicand is 1-4*x in OEIS A174193, FORMULA section (no page numbers).

**Definition 1.2 (The rational numerator polynomial).**

$$P = 1 - 8 \cdot X + 13 \cdot X^{2} + 24 \cdot X^{3} - 48 \cdot X^{4}$$

*Formalization.* `D5/S1/Recurrence/Algebraic/MatharA174193OrderFourRecurrence.P` (`✓ std3`).

*Citation.* R. J. Mathar; OEIS Foundation Inc. (2016). *OEIS A174193 — an order-four recurrence for an algebraic generating series*. URL: <https://oeis.org/A174193>.

*Commentary.*

The rational part of the source numerator is 1-8*x+13*x^2+24*x^3-48*x^4.

**Definition 1.3 (The square-root multiplier).**

$$B = 1 - 6 \cdot X + X^{2} + 34 \cdot X^{3} - 26 \cdot X^{4} - 4 \cdot X^{5}$$

*Formalization.* `D5/S1/Recurrence/Algebraic/MatharA174193OrderFourRecurrence.B` (`✓ std3`).

*Citation.* R. J. Mathar; OEIS Foundation Inc. (2016). *OEIS A174193 — an order-four recurrence for an algebraic generating series*. URL: <https://oeis.org/A174193>.

*Commentary.*

The polynomial multiplying the square root is 1-6*x+x^2+34*x^3-26*x^4-4*x^5.

**Definition 1.4 (The denominator polynomial).**

$$D = 2 \cdot X^{2} \cdot (1 - X) \cdot p^{2}$$

*Formalization.* `D5/S1/Recurrence/Algebraic/MatharA174193OrderFourRecurrence.D` (`✓ std3`).

*Citation.* R. J. Mathar; OEIS Foundation Inc. (2016). *OEIS A174193 — an order-four recurrence for an algebraic generating series*. URL: <https://oeis.org/A174193>.

*Commentary.*

The denominator is 2*x^2*(1 -x)*(1- 4*x)^2; its constant coefficient is zero.

**Definition 1.5 (The exact algebraic source series).**

$$\forall A \in \operatorname{PowerSeries}\left(\mathbb{Q}\right),\; \operatorname{IsSourceSeries}\left(A\right) \Leftrightarrow \left(\exists s \in \operatorname{PowerSeries}\left(\mathbb{Q}\right),\; \operatorname{constantCoeff}\left(s\right) = 1 \land \left(s^{2} = p \land D \cdot A = P - B \cdot s\right)\right)$$

*Formalization.* `D5/S1/Recurrence/Algebraic/MatharA174193OrderFourRecurrence.IsSourceSeries` (`✓ std3`).

*Citation.* R. J. Mathar; OEIS Foundation Inc. (2016). *OEIS A174193 — an order-four recurrence for an algebraic generating series*. URL: <https://oeis.org/A174193>.

*Commentary.*

OEIS A174193, FORMULA section (no page numbers): “G.f.: (1-8*x+13*x^2+24*x^3-48*x^4-(1-6*x+x^2+34*x^3-26*x^4-4*x^5)*sqrt(1-4*x))/(2*x^2*(1 -x)*(1- 4*x)^2)”. The letters p, P, B and D denote the four polynomials above. A is the generating series and s is the square root with constant coefficient one. D*A=P-B*s expresses the source fraction after clearing its nonunit denominator; existence of A is asserted separately below.

**Definition 1.6 (Mathar's recurrence assertion).**

$$claim \Leftrightarrow \left(\left(\exists A \in \operatorname{PowerSeries}\left(\mathbb{Q}\right),\; \operatorname{IsSourceSeries}\left(A\right)\right) \land \left(\forall A \in \operatorname{PowerSeries}\left(\mathbb{Q}\right),\; \operatorname{IsSourceSeries}\left(A\right) \Rightarrow \left(\forall n \in \mathbb{N},\; 4 \le n \Rightarrow -((n:\mathbb{Q}) + 2) \cdot (404489 \cdot (n:\mathbb{Q}) - 1866368) \cdot \operatorname{coeff}\left(n, A\right) + (3147815 \cdot (n:\mathbb{Q})^{2} - 8680082 \cdot (n:\mathbb{Q}) - 14098754) \cdot \operatorname{coeff}\left(n - 1, A\right) + 2 \cdot (-2336439 \cdot (n:\mathbb{Q})^{2} + 652022 \cdot (n:\mathbb{Q}) + 14514849) \cdot \operatorname{coeff}\left(n - 2, A\right) + 8 \cdot (-1044770 \cdot (n:\mathbb{Q})^{2} + 10585023 \cdot (n:\mathbb{Q}) - 20370553) \cdot \operatorname{coeff}\left(n - 3, A\right) + 8 \cdot (642982 \cdot (n:\mathbb{Q}) - 2004177) \cdot (2 \cdot (n:\mathbb{Q}) - 9) \cdot \operatorname{coeff}\left(n - 4, A\right) = 0\right)\right)\right)$$

*Formalization.* `D5/S1/Recurrence/Algebraic/MatharA174193OrderFourRecurrence.claim` (`✓ std3`).

*Citation.* R. J. Mathar; OEIS Foundation Inc. (2016). *OEIS A174193 — an order-four recurrence for an algebraic generating series*. URL: <https://oeis.org/A174193>.

*Commentary.*

OEIS A174193, FORMULA section (no page numbers): “Conjecture: -(n+2)*(404489*n-1866368)*a(n) +(3147815*n^2-8680082*n-14098754)*a(n-1) +2*(-2336439*n^2+652022*n+14514849)*a(n-2) +8*(-1044770*n^2+10585023*n-20370553)*a(n-3) +8*(642982*n-2004177)*(2*n-9)*a(n-4)=0. - _R. J. Mathar_, Jun 14 2016”. Here a(n) is coeff n A. OEIS OFFSET 0,3 gives index zero to the first coefficient; the second offset component is metadata. All five sequence terms exist for n ≥ 4. The assertion includes existence of a source series and quantifies over every such A.

**Theorem 1.7 (The recurrence holds).**

$$\left(\exists A \in \operatorname{PowerSeries}\left(\mathbb{Q}\right),\; \operatorname{IsSourceSeries}\left(A\right)\right) \land \left(\forall A \in \operatorname{PowerSeries}\left(\mathbb{Q}\right),\; \operatorname{IsSourceSeries}\left(A\right) \Rightarrow \left(\forall n \in \mathbb{N},\; 4 \le n \Rightarrow -((n:\mathbb{Q}) + 2) \cdot (404489 \cdot (n:\mathbb{Q}) - 1866368) \cdot \operatorname{coeff}\left(n, A\right) + (3147815 \cdot (n:\mathbb{Q})^{2} - 8680082 \cdot (n:\mathbb{Q}) - 14098754) \cdot \operatorname{coeff}\left(n - 1, A\right) + 2 \cdot (-2336439 \cdot (n:\mathbb{Q})^{2} + 652022 \cdot (n:\mathbb{Q}) + 14514849) \cdot \operatorname{coeff}\left(n - 2, A\right) + 8 \cdot (-1044770 \cdot (n:\mathbb{Q})^{2} + 10585023 \cdot (n:\mathbb{Q}) - 20370553) \cdot \operatorname{coeff}\left(n - 3, A\right) + 8 \cdot (642982 \cdot (n:\mathbb{Q}) - 2004177) \cdot (2 \cdot (n:\mathbb{Q}) - 9) \cdot \operatorname{coeff}\left(n - 4, A\right) = 0\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Algebraic/MatharA174193OrderFourRecurrence.result` (`✓ std3`). ∎

*Resolves.* `Problems/mathar-a174193-order-four-recurrence` (proved) by `D5/S1/Recurrence/Algebraic/MatharA174193OrderFourRecurrence.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"mathar-a174193-order-four-recurrence","declaration_gid":"D5/S1/Recurrence/Algebraic/MatharA174193OrderFourRecurrence.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* R. J. Mathar; OEIS Foundation Inc. (2016). *OEIS A174193 — an order-four recurrence for an algebraic generating series*. URL: <https://oeis.org/A174193>.

*Commentary.*

Map the natural Catalan series to rational coefficients and set s=1-2*X*C. Its quadratic equation gives s^2=1-4*X. The numerator P-B*s has a factor X^2; the remaining denominator has constant coefficient two and is invertible. This constructs a source series. Differentiating its equation twice and cancelling nonzero polynomial factors yields a second-order Euler differential identity with a cubic right-hand side. The square-root terms cancel by two explicit polynomial identities. Coefficients of degree n ≥ 4 therefore give the displayed recurrence. The identification with the counting series of Av(321)^{+1}, and the background paper's Section 4 questions, are not proved here.

## References

- Truth anchor: `D5/S1/Recurrence/Algebraic/MatharA174193OrderFourRecurrence.B`
- Truth anchor: `D5/S1/Recurrence/Algebraic/MatharA174193OrderFourRecurrence.D`
- Truth anchor: `D5/S1/Recurrence/Algebraic/MatharA174193OrderFourRecurrence.IsSourceSeries`
- Truth anchor: `D5/S1/Recurrence/Algebraic/MatharA174193OrderFourRecurrence.P`
- Truth anchor: `D5/S1/Recurrence/Algebraic/MatharA174193OrderFourRecurrence.claim`
- Truth anchor: `D5/S1/Recurrence/Algebraic/MatharA174193OrderFourRecurrence.p`
- Truth anchor: `D5/S1/Recurrence/Algebraic/MatharA174193OrderFourRecurrence.result`
- Dependency: [D5/S1/Recurrence/A308815DFiniteRecurrence](../A308815DFiniteRecurrence.md)
