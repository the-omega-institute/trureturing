# Curtz's OEIS A189733 denominator conjecture

## Abstract

The reduced denominators of Curtz's rational triangle satisfy all six residue formulas.

All indices are natural numbers and all triangle values are rational. Write T for triangle and let den be the reduced rational denominator, including den(0)=1. The upper-triangular source array is reindexed by T(m,k)=B(m,m+k). Boundary cases take precedence over the recurrence. The lower-triangular extension is not used.

**Definition 1.1 (The literal rational triangle).**

$$\forall m \in \mathrm{Nat},\; \begin{aligned}\operatorname{T}\left(m, 0\right) = 0\\\operatorname{T}\left(m, 1\right) = ((-1)^{m}) / (m + 1)\\\forall k \in \mathrm{Nat},\; \operatorname{T}\left(m, k + 2\right) = \operatorname{T}\left(m, k + 1\right) + \operatorname{T}\left(m + 1, k\right)\end{aligned}$$

*Formalization.* `D5/S1/Recurrence/Residue/OEISA189733DenominatorConjecture.triangle` (`✓ std3`).

*Citation.* Paul Curtz (2011). *OEIS A189733, denominators of the first row of a rational difference array*. URL: <https://oeis.org/A189733>.

*Commentary.*

The three branches uniquely define the array by induction on the second index. In the source first-superdiagonal formula the exponent is m+2, giving the same sign as m. No closed form is assumed.

**Definition 1.2 (The denominator sequence).**

$$\forall n \in \mathrm{Nat},\; \operatorname{a}\left(n\right) = \operatorname{den}\left(\operatorname{T}\left(0, n\right)\right)$$

*Formalization.* `D5/S1/Recurrence/Residue/OEISA189733DenominatorConjecture.a` (`✓ std3`).

*Citation.* Paul Curtz (2011). *OEIS A189733, denominators of the first row of a rational difference array*. URL: <https://oeis.org/A189733>.

*Commentary.*

This is the actual reduced denominator of the zeroth-row entry, not the denominator of an unreduced expression.

**Theorem 1.3 (The six universal denominator formulas).**

$$\forall k \in \mathrm{Nat},\; (\operatorname{a}\left(6 \cdot k\right), \operatorname{a}\left(6 \cdot k + 1\right), \operatorname{a}\left(6 \cdot k + 2\right), \operatorname{a}\left(6 \cdot k + 3\right), \operatorname{a}\left(6 \cdot k + 4\right), \operatorname{a}\left(6 \cdot k + 5\right)) = (1, 3 \cdot k + 1, 2 \cdot k + 1, 3 \cdot k + 2, 1, 6 \cdot k + 6)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Residue/OEISA189733DenominatorConjecture.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a189733-curtz-denominator-conjecture` (proved) by `D5/S1/Recurrence/Residue/OEISA189733DenominatorConjecture.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a189733-curtz-denominator-conjecture","declaration_gid":"D5/S1/Recurrence/Residue/OEISA189733DenominatorConjecture.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Paul Curtz (2011). *OEIS A189733, denominators of the first row of a rational difference array*. URL: <https://oeis.org/A189733>.

*Commentary.*

The assertion includes k=0 and has no additional hypotheses. Finite polynomial moments connect the source recursion to the companion polynomials. The derivative identity gives an endpoint difference, and the recurrence at X=1 supplies period six. Positive reciprocal denominators then give the displayed reduced values.

For the algebraic argument, define rational polynomials Q and L and a finite coefficient moment J as follows. The sum ranges over the finite support of P; X is the polynomial variable.

$$
\begin{aligned}(\operatorname{Q}\left(0\right), \operatorname{Q}\left(1\right)) = (0, 1)\\(\operatorname{L}\left(0\right), \operatorname{L}\left(1\right)) = (2, 1)\\\operatorname{Q}\left(n + 2\right) = \operatorname{Q}\left(n + 1\right) - X \cdot \operatorname{Q}\left(n\right)\\\operatorname{L}\left(n + 2\right) = \operatorname{L}\left(n + 1\right) - X \cdot \operatorname{L}\left(n\right)\\\operatorname{J}\left(m, P\right) = \sum_{i\in\operatorname{support}\left(P\right)}(\operatorname{coeff}\left(P, i\right)) / (m + i + 1)\end{aligned}
$$

Multiplication by X shifts the moment index from m to m+1. Induction on the source recursion proves the first identity below. The companion relation proves the derivative identity by induction. On each monomial, J(0,P') equals the difference of its endpoint values, so linearity gives the last identity.

$$
\begin{aligned}\operatorname{T}\left(m, n\right) = (-1)^{m} \cdot \operatorname{J}\left(m, \operatorname{Q}\left(n\right)\right)\\\operatorname{L}\left(n + 1\right) = \operatorname{Q}\left(n + 1\right) - 2 \cdot X \cdot \operatorname{Q}\left(n\right)\\\operatorname{derivative}\left(\operatorname{L}\left(n + 1\right)\right) = -(n + 1) \cdot \operatorname{Q}\left(n\right)\\\operatorname{T}\left(0, n\right) = (1 - \operatorname{eval}\left(\operatorname{L}\left(n + 1\right), 1\right)) / (n + 1)\end{aligned}
$$

At X=1, the companion recurrence has initial values two and one and repeats after six steps. Its six consecutive values are 2, 1, -1, -2, -1, 1. Substitution in the endpoint identity yields the following exact rational values for every k.

$$
\forall k \in \mathrm{Nat},\; (\operatorname{T}\left(0, 6 \cdot k\right), \operatorname{T}\left(0, 6 \cdot k + 1\right), \operatorname{T}\left(0, 6 \cdot k + 2\right), \operatorname{T}\left(0, 6 \cdot k + 3\right), \operatorname{T}\left(0, 6 \cdot k + 4\right), \operatorname{T}\left(0, 6 \cdot k + 5\right)) = (0, (1) / (3 \cdot k + 1), (1) / (2 \cdot k + 1), (1) / (3 \cdot k + 2), 0, -(1) / (6 \cdot k + 6))
$$

The source and exact assertion are also recorded at https://github.com/the-omega-institute/trureturing/issues/25342. The conclusion concerns the six formulas in OEIS A189733; it makes no claim of exhaustive literature coverage or worldwide priority.

## References

- Truth anchor: `D5/S1/Recurrence/Residue/OEISA189733DenominatorConjecture.a`
- Truth anchor: `D5/S1/Recurrence/Residue/OEISA189733DenominatorConjecture.result`
- Truth anchor: `D5/S1/Recurrence/Residue/OEISA189733DenominatorConjecture.triangle`
