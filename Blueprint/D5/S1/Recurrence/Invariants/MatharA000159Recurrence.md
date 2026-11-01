# Mathar's Six-Step Recurrence for Three-Hit Ménage Numbers

## Abstract

The three-hit ménage coefficients satisfy Mathar's six-step recurrence.

U is a polynomial over the rational numbers. Polynomial.C embeds a rational as a constant polynomial, Polynomial.X is the indeterminate, and Polynomial.coeff extracts a coefficient. All indices are natural numbers. Subtractions in indices, factorial arguments and binomial arguments are natural subtraction; the sum has k at most n, so these subtractions agree with integer subtraction. The quotients and displayed casts have values in the rational numbers. For n positive every summand denominator is at least n. The recurrence uses n at least nine, so each sequence argument is at least three.

**Definition 1.1 (The ménage hit polynomial).**

$$\forall n: \mathbb{N}, \operatorname{U}\left(n\right) = \operatorname{ite}\left(n = 0, 1, \sum_{k \in \operatorname{Finset}.\operatorname{range}\left(n + 1\right)} \operatorname{Polynomial}.\operatorname{C}\left(\frac{(2 \cdot n: \mathbb{Q})}{(2 \cdot n - k: \mathbb{Q})} \cdot (\operatorname{Nat}.\operatorname{choose}\left(2 \cdot n - k, k\right): \mathbb{Q}) \cdot (\operatorname{Nat}.\operatorname{factorial}\left(n - k\right): \mathbb{Q})\right) \cdot (\operatorname{Polynomial}.\operatorname{X} - 1)^{k}\right)$$

*Formalization.* `D5/S1/Recurrence/Invariants/MatharA000159Recurrence.U` (`✓ std3`).

*Citation.* R. J. Mathar (2015). *OEIS A000159: six-step recurrence for three-hit ménage numbers*. URL: <https://oeis.org/A000159>.

*Commentary.*

The unpaginated OEIS A058087 FORMULA field states: "Row n of the triangle lists the coefficients of the polynomial U_n(t) = Sum_{k=0..n} (2*n/(2*n-k))*binomial(2*n-k,k)*(n-k)!*(t-1)^k, with higher order terms first (Kaplansky and Riordan)." Its Maple definition begins "U := proc(n) if n = 0 then return 1 fi;". U uses this constant branch at zero and the quoted finite sum at positive n.

**Definition 1.2 (The three-hit coefficient).**

$$\forall n: \mathbb{N}, \operatorname{a}\left(n\right) = \operatorname{Polynomial}.\operatorname{coeff}\left(\operatorname{U}\left(n\right), 3\right)$$

*Formalization.* `D5/S1/Recurrence/Invariants/MatharA000159Recurrence.a` (`✓ std3`).

*Citation.* R. J. Mathar (2015). *OEIS A000159: six-step recurrence for three-hit ménage numbers*. URL: <https://oeis.org/A000159>.

*Commentary.*

The unpaginated OEIS A000159 NAME field states: "a(n) = A058087(n,n-3)." The A058087 NAME field states: "Triangle read by rows, giving coefficients of the ménage hit polynomials ordered by descending powers. T(n, k) for 0 <= k <= n." Thus a(n) is the coefficient of degree three in U(n). The source offset is 3,1.

**Definition 1.3 (The six-step recurrence proposition).**

$$\operatorname{claim} = (\forall n: \mathbb{N}, 9 \le n \implies \begin{aligned}(2 \cdot (-252307 \cdot (n: \mathbb{Q}) + 1041077)) \cdot \operatorname{a}\left(n\right)\\+(504614 \cdot ((n: \mathbb{Q}))^{2} - 3362985 \cdot (n: \mathbb{Q}) + 5118150) \cdot \operatorname{a}\left(n - 1\right)\\+(1280831 \cdot ((n: \mathbb{Q}))^{2} - 7397886 \cdot (n: \mathbb{Q}) + 6461565) \cdot \operatorname{a}\left(n - 2\right)\\+(746598 \cdot ((n: \mathbb{Q}))^{2} - 2913543 \cdot (n: \mathbb{Q}) - 1336090) \cdot \operatorname{a}\left(n - 3\right)\\+(-405481 \cdot ((n: \mathbb{Q}))^{2} + 6175011 \cdot (n: \mathbb{Q}) - 15469320) \cdot \operatorname{a}\left(n - 4\right)\\+(-375862 \cdot ((n: \mathbb{Q}))^{2} + 4098537 \cdot (n: \mathbb{Q}) - 8846430) \cdot \operatorname{a}\left(n - 5\right)\\+(2 \cdot (-187931 \cdot (n: \mathbb{Q}) + 560630)) \cdot \operatorname{a}\left(n - 6\right)\\= 0\end{aligned})$$

*Formalization.* `D5/S1/Recurrence/Invariants/MatharA000159Recurrence.claim` (`✓ std3`).

*Citation.* R. J. Mathar (2015). *OEIS A000159: six-step recurrence for three-hit ménage numbers*. URL: <https://oeis.org/A000159>.

*Commentary.*

The unpaginated OEIS A000159 first FORMULA field states: "Conjecture: 2*(-252307*n + 1041077)*a(n) + (504614*n^2 - 3362985*n + 5118150)*a(n-1) + (1280831*n^2 - 7397886*n + 6461565)*a(n-2) + (746598*n^2 - 2913543*n - 1336090)*a(n-3) + (-405481*n^2 + 6175011*n - 15469320)*a(n-4) + (-375862*n^2 + 4098537*n - 8846430)*a(n-5) + 2*(-187931*n + 560630)*a(n-6) = 0." — R. J. Mathar, Nov 02 2015. The quantifier ranges over every natural n at least nine, the first index whose six backward shifts all belong to the sequence's domain.

**Theorem 1.4 (The recurrence holds at every source-domain index).**

$$\forall n: \mathbb{N}, 9 \le n \implies \begin{aligned}(2 \cdot (-252307 \cdot (n: \mathbb{Q}) + 1041077)) \cdot \operatorname{a}\left(n\right)\\+(504614 \cdot ((n: \mathbb{Q}))^{2} - 3362985 \cdot (n: \mathbb{Q}) + 5118150) \cdot \operatorname{a}\left(n - 1\right)\\+(1280831 \cdot ((n: \mathbb{Q}))^{2} - 7397886 \cdot (n: \mathbb{Q}) + 6461565) \cdot \operatorname{a}\left(n - 2\right)\\+(746598 \cdot ((n: \mathbb{Q}))^{2} - 2913543 \cdot (n: \mathbb{Q}) - 1336090) \cdot \operatorname{a}\left(n - 3\right)\\+(-405481 \cdot ((n: \mathbb{Q}))^{2} + 6175011 \cdot (n: \mathbb{Q}) - 15469320) \cdot \operatorname{a}\left(n - 4\right)\\+(-375862 \cdot ((n: \mathbb{Q}))^{2} + 4098537 \cdot (n: \mathbb{Q}) - 8846430) \cdot \operatorname{a}\left(n - 5\right)\\+(2 \cdot (-187931 \cdot (n: \mathbb{Q}) + 560630)) \cdot \operatorname{a}\left(n - 6\right)\\= 0\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/MatharA000159Recurrence.result` (`✓ std3`). ∎

*Resolves.* `Problems/mathar-a000159-recurrence` (proved) by `D5/S1/Recurrence/Invariants/MatharA000159Recurrence.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"mathar-a000159-recurrence","declaration_gid":"D5/S1/Recurrence/Invariants/MatharA000159Recurrence.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* R. J. Mathar (2015). *OEIS A000159: six-step recurrence for three-hit ménage numbers*. URL: <https://oeis.org/A000159>.

*Commentary.*

Coefficient extraction converts the rook sum into a rational affine expression in the factorial series evaluated at X/(1+X)^2. The factorial series satisfies a first-order formal differential equation. After differentiating and clearing denominators, the resulting second-order equation has polynomial forcing of degree five. Its coefficient at n at least nine is exactly the displayed recurrence. The argument uses formal power series and does not require convergence or an inverse of the indeterminate.

## References

- Truth anchor: `D5/S1/Recurrence/Invariants/MatharA000159Recurrence.U`
- Truth anchor: `D5/S1/Recurrence/Invariants/MatharA000159Recurrence.a`
- Truth anchor: `D5/S1/Recurrence/Invariants/MatharA000159Recurrence.claim`
- Truth anchor: `D5/S1/Recurrence/Invariants/MatharA000159Recurrence.result`
- Dependency: [D5/S1/Recurrence/Residue/CompositionalSquareDyadicDenominators](../Residue/CompositionalSquareDyadicDenominators.md)
