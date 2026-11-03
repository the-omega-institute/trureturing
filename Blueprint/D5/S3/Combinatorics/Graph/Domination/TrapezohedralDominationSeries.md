# The complete formal generating series

## Abstract

The original A381190 rational generating function for all n>=3.

The coefficient ring is Q and x is the formal indeterminate X. The actualSeries coefficient of order n is the rational cast of actualCount n. Thus its coefficients at orders 0, 1 and 2 vanish, and every order n>=3 counts the original actual labelled subsets. No convergence, eventual recurrence, finite extrapolation, actual-count hypothesis or replacement graph is used.

**Definition 1.1 (The literal actual-count series).**

$$\forall (n : \mathbb{N}), \operatorname{coeff}\left(n, \operatorname{actualSeries}\left(\right)\right) = \operatorname{castToQ}\left(\operatorname{actualCount}\left(n\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/TrapezohedralDominationSeries.actualSeries` (`✓ std3`).

*Citation.* Eric W. Weisstein; Joerg Arndt; Peter Luschny; Emily Egolf; Veronika Furst (2026). *OEIS A381190, connected minimal dominating sets in the n-trapezohedral graph*. URL: <https://oeis.org/A381190>.

*Commentary.*

This is PowerSeries.mk applied to the rational actual-count sequence. castToQ denotes the natural-number cast into Q.

**Theorem 1.2 (The original polynomial and squared denominator).**

$$\operatorname{actualSeries}\left(\right) = \frac{-2 \cdot (\operatorname{X}\left(\right))^{3} \cdot (4 \cdot (\operatorname{X}\left(\right))^{5} + 8 \cdot (\operatorname{X}\left(\right))^{4} + 4 \cdot (\operatorname{X}\left(\right))^{3} - 9 \cdot (\operatorname{X}\left(\right))^{2} - 8 \cdot \operatorname{X}\left(\right) - 3)}{((\operatorname{X}\left(\right))^{3} + (\operatorname{X}\left(\right))^{2} - 1)^{2}}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Domination/TrapezohedralDominationSeries.actual_series` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a381190-trapezohedral-domination-series` (proved) by `D5/S3/Combinatorics/Graph/Domination/TrapezohedralDominationSeries.actual_series`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a381190-trapezohedral-domination-series","declaration_gid":"D5/S3/Combinatorics/Graph/Domination/TrapezohedralDominationSeries.actual_series","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Eric W. Weisstein; Joerg Arndt; Peter Luschny; Emily Egolf; Veronika Furst (2026). *OEIS A381190, connected minimal dominating sets in the n-trapezohedral graph*. URL: <https://oeis.org/A381190>.

*Commentary.*

Let M count native path maximal independent subsets and r the endpoint-restricted count with the zero prefix. The proved inverse head/tail maps give M(n+3)=M(n+1)+M(n), with M(0)=M(1)=1 and M(2)=2. The inverse endpoint/middle maps give r(n+4)+M(n)=M(n+4), and r(3)=1. Coefficientwise formal identities yield F(1-x^2-x^3)=1+x+x^2 and R(1-x^2-x^3)=x^3+2x^4+2x^5. The actual-set bijections give actualSeries=2xR'. Differentiating the second identity and multiplying by the unit denominator proves the displayed expression. In Lean the fraction is multiplication by the inverse of the squared power-series denominator; its constant coefficient is 1, so this is the literal rational formal series. All hypotheses are discharged by actual set constructions and the entire count sequence is included.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/TrapezohedralDominationSeries.actualSeries`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/TrapezohedralDominationSeries.actual_series`
- Dependency: [D5/S3/Combinatorics/Graph/Domination/TrapezohedralPathEquivalence](TrapezohedralPathEquivalence.md)
