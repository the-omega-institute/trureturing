# Exact Maximum of a Rational Repulsion Profile

## Abstract

A positive rational repulsion profile has an attained square-root maximum.

**Theorem 1.1 (The rational repulsion profile has an exact attained maximum).**

$$\forall a, b, u \in \mathbb{R},\ 0 < b < a \land 0 < u \Rightarrow \operatorname{IsGreatest}(\left\{\frac{a}{w + u} - \frac{b}{w} \mid w > 0\right\},\ \frac{(\sqrt{a} - \sqrt{b})^{2}}{u}).$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/Repulsion/RepulsionMaximum.repulsion_profile_has_exact_maximum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive b below a and positive u, every value of the profile a/(w+u) - b/w at positive w is bounded above by (sqrt(a)-sqrt(b))^2/u, and that bound is attained.

The proof rewrites the difference between the proposed maximum and the profile as ((sqrt(a)-sqrt(b))w-sqrt(b)u)^2 divided by u w (w+u). The denominator is positive, so the square gives the global upper bound. Taking w = sqrt(b)u/(sqrt(a)-sqrt(b)) makes the square vanish and supplies the maximizing witness.

This document closes only the one-line optimization lemma in the first part of the source remark. It does not formalize the subsequent zeta zero hypotheses, normalized exclusion curve, or directional Deuring--Heilbronn interpretation.

## References

- Truth anchor: `D5/S3/Zeros/Repulsion/RepulsionMaximum.repulsion_profile_has_exact_maximum`
