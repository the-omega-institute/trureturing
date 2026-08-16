# Geometric Numerator Parity

## Abstract

A geometric numerator cancels the quadratic denominator exactly at even capacities.

**Theorem 1.1 (The quadratic denominator divides exactly at even capacities).**

$$\forall cap \in \mathbb{N},\ (X^{2}-1) \mid (X^{cap}-1) \iff \operatorname{Even}(cap).$$

*Proof.* Machine-checked in Lean as `D5/S3/AnalyticClosure/GeometricNumeratorParity.geometric_numerator_divisible_iff_even` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the integer polynomial X^cap-1, the factor X^2-1 cancels exactly when cap is even. In the forward direction, evaluating a claimed divisibility at X=-1 forces (-1)^cap=1 and hence even parity. In the reverse direction, even parity gives 2 divides cap, so Mathlib's generic power-difference divisibility theorem applies directly.

This closes only clause (ii) of source theorem 6.53: the parity criterion for cancellation of the geometric numerator by the quadratic denominator. It does not close the fiber bijection, the row-tail residue identification, the generating-function coefficient formula, or the subsequent numerical predictions in the same atom.

Repository and pinned-Mathlib searches found no exact biconditional. The proof reuses dvd_pow_sub_one_of_dvd, Polynomial.eval_dvd, and neg_one_pow_eq_one_iff_even. An external GitHub and Loogle domain search through NyxID and Tavily found no exact match.

## References

- Truth anchor: `D5/S3/AnalyticClosure/GeometricNumeratorParity.geometric_numerator_divisible_iff_even`
