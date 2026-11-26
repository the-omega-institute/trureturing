# The sign needed for forward transport

## Abstract

Finite reduction of the weighted Robin budget

**Theorem 1.1 (Two-sided comparison with an explicit endpoint error).**

$$Wred - M \le W \land W \le Wred + M + \operatorname{sqrt}\left(Y\right) \cdot B^{kappa - \frac{1}{2}}$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/WeightedTailBudgetReduction.budget_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix 2 ≤ Y ≤ B ≤ C and 0 < κ ≤ 1/2. For a real kernel integrable on (Y, ∞), let Q be the ordinary tail, J the logarithmically weighted tail, a the inverse logarithmic weight, and E=Q−aJ. Assume the negative part of Q at u is at most u^(κ−1/2) on [Y,C].

W is the integral of a(t) times the negative part of J(t) against dt/sqrt(t), plus sqrt(Y) times the negative part of E(B). Let F(t) be the signed density tail at C plus the integral from t to C of the positive part of Q against the negative derivative of the weight. Form Wred using the positive part of a(t)F(t)−max(Q(t),0) in the integral and the negative part of a(B)F(B) at the endpoint.

The omitted negative tail is nonnegative and, after normalizing by a(t), is at most t^(κ−1/2). Subtracting it from the already bounded negative part of Q gives the pointwise error. Taking positive parts preserves the bound, whose integral is M=(B^κ−Y^κ)/κ. The endpoint contribution increases by at most sqrt(Y) B^(κ−1/2).

## References

- Truth anchor: `D5/S3/Weil/Mertens/WeightedTailBudgetReduction.budget_bounds`
- Dependency: [D5/S3/Weil/Mertens/WeightedTailWindowMass](WeightedTailWindowMass.md)
