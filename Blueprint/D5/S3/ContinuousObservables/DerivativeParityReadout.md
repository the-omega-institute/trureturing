# Derivative Parity Readout

## Abstract

Scalar reflection and translation symmetries pass to the derivative readout.

**Theorem 1.1 (The balanced field is odd under reflection).**

$$\forall S \in Type, Zunit \in S \to \left(\mathbb{R} \to \mathbb{R}\right),\; ((\forall s \in S, eta \in \mathbb{R},\; \operatorname{DifferentiableAt}(\mathbb{R}, \operatorname{lambda}(u, Zunit\left(s, u\right)), eta)) \land (\forall s \in S, eta \in \mathbb{R},\; Zunit\left(s, -eta\right) = Zunit\left(s, eta\right))) \Rightarrow (\forall s \in S, eta \in \mathbb{R},\; balancedField\left(Zunit, s, -eta\right) = -balancedField\left(Zunit, s, eta\right)).$$

*Proof.* Machine-checked in Lean as `D5/S3/ContinuousObservables/DerivativeParityReadout.balanced_field_reflection_odd` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every parameter value, a differentiable scalar field that is even in eta has a derivative readout that is odd in eta.

The proof uses only the chain rule for eta mapped to -eta and uniqueness of derivatives. The concrete Z_unit family is intentionally left as an external parameter.

**Theorem 1.2 (The balanced field keeps the scalar period).**

$$\forall S \in Type, Zunit \in S \to \left(\mathbb{R} \to \mathbb{R}\right), period \in \mathbb{R},\; ((\forall s \in S, eta \in \mathbb{R},\; \operatorname{DifferentiableAt}(\mathbb{R}, \operatorname{lambda}(u, Zunit\left(s, u\right)), eta)) \land (\forall s \in S, eta \in \mathbb{R},\; Zunit\left(s, eta + period\right) = Zunit\left(s, eta\right))) \Rightarrow (\forall s \in S, eta \in \mathbb{R},\; balancedField\left(Zunit, s, eta + period\right) = balancedField\left(Zunit, s, eta\right)).$$

*Proof.* Machine-checked in Lean as `D5/S3/ContinuousObservables/DerivativeParityReadout.balanced_field_periodic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A differentiable scalar field periodic under a translation has a derivative readout with the same translation period.

Together the two declarations formalize formulas 765.1--765.3. The source's U^k J^epsilon action, lifted coordinate, connection memory, and arithmetic representation analogy remain outside this self-contained partial closure.

## References

- Truth anchor: `D5/S3/ContinuousObservables/DerivativeParityReadout.balanced_field_periodic`
- Truth anchor: `D5/S3/ContinuousObservables/DerivativeParityReadout.balanced_field_reflection_odd`
