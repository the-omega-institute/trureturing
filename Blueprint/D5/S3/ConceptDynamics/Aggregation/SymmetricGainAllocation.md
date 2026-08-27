# Symmetric Gain Allocation

## Abstract

Equal gains above a feasible disagreement point uniquely split the residual resource.

**Theorem 1.1 (Equal gains uniquely determine the allocation).**

$$\begin{gathered}\forall d_{1}, d_{2}: \mathbb{R},\\{}d_{1} + d_{2} \leq 1 \Rightarrow \\{}\exists! x: \operatorname{Prod}\left(\mathbb{R}, \mathbb{R}\right),\\{}x_{1} + x_{2} = 1 \land \\{}x_{1} - d_{1} = x_{2} - d_{2} \land \\{}x_{1} = d_{1} + \frac{1 - d_{1} - d_{2}}{2} \land \\{}x_{2} = d_{2} + \frac{1 - d_{1} - d_{2}}{2} \land \\{}x_{1} - d_{1} = \frac{1 - d_{1} - d_{2}}{2} \land \\{}x_{2} - d_{2} = \frac{1 - d_{1} - d_{2}}{2} \land \\{}0 \leq \frac{1 - d_{1} - d_{2}}{2}.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Aggregation/SymmetricGainAllocation.symmetric_gain_allocation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The disagreement coordinates are arbitrary real anchors whose sum is at most one. The public statement gives the unique efficient pair with equal gains above those anchors.

Both allocation coordinates and both gains are displayed explicitly. Feasibility makes the common half-residual gain nonnegative, so the split is relative to the disagreement point rather than an absolute midpoint.

Ring normalization establishes the equalities, and real linear arithmetic uses the feasibility premise for nonnegativity.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Aggregation/SymmetricGainAllocation.symmetric_gain_allocation`
