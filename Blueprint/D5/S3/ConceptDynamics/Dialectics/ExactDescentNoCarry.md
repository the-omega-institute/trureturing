# Exact Descent Has No Carry

## Abstract

Exact descent through source and target readouts excludes every carry witness.

**Theorem 1.1 (Exact descent excludes carry).**

$$\begin{gathered}\forall X, Y, B, C: \operatorname{Type},\\{}q_{X}: X \to B, q_{Y}: Y \to C,\\{}F: X \to Y, \overline{F}: B \to C,\\{}q_{Y} \circ F = \overline{F} \circ q_{X} \Rightarrow\\{}\forall x, y\in X, \neg \operatorname{IsCarryWitness}\left(q_{X}, id_{X}, {q_{Y} \circ F}, x, y\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Dialectics/ExactDescentNoCarry.exact_descent_has_no_carry` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The source readout, target readout, flow, and descended map are independent public primitives. Exact commutation is assumed, rather than installed by a definition.

A carry is the existing family predicate: two states have the same source readout but different target readouts after the flow. Applying the descended map to the source equality contradicts the target inequality.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Dialectics/ExactDescentNoCarry.exact_descent_has_no_carry`
- Dependency: [D5/S3/ConceptDynamics/Dialectics/MinimalDialecticalRepair](MinimalDialecticalRepair.md)
