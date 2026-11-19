# Exact full-vector two-point restriction

## Abstract

Exact full-vector two-point restriction.

**Theorem 1.1 (Exact full-vector two-point restriction).**

$$\forall i, \forall a, \forall v: \operatorname{TailVector}\left(i\right), \forall b: Bool, \operatorname{ProjectionEdgeAction}\left(i, a, v, b\right) = \operatorname{SourceQAction}\left(i, a, v, b\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/NativeReader/Edges.projection_edge_mulVec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The Boolean a selects physical address eleven when false and thirteen when true. The actual edge configurations differ only at tail position two or four, respectively. They are ordered by that physical center bit. The ready tail has center not-a, and the opposite configuration has center a. Both configurations are legal for each source sector. The exact block is sourceQ=((x,x*sqrt(x)),(x*sqrt(x),x*x)); there is no basis or gauge replacement.

ProjectionEdgeAction(i,a,v,b) is the ready-edge row of projection(i,changedAddress(a)) applied to the complete tail vector v. SourceQAction is (sourceQ*pairVector(i,a,v))(b). The theorem quantifies over both sectors, both addresses, every complete complex vector and both edge rows. The proof first shows every other legal tail contributes zero, then evaluates both retained entries using the original weights and sums the two-point support. The complete input vector remains unchanged as a domain object. pulse_pair transports this exact restriction to the full pulse and is consumed by charge conservation and uniform nonvanishing. The restriction does not authorize a projected state update.

## References

- Truth anchor: `D5/S3/Quantum/Dynamics/NativeReader/Edges.projection_edge_mulVec`
- Dependency: [D5/S3/Quantum/Dynamics/NativeReader/Pulses](Pulses.md)
