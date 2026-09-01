# Trace Pairings for Weyl Displacement Words

## Abstract

Weyl displacement words have trace M at the zero index and zero trace elsewhere; their trace pairings are M at equal indices and zero otherwise.

**Theorem 1.1 (Vanishing trace away from the origin).**

$$\forall M: \mathbb{N},\ [\operatorname{NeZero}(M)],\ \forall e, f: \operatorname{ZMod}(M),\ {e \neq 0 \lor f \neq 0} \implies \operatorname{trace}\left(\operatorname{displacement}\left(M, e, f\right)\right) = 0.$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/WeylDisplacementTrace.displacement_trace_eq_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A displacement word has zero trace whenever at least one of its two residue indices is nonzero.

**Theorem 1.2 (Trace at the origin).**

$$\forall M: \mathbb{N},\ [\operatorname{NeZero}(M)],\ \operatorname{trace}\left(\operatorname{displacement}\left(M, 0, 0\right)\right) = {M: \mathbb{C}}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/WeylDisplacementTrace.displacement_trace_origin` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At the zero index, the trace of the displacement word is the window cardinality M.

**Theorem 1.3 (Trace of a displacement word).**

$$\forall M: \mathbb{N},\ [\operatorname{NeZero}(M)],\ \forall e, f: \operatorname{ZMod}(M),\ \operatorname{trace}\left(\operatorname{displacement}\left(M, e, f\right)\right) = \begin{cases}{M: \mathbb{C}},&e = 0 \land f = 0\\0,&\text{otherwise}\end{cases}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/WeylDisplacementTrace.displacement_trace` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The trace of a displacement word is M when both residue indices vanish and zero otherwise.

**Theorem 1.4 (Pairwise orthogonality for the trace form).**

$$\forall M: \mathbb{N},\ [\operatorname{NeZero}(M)],\ \forall a, b, c, d: \operatorname{ZMod}(M),\ \operatorname{trace}\left(\operatorname{star}\left(\operatorname{displacement}\left(M, a, b\right)\right) \cdot \operatorname{displacement}\left(M, c, d\right)\right) = \begin{cases}{M: \mathbb{C}},&a = c \land b = d\\0,&\text{otherwise}\end{cases}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/WeylDisplacementTrace.displacement_trace_orthogonal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The trace pairing of two displacement words is M when their two residue indices agree and zero otherwise; hence distinct indices are orthogonal for this trace form.

This is the pairing identity itself. This module proves no conclusion about linear independence, spanning, or a basis, and it must not be read as asserting any such conclusion.

## References

- Truth anchor: `D5/S3/Quantum/Algebra/WeylDisplacementTrace.displacement_trace`
- Truth anchor: `D5/S3/Quantum/Algebra/WeylDisplacementTrace.displacement_trace_eq_zero`
- Truth anchor: `D5/S3/Quantum/Algebra/WeylDisplacementTrace.displacement_trace_origin`
- Truth anchor: `D5/S3/Quantum/Algebra/WeylDisplacementTrace.displacement_trace_orthogonal`
- Dependency: [D5/S3/Quantum/Algebra/WeylDisplacementAdjoint](WeylDisplacementAdjoint.md)
