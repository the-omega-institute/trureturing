# Double-Extensional Supremum Pseudometrics

## Abstract

The state-row and protocol-column evaluation suprema are pseudometrics with the exact extensional kernels.

**Definition 1.1 (State distance is the protocol supremum).**

Lean statement: `D5/S3/Observer/MetricGeometryLaws/DualSupremumPseudometricKernels.stateObservationDistance`

*Formalization.* `D5/S3/Observer/MetricGeometryLaws/DualSupremumPseudometricKernels.stateObservationDistance` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For two states, stateObservationDistance is the supremum over every protocol of the law-carrier distance between their evaluations.

**Definition 1.2 (Protocol distance is the state supremum).**

Lean statement: `D5/S3/Observer/MetricGeometryLaws/DualSupremumPseudometricKernels.protocolResponseDistance`

*Formalization.* `D5/S3/Observer/MetricGeometryLaws/DualSupremumPseudometricKernels.protocolResponseDistance` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For two protocols, protocolResponseDistance is the supremum over every state of the law-carrier distance between their evaluations.

**Theorem 1.3 (Both supremum distances have the exact evaluation kernels).**

$$\begin{gathered}\forall State, Protocol, Law: Type,\\{}e: State \to \left(Protocol \to Law\right),\\{}\operatorname{MetricSpace}\left(Law\right) \land (\forall a, b\in Law, \operatorname{dist}\left(a, b\right) \leq 1) \Rightarrow\\{}(\forall x, y, z\in State,\\{}0 \leq stateObservationDistance(e, x, y) \land stateObservationDistance(e, x, x) = 0 \land\\{}stateObservationDistance(e, x, y) = stateObservationDistance(e, y, x) \land\\{}stateObservationDistance(e, x, y) \leq stateObservationDistance(e, x, z) + stateObservationDistance(e, z, y)) \land\\{}(\forall p, q, r\in Protocol,\\{}0 \leq protocolResponseDistance(e, p, q) \land protocolResponseDistance(e, p, p) = 0 \land\\{}protocolResponseDistance(e, p, q) = protocolResponseDistance(e, q, p) \land\\{}protocolResponseDistance(e, p, q) \leq protocolResponseDistance(e, p, r) + protocolResponseDistance(e, r, q)) \land\\{}(\forall x, y\in State, stateObservationDistance(e, x, y) = 0 \iff (\forall p\in Protocol, e(x, p) = e(y, p))) \land\\{}(\forall p, q\in Protocol, protocolResponseDistance(e, p, q) = 0 \iff (\forall x\in State, e(x, p) = e(x, q))).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/MetricGeometryLaws/DualSupremumPseudometricKernels.dual_supremum_pseudometric_kernels` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The shared law carrier is a metric space whose distances are bounded by one. Pointwise nonnegativity, symmetry, and the triangle law pass to each bounded real supremum.

The proof treats empty state and protocol types separately, so no unstated inhabitation or finiteness premise is added.

A supremum is zero exactly when every contributing metric distance is zero. Metric separation then identifies the zero-distance relations with equality of evaluation rows and columns, making the exact double-extensional quotients precisely the two zero-distance quotients.

## References

- Truth anchor: `D5/S3/Observer/MetricGeometryLaws/DualSupremumPseudometricKernels.dual_supremum_pseudometric_kernels`
- Truth anchor: `D5/S3/Observer/MetricGeometryLaws/DualSupremumPseudometricKernels.protocolResponseDistance`
- Truth anchor: `D5/S3/Observer/MetricGeometryLaws/DualSupremumPseudometricKernels.stateObservationDistance`
