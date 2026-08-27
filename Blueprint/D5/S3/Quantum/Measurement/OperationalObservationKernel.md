# Operational Observation Kernel and Metric

## Abstract

Positive weighted centered effects induce the residual kernel and operational metric.

**Definition 1.1 (Centered effects construct a weighted Euclidean analysis map).**

Lean statement: `D5/S3/Quantum/Measurement/OperationalObservationKernel.weightedEffectAnalysis`

*Formalization.* `D5/S3/Quantum/Measurement/OperationalObservationKernel.weightedEffectAnalysis` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each real trace-zero Hermitian direction is paired with every centered effect and scaled by the square root of its source weight.

**Definition 1.2 (The observation seminorm is the weighted analysis norm).**

Lean statement: `D5/S3/Quantum/Measurement/OperationalObservationKernel.operationalObservationSeminorm`

*Formalization.* `D5/S3/Quantum/Measurement/OperationalObservationKernel.operationalObservationSeminorm` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The Euclidean norm of the weighted analysis vector is exactly the source's positive weighted observation seminorm.

**Definition 1.3 (Density states have weighted centered-effect readouts).**

Lean statement: `D5/S3/Quantum/Measurement/OperationalObservationKernel.weightedDensityReadout`

*Formalization.* `D5/S3/Quantum/Measurement/OperationalObservationKernel.weightedDensityReadout` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A positive trace-one density state is sent to its finite vector of real trace pairings, with the same square-root weights.

**Definition 1.4 (State distance is Euclidean readout distance).**

Lean statement: `D5/S3/Quantum/Measurement/OperationalObservationKernel.operationalStateDistance`

*Formalization.* `D5/S3/Quantum/Measurement/OperationalObservationKernel.operationalStateDistance` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The induced distance compares only observer-accessible weighted readouts.

**Definition 1.5 (The operational quotient identifies equal readouts).**

Lean statement: `D5/S3/Quantum/Measurement/OperationalObservationKernel.OperationalStateQuotient`

*Formalization.* `D5/S3/Quantum/Measurement/OperationalObservationKernel.OperationalStateQuotient` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The carrier is the canonical quotient by the kernel Setoid of the weighted density-state readout.

**Definition 1.6 (Readout distance descends to operational classes).**

Lean statement: `D5/S3/Quantum/Measurement/OperationalObservationKernel.operationalQuotientDistance`

*Formalization.* `D5/S3/Quantum/Measurement/OperationalObservationKernel.operationalQuotientDistance` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Quotient.liftOn2 constructs the representative-independent distance directly on operational classes.

**Theorem 1.7 (The seminorm kernel is the invisible residual).**

$$\begin{gathered}\forall d: \mathbb{N}, \operatorname{NeZero}\left(d\right), A: \operatorname{Type},\\{}[\operatorname{Fintype}\left(A\right)], E: A \to \operatorname{Herm}_{d}^{0}, w: A \to \mathbb{R},\\{}(\forall i\in A, 0 < w(i)) \Rightarrow\\{}\operatorname{let} \forall D: \operatorname{Herm}_{d}^{0}, \left\lVert D \right\rVert_{O} = \sqrt{\sum_{i \in A} w(i) \langle D, E_{i} \rangle_{\mathbb{R}}^{2}},\\{}\forall \rho: \operatorname{DensityState}\left(\operatorname{Fin}\left(d\right)\right), i: A, q(\rho)(i) = \Re \operatorname{Tr}\left(\operatorname{matrix}\left(\rho\right) E_{i}\right), \forall \rho: \operatorname{DensityState}\left(\operatorname{Fin}\left(d\right)\right), i: A, q_{w}(\rho)(i) = \sqrt{w(i)} q(\rho)(i),\\{}\forall \rho: \operatorname{DensityState}\left(\operatorname{Fin}\left(d\right)\right), \sigma: \operatorname{DensityState}\left(\operatorname{Fin}\left(d\right)\right), d_{O}(\rho, \sigma) = \left\lVert q_{w}(\rho) - q_{w}(\sigma) \right\rVert_{2}, Q_{O} = \operatorname{DensityState}\left(\operatorname{Fin}\left(d\right)\right) / \operatorname{ker}\left(q_{w}\right),\\{}\forall \rho: \operatorname{DensityState}\left(\operatorname{Fin}\left(d\right)\right), \sigma: \operatorname{DensityState}\left(\operatorname{Fin}\left(d\right)\right), d_{quot}([\rho], [\sigma]) = d_{O}(\rho, \sigma),\\{}\operatorname{ker}\left(D \mapsto \left\lVert D \right\rVert_{O}\right) = \operatorname{span}\left(\mathbb{R}, \{E_{i}: i \in A\}\right)^{\perp} \land\\{}(\forall \rho: \operatorname{DensityState}\left(\operatorname{Fin}\left(d\right)\right), \sigma: \operatorname{DensityState}\left(\operatorname{Fin}\left(d\right)\right), 0 \leq d_{O}(\rho, \sigma)) \land (\forall \rho: \operatorname{DensityState}\left(\operatorname{Fin}\left(d\right)\right), d_{O}(\rho, \rho) = 0) \land\\{}(\forall \rho: \operatorname{DensityState}\left(\operatorname{Fin}\left(d\right)\right), \sigma: \operatorname{DensityState}\left(\operatorname{Fin}\left(d\right)\right), d_{O}(\rho, \sigma) = d_{O}(\sigma, \rho)) \land (\forall \rho: \operatorname{DensityState}\left(\operatorname{Fin}\left(d\right)\right), \sigma: \operatorname{DensityState}\left(\operatorname{Fin}\left(d\right)\right), tau: \operatorname{DensityState}\left(\operatorname{Fin}\left(d\right)\right), d_{O}(\rho, tau) \leq d_{O}(\rho, \sigma) + d_{O}(\sigma, tau)) \land\\{}(\forall u: Q_{O}, v: Q_{O}, 0 \leq d_{quot}(u, v)) \land (\forall u: Q_{O}, d_{quot}(u, u) = 0) \land\\{}(\forall u: Q_{O}, v: Q_{O}, d_{quot}(u, v) = d_{quot}(v, u)) \land (\forall u: Q_{O}, v: Q_{O}, z: Q_{O}, d_{quot}(u, z) \leq d_{quot}(u, v) + d_{quot}(v, z)) \land\\{}(\forall u: Q_{O}, v: Q_{O}, d_{quot}(u, v) = 0 \iff u = v) \land\\{}((\forall \rho: \operatorname{DensityState}\left(\operatorname{Fin}\left(d\right)\right), \sigma: \operatorname{DensityState}\left(\operatorname{Fin}\left(d\right)\right), d_{O}(\rho, \sigma) = 0 \iff \rho = \sigma) \iff \operatorname{Injective}\left(\rho: \operatorname{DensityState}\left(\operatorname{Fin}\left(d\right)\right) \mapsto (i: A \mapsto q(\rho)(i))\right)).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/OperationalObservationKernel.operational_observation_kernel_and_metric` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Strictly positive weights make a zero weighted coordinate equivalent to a zero trace pairing. Orthogonality to every effect therefore equals orthogonality to their real span.

Euclidean readout distance supplies the state pseudometric laws. Its canonical kernel quotient is separated and retains symmetry and the triangle inequality.

Because every square-root weight is nonzero, the weighted and unweighted state signatures have the same fibers. Full-state separation is therefore equivalent to informational completeness.

## References

- Truth anchor: `D5/S3/Quantum/Measurement/OperationalObservationKernel.OperationalStateQuotient`
- Truth anchor: `D5/S3/Quantum/Measurement/OperationalObservationKernel.operationalObservationSeminorm`
- Truth anchor: `D5/S3/Quantum/Measurement/OperationalObservationKernel.operationalQuotientDistance`
- Truth anchor: `D5/S3/Quantum/Measurement/OperationalObservationKernel.operationalStateDistance`
- Truth anchor: `D5/S3/Quantum/Measurement/OperationalObservationKernel.operational_observation_kernel_and_metric`
- Truth anchor: `D5/S3/Quantum/Measurement/OperationalObservationKernel.weightedDensityReadout`
- Truth anchor: `D5/S3/Quantum/Measurement/OperationalObservationKernel.weightedEffectAnalysis`
- Dependency: [D5/S3/Quantum/Tomography/InformationalCompletenessEquivalence](../Tomography/InformationalCompletenessEquivalence.md)
