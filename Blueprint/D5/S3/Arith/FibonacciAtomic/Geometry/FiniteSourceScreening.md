# Finite Source Screening

## Abstract

Actual path gradients connect the finite counting Laplacian with the uniformly weighted node space.

**Definition 1.1 (Potential).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/FiniteSourceScreening.Potential`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/FiniteSourceScreening.Potential` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A concrete potential assigns a real value to every original occurrence node, including the root and terminal nodes.

**Definition 1.2 (rootNode).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/FiniteSourceScreening.rootNode`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/FiniteSourceScreening.rootNode` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The root is the reached empty address.

**Definition 1.3 (nodeLp).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/FiniteSourceScreening.nodeLp`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/FiniteSourceScreening.nodeLp` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A concrete potential is represented in the actual node L2 space with uniform mass 1/N(n).

**Definition 1.4 (child).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/FiniteSourceScreening.child`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/FiniteSourceScreening.child` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each reached nonempty address identifies the child endpoint of one original edge.

**Definition 1.5 (parent).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/FiniteSourceScreening.parent`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/FiniteSourceScreening.parent` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Deleting the final direction gives the reached parent endpoint. Prefix closure supplies membership in the same source.

**Definition 1.6 (gradient).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/FiniteSourceScreening.gradient`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/FiniteSourceScreening.gradient` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The gradient is parent value minus child value on every reached edge, extended by zero to all absent coordinates of the common real edge Hilbert space.

**Definition 1.7 (Supported).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/FiniteSourceScreening.Supported`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/FiniteSourceScreening.Supported` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An edge vector is supported when all coordinates outside the actual reached edge set vanish.

**Definition 1.8 (reconstruct).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/FiniteSourceScreening.reconstruct`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/FiniteSourceScreening.reconstruct` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Reconstruction subtracts the root-to-node sum of edge coordinates from the prescribed root value.

**Definition 1.9 (countingLaplacian).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/FiniteSourceScreening.countingLaplacian`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/FiniteSourceScreening.countingLaplacian` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The counting Laplacian sums the signed contributions of each original unit-conductance parent-child edge exactly once. The root has no killing term.

**Definition 1.10 (nodeEquiv).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/FiniteSourceScreening.nodeEquiv`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/FiniteSourceScreening.nodeEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The uniform L2 representation is a continuous linear equivalence. Positive mass at every actual occurrence makes concrete potentials faithful, and every L2 element has a concrete representative.

**Definition 1.11 (L).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/FiniteSourceScreening.L`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/FiniteSourceScreening.L` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The actual counting Laplacian acts on NodeL2 by transport through the faithful concrete-potential equivalence.

**Definition 1.12 (root).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/FiniteSourceScreening.root`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/FiniteSourceScreening.root` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Root evaluation is the continuous linear functional obtained from the actual empty-address coordinate.

**Definition 1.13 (source).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/FiniteSourceScreening.source`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/FiniteSourceScreening.source` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The source is the counting root delta represented in uniform NodeL2; pairing with a concrete potential gives its root value divided by N(n).

**Theorem 1.14 (Actual reconstruction and energy).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/FiniteSourceScreening.actual_reconstruction_energy`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Geometry/FiniteSourceScreening.actual_reconstruction_energy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Path sums telescope to the root value minus the node value. Conversely, every supported edge vector is recovered as the gradient of its reconstructed potential. Summing the signed edge contributions gives counting integration by parts; passing to uniform node measure introduces exactly the factor N(n). The reconstructed L2 potential is c times the constant one minus J(n)z. All assertions quantify over every natural source index, so empty edge sums are included.

**Definition 1.15 (unitInverse).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/FiniteSourceScreening.unitInverse`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/FiniteSourceScreening.unitInverse` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a complete real inner-product space, unitInverse attaches the inverse continuous linear map to an explicit IsUnit proof.

**Theorem 1.16 (Actual node-space bridge).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/FiniteSourceScreening.actual_screening_bridge`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Geometry/FiniteSourceScreening.actual_screening_bridge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every actual node-space potential decomposes into its root value and supported path increments. The transported counting Laplacian has the supported-edge bilinear energy with the exact factor N(n). Root evaluation and root-delta pairing give respectively c and c/N(n) on c times one minus J(n)z.

**Definition 1.17 (root_response).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/FiniteSourceScreening.root_response`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/FiniteSourceScreening.root_response` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a positive screening parameter, root_response evaluates the actual root delta through the proved inverse of the counting Laplacian plus lambda.

**Definition 1.18 (screened_inverse).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/FiniteSourceScreening.screened_inverse`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/FiniteSourceScreening.screened_inverse` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a positive screening parameter, screened_inverse is the proved inverse on the full common edge Hilbert space of I plus N(n) times lambda times the centered finite covariance.

**Theorem 1.19 (Centered counting response).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/FiniteSourceScreening.finite_source_screening`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Geometry/FiniteSourceScreening.finite_source_screening` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural source index n and positive lambda, the counting root response minus 1/(N(n) lambda) equals the inner product of v(n) with its image under the full common-edge inverse of I plus N(n) lambda Sigma(n). The root value and the path-gradient energy establish the original counting weak equation. This gives the exact constant-mode subtraction, including the edge-free sources at n=0 and n=1.

The source node spaces depend on n, while the edge space is common to all sources. Counting energy is unnormalized, node inner products use uniform mass 1/N(n), and all original edges have unit conductance. Positive screening gives a genuine inverse on the node space and on the full common edge space, including absent coordinates.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/FiniteSourceScreening.L`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/FiniteSourceScreening.Potential`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/FiniteSourceScreening.Supported`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/FiniteSourceScreening.actual_reconstruction_energy`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/FiniteSourceScreening.actual_screening_bridge`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/FiniteSourceScreening.child`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/FiniteSourceScreening.countingLaplacian`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/FiniteSourceScreening.finite_source_screening`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/FiniteSourceScreening.gradient`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/FiniteSourceScreening.nodeEquiv`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/FiniteSourceScreening.nodeLp`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/FiniteSourceScreening.parent`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/FiniteSourceScreening.reconstruct`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/FiniteSourceScreening.root`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/FiniteSourceScreening.rootNode`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/FiniteSourceScreening.root_response`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/FiniteSourceScreening.screened_inverse`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/FiniteSourceScreening.source`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/FiniteSourceScreening.unitInverse`
- Dependency: [D5/S3/Arith/FibonacciAtomic/Geometry/FiniteSourceCovariance](FiniteSourceCovariance.md)
