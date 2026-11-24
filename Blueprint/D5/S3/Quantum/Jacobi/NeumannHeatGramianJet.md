# The zero-net Gramian jet of a lumped Neumann path

## Abstract

A zero-net input removes an additive constant in the endpoint heat response. For two positive Neumann paths with a common prefix, the first changed return moment determines the first changed Gramian coefficient.

**Definition 1.1 (Formal time average).**

Lean statement: `D5/S3/Quantum/Jacobi/NeumannHeatGramianJet.timeAverage`

*Formalization.* `D5/S3/Quantum/Jacobi/NeumannHeatGramianJet.timeAverage` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The coefficient of degree r in the time average is the original coefficient divided by r+1. Multiplying the result by time gives the formal integral with zero constant term.

**Definition 1.2 (The centered Gramian).**

Lean statement: `D5/S3/Quantum/Jacobi/NeumannHeatGramianJet.gramian`

*Formalization.* `D5/S3/Quantum/Jacobi/NeumannHeatGramianJet.gramian` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Integrate the square of the heat response from zero and subtract time times the square of its mean. Shifting the response by a constant leaves this series invariant. Its derivative is the square of the difference between the time average and the response.

**Definition 1.3 (Positive finite paths).**

Lean statement: `D5/S3/Quantum/Jacobi/NeumannHeatGramianJet.Path`

*Formalization.* `D5/S3/Quantum/Jacobi/NeumannHeatGramianJet.Path` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The n positive edge lengths are ordered from the measured endpoint.

**Definition 1.4 (Edge lengths).**

Lean statement: `D5/S3/Quantum/Jacobi/NeumannHeatGramianJet.edge`

*Formalization.* `D5/S3/Quantum/Jacobi/NeumannHeatGramianJet.edge` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Edge i joins vertices i and i+1 for i below n. The edge-length sequence is extended by zero at and beyond n.

**Definition 1.5 (Lumped vertex mass).**

Lean statement: `D5/S3/Quantum/Jacobi/NeumannHeatGramianJet.mass`

*Formalization.* `D5/S3/Quantum/Jacobi/NeumannHeatGramianJet.mass` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The mass at a vertex is half the sum of the lengths of its incident edges.

**Definition 1.6 (Stiffness diagonal).**

Lean statement: `D5/S3/Quantum/Jacobi/NeumannHeatGramianJet.diagonal`

*Formalization.* `D5/S3/Quantum/Jacobi/NeumannHeatGramianJet.diagonal` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Divide the sum of incident conductances by the vertex mass. Each conductance on the finite path is the reciprocal of its edge length.

**Definition 1.7 (Symmetric stiffness coupling).**

Lean statement: `D5/S3/Quantum/Jacobi/NeumannHeatGramianJet.bond`

*Formalization.* `D5/S3/Quantum/Jacobi/NeumannHeatGramianJet.bond` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The coupling is the negative edge conductance divided by the geometric mean of the adjacent vertex masses.

**Definition 1.8 (Physical endpoint moment).**

Lean statement: `D5/S3/Quantum/Jacobi/NeumannHeatGramianJet.moment`

*Formalization.* `D5/S3/Quantum/Jacobi/NeumannHeatGramianJet.moment` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Apply the finite mass-normalized stiffness repeatedly to the endpoint unit vector. Divide the resulting endpoint coordinate by the endpoint mass for the collocated physical heat port.

**Definition 1.9 (Formal heat response).**

Lean statement: `D5/S3/Quantum/Jacobi/NeumannHeatGramianJet.heat`

*Formalization.* `D5/S3/Quantum/Jacobi/NeumannHeatGramianJet.heat` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The degree-r coefficient is the physical moment of order r times the alternating sign divided by r factorial. An arbitrary constant offset is added to the response.

**Theorem 1.10 (Exact first difference after a common positive prefix).**

Lean statement: `D5/S3/Quantum/Jacobi/NeumannHeatGramianJet.first_reveal`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Jacobi/NeumannHeatGramianJet.first_reveal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Consider two paths p and q with n positive edges. Let k be positive and smaller than n. Assume the paths share all edges with index below k and have unequal lengths at index k. Their Gramian difference has zero coefficients below degree 2k+2, for any pair of constant heat offsets.

At degree 2k+2 the coefficient is the product of the negative first moment of p, the order 2k, and the order-2k moment difference p minus q, divided by the factorial of 2k+2. This coefficient is nonzero.

The paths have the same Jacobi compression onto the first k vertices. The first return outside this compression contributes the product of squared couplings. Only the last factor varies with edge k, through the reciprocal of the mass at vertex k. In the derivative of the Gramian, the first changed centered coefficient pairs with the shared linear coefficient. Formal integration raises the degree by one.

## References

- Truth anchor: `D5/S3/Quantum/Jacobi/NeumannHeatGramianJet.Path`
- Truth anchor: `D5/S3/Quantum/Jacobi/NeumannHeatGramianJet.bond`
- Truth anchor: `D5/S3/Quantum/Jacobi/NeumannHeatGramianJet.diagonal`
- Truth anchor: `D5/S3/Quantum/Jacobi/NeumannHeatGramianJet.edge`
- Truth anchor: `D5/S3/Quantum/Jacobi/NeumannHeatGramianJet.first_reveal`
- Truth anchor: `D5/S3/Quantum/Jacobi/NeumannHeatGramianJet.gramian`
- Truth anchor: `D5/S3/Quantum/Jacobi/NeumannHeatGramianJet.heat`
- Truth anchor: `D5/S3/Quantum/Jacobi/NeumannHeatGramianJet.mass`
- Truth anchor: `D5/S3/Quantum/Jacobi/NeumannHeatGramianJet.moment`
- Truth anchor: `D5/S3/Quantum/Jacobi/NeumannHeatGramianJet.timeAverage`
- Dependency: [D5/S3/Quantum/Jacobi/EndpointMomentTruncation](EndpointMomentTruncation.md)
