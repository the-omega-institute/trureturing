# Complex Hadamard Cocycle Gauge

## Abstract

Coherent unitary vertex gauges preserve scaled relative-Gram cocycles.

**Theorem 1.1 (Right vertex gauge action).**

Lean statement: `D5/S3/Quantum/Tomography/MUB/ComplexHadamardCocycleGauge.relativeGram_right_vertexGauge`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/MUB/ComplexHadamardCocycleGauge.relativeGram_right_vertexGauge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For two families H and M of complex square matrices on a finite coordinate type, the relative Gram of H(a) M(a) and H(b) M(b) equals the relative Gram of H(a) and H(b), multiplied on the left by the adjoint of M(a) and on the right by M(b).

**Theorem 1.2 (Scaled cocycle covariance).**

Lean statement: `D5/S3/Quantum/Tomography/MUB/ComplexHadamardCocycleGauge.scaledCocycle_vertexGauge`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/MUB/ComplexHadamardCocycleGauge.scaledCocycle_vertexGauge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Suppose G(a,b) G(b,c) equals scale times G(a,c) for every vertex triple, and each M(b) times its adjoint is the identity. Replacing every G(a,b) by M(a)-adjoint times G(a,b) times M(b) preserves the same scaled cocycle equation.

**Theorem 1.3 (Relative Gram cocycle after gauging).**

Lean statement: `D5/S3/Quantum/Tomography/MUB/ComplexHadamardCocycleGauge.relativeGram_cocycle_after_vertexGauge`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/MUB/ComplexHadamardCocycleGauge.relativeGram_cocycle_after_vertexGauge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a family of complex Hadamard matrices H and vertex matrices M satisfying M(b) times its adjoint equals the identity, the relative Grams of H(b) M(b) satisfy the cocycle equation with scale equal to the finite coordinate cardinality.

## References

- Truth anchor: `D5/S3/Quantum/Tomography/MUB/ComplexHadamardCocycleGauge.relativeGram_cocycle_after_vertexGauge`
- Truth anchor: `D5/S3/Quantum/Tomography/MUB/ComplexHadamardCocycleGauge.relativeGram_right_vertexGauge`
- Truth anchor: `D5/S3/Quantum/Tomography/MUB/ComplexHadamardCocycleGauge.scaledCocycle_vertexGauge`
- Dependency: [D5/S3/Quantum/Tomography/MUB/ComplexHadamardRelativeGramCocycle](ComplexHadamardRelativeGramCocycle.md)
