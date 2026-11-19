# Normalized physical repairs

## Abstract

Normalize retained isometry columns to compare the actual physical output with pointer outputs. Conditional density blocks and orthogonal pointer entropies give a classical Markov repair even at zero weights. A common normalized environment vector instead gives an AB-C product repair.

**Theorem 1.1 (A product across AB and C).**

Lean statement: `D5/S3/Quantum/Recovery/QubitPhysicalRepair.qcmi_product_right`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/QubitPhysicalRepair.qcmi_product_right` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every density state P on A times B and every density state gamma on C, relabeling P tensor gamma onto A times (B times C) gives ordinary conditional mutual information zero.

**Definition 1.2 (An orthogonal pointer state).**

Lean statement: `D5/S3/Quantum/Recovery/QubitPhysicalRepair.classicalMarkovState`

*Formalization.* `D5/S3/Quantum/Recovery/QubitPhysicalRepair.classicalMarkovState` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A probability vector on B and normalized conditional states alpha(j) on A and gamma(j) on C define the mixture of alpha(j) tensor the computational pointer j tensor gamma(j). Zero weights do not require division.

**Theorem 1.3 (Conditional independence in every pointer block).**

Lean statement: `D5/S3/Quantum/Recovery/QubitPhysicalRepair.qcmi_classicalMarkovState`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/QubitPhysicalRepair.qcmi_classicalMarkovState` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The orthogonal pointer mixture has ordinary conditional mutual information zero. Each of its four actual marginal entropies is evaluated using product additivity and the orthogonal record entropy formula; the classical entropy and both conditional entropy sums cancel.

**Theorem 1.4 (Operator norm of an isometry).**

Lean statement: `D5/S3/Quantum/Recovery/QubitPhysicalRepair.isometry_operatorNorm_le`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/QubitPhysicalRepair.isometry_operatorNorm_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every finite matrix with orthonormal columns has operator norm at most one, including empty coordinate types.

**Definition 1.5 (A normalized retained-column pointer map).**

Lean statement: `D5/S3/Quantum/Recovery/QubitPhysicalRepair.pointerIsometry`

*Formalization.* `D5/S3/Quantum/Recovery/QubitPhysicalRepair.pointerIsometry` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Two environment vectors define a qubit map whose j-th column has support only on output pointer j. Unit norms make this map an isometry.

**Theorem 1.6 (Normalize retained columns below unit flip probability).**

Lean statement: `D5/S3/Quantum/Recovery/QubitPhysicalRepair.normalized_pointer_isometry`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/QubitPhysicalRepair.normalized_pointer_isometry` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If the sum s squared of the two flip probabilities is below one, both retained columns of the actual isometry have positive norm. Normalize them and delete the flips to obtain a pointer isometry within operator norm 2s. No input block weight is inverted.

**Theorem 1.7 (A common environment comparison).**

Lean statement: `D5/S3/Quantum/Recovery/QubitPhysicalRepair.physicalOutput_distance`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/QubitPhysicalRepair.physicalOutput_distance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Two physical isometries applied to the same AB density state, followed by discarding their common environment, differ in half trace distance by at most the operator norm of the difference of the isometries. This comparison has no reference-dimension factor.

**Theorem 1.8 (The cost of deleting qubit coherence).**

Lean statement: `D5/S3/Quantum/Recovery/QubitPhysicalRepair.pointerInput_distance`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/QubitPhysicalRepair.pointerInput_distance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Pinching an actual AB density state in the two-dimensional B basis changes it in half trace distance by at most the trace norm of its complex off-diagonal A block. The two conjugate off-diagonal terms and the half-distance convention account for the factor.

**Theorem 1.9 (A classical repair on the same physical system).**

Lean statement: `D5/S3/Quantum/Recovery/QubitPhysicalRepair.classical_pointer_repair`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/QubitPhysicalRepair.classical_pointer_repair` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let W be an actual dilation of T, and let s squared be its total flip probability in the chosen qubit basis. If s squared is below one, normalizing its two retained vectors and pinching the actual AB input produces a classical Markov state on the same ABC carrier. Its half trace distance from rho is at most r plus the trace norm z of the actual off-diagonal AB block plus 2s. A positive block weight normalizes its conditional A state; a zero block has zero positive matrix and needs no division.

**Theorem 1.10 (A common environment gives an AB-C product).**

Lean statement: `D5/S3/Quantum/Recovery/QubitPhysicalRepair.common_environment_product_repair`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/QubitPhysicalRepair.common_environment_product_repair` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let g be the modulus of one minus the inner product of the two retained Stinespring vectors. If the total flip probability s squared is below one, normalize the first retained vector and use it for both pointer columns. This is a physical product across AB and C, with ordinary qcmi zero and half trace distance from rho at most r plus 2s plus the square root of 2g. The comparison retains every rank and the same ABC system.

## References

- Truth anchor: `D5/S3/Quantum/Recovery/QubitPhysicalRepair.classicalMarkovState`
- Truth anchor: `D5/S3/Quantum/Recovery/QubitPhysicalRepair.classical_pointer_repair`
- Truth anchor: `D5/S3/Quantum/Recovery/QubitPhysicalRepair.common_environment_product_repair`
- Truth anchor: `D5/S3/Quantum/Recovery/QubitPhysicalRepair.isometry_operatorNorm_le`
- Truth anchor: `D5/S3/Quantum/Recovery/QubitPhysicalRepair.normalized_pointer_isometry`
- Truth anchor: `D5/S3/Quantum/Recovery/QubitPhysicalRepair.physicalOutput_distance`
- Truth anchor: `D5/S3/Quantum/Recovery/QubitPhysicalRepair.pointerInput_distance`
- Truth anchor: `D5/S3/Quantum/Recovery/QubitPhysicalRepair.pointerIsometry`
- Truth anchor: `D5/S3/Quantum/Recovery/QubitPhysicalRepair.qcmi_classicalMarkovState`
- Truth anchor: `D5/S3/Quantum/Recovery/QubitPhysicalRepair.qcmi_product_right`
- Dependency: [D5/S3/Quantum/Recovery/QubitActualResidualGeometry](QubitActualResidualGeometry.md)
