# Mixture bounds

## Abstract

Exponential overlap rates of uniform finite mixtures.

**Theorem 1.1 (Largest component overlap controls a uniform mixture).**

Lean statement: `D5/S3/Quantum/Information/GroupInvariantPsi/Sandwich.sandwich`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/GroupInvariantPsi/Sandwich.sandwich` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let a finite group of size k permute a finite alphabet, and let p and q be nonnegative functions on that alphabet. For s strictly between zero and one, let M be the largest relative permutation overlap. The overlap of the uniform mixtures of the n-fold product functions lies between M to the power n divided by k and k times M to the power n. Relative permutation reindexing reduces every component pair to a single-site overlap raised to the power n. The lower bound retains a maximizing pair, and the upper bound uses subadditivity of fractional powers.

**Definition 1.2 (Relative permutation overlap).**

Lean statement: `D5/S3/Quantum/Information/GroupInvariantPsi/Sandwich.componentCoeff`

*Formalization.* `D5/S3/Quantum/Information/GroupInvariantPsi/Sandwich.componentCoeff` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a group action on basis labels, sum p(i) to the power s times q(g i) to the power one minus s over all labels.

**Definition 1.3 (Largest relative overlap).**

Lean statement: `D5/S3/Quantum/Information/GroupInvariantPsi/Sandwich.maxCoeff`

*Formalization.* `D5/S3/Quantum/Information/GroupInvariantPsi/Sandwich.maxCoeff` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Take the maximum of the relative permutation overlaps over the finite group.

**Theorem 1.4 (The asymptotic logarithmic overlap).**

Lean statement: `D5/S3/Quantum/Information/GroupInvariantPsi/Sandwich.psi_eq_max`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/GroupInvariantPsi/Sandwich.psi_eq_max` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For strictly positive p and q on a nonempty finite alphabet, the normalized logarithm of the tensor overlap converges, at each parameter strictly between zero and one, to log M. This is also the value of the selected limit psi. The sandwich bounds leave a correction of absolute size at most log k divided by n. Diagonal spectral calculus and the permutation twirl identity identify this scalar overlap with the original matrix trace expression. Probability normalization is not required for this convergence calculation.

## References

- Truth anchor: `D5/S3/Quantum/Information/GroupInvariantPsi/Sandwich.componentCoeff`
- Truth anchor: `D5/S3/Quantum/Information/GroupInvariantPsi/Sandwich.maxCoeff`
- Truth anchor: `D5/S3/Quantum/Information/GroupInvariantPsi/Sandwich.psi_eq_max`
- Truth anchor: `D5/S3/Quantum/Information/GroupInvariantPsi/Sandwich.sandwich`
- Dependency: [D5/S3/Quantum/Information/GroupInvariantPsi/Mixture](Mixture.md)
