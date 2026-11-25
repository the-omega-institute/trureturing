# The mixed residue of two normalized sources

## Abstract

Two normalized sources have mixed massless residue between minus and plus one half. Both endpoints determine the entire residue.

**Definition 1.1 (Balanced realization).**

Lean statement: `D5/S3/Quantum/TwoSource/MasslessResidue.balanced`

*Formalization.* `D5/S3/Quantum/TwoSource/MasslessResidue.balanced` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This real symmetric matrix has diagonal entries one half and off-diagonal entries r.

**Theorem 1.2 (Attainable mixed residues and rigidity at the endpoints).**

$$-\frac{1}{2} \le r \le \frac{1}{2}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TwoSource/MasslessResidue.sharp_mixed_residue` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

There exists a real two-by-two positive semidefinite matrix Z with mixed entry r and positive semidefinite complement I−Z exactly when |r| ≤ 1/2. Each attainable r is realized by the balanced matrix. At either endpoint every such matrix equals that balanced realization.

Evaluate both quadratic forms on (1,1) and (1,−1). These tests trap the trace between 2|r| and 2−2|r|. When |r|=1/2, the trace is one. Positivity of the determinant then forces each diagonal entry to be one half. Conversely the balanced quadratic form is a nonnegative weighted sum of the squares of the sum and difference of the coordinates. The complement is the balanced matrix with coefficient −r.

## References

- Truth anchor: `D5/S3/Quantum/TwoSource/MasslessResidue.balanced`
- Truth anchor: `D5/S3/Quantum/TwoSource/MasslessResidue.sharp_mixed_residue`
