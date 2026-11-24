# The two residual disks for Fibonacci marginals

## Abstract

A closed-form choice of coupling for coherent marginals on three Fibonacci sites.

**Theorem 1.1 (Testing one prescribed coupling).**

Lean statement: `D5/S3/Quantum/Entanglement/Marginals/FibCoherentDisks.extendible_iff_selected`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Marginals/FibCoherentDisks.extendible_iff_selected` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume positive middle occupation. A common positive semidefinite trace-one extension exists exactly when the two endpoint block traces equal one minus the middle occupation and both Schur residuals at the prescribed coupling are positive semidefinite. These residuals and the subtracted outer-product marginals are Hermitian, so positivity of the residuals also forces the endpoint blocks to be Hermitian.

At zero middle occupation the correction vanishes and positivity of the joint state forces the entire coupling row to vanish. For example, both endpoint blocks can be the vacuum projection with a nonzero middle-to-vacuum coupling. The residuals then pass both positivity tests, and the nonzero coupling rules out a common extension.

After scaling by the middle occupation, either residual has a fixed upper diagonal a, a lower diagonal e minus the squared modulus of z, and upper off-diagonal c minus the conjugate of k times z. For positive a, the determinant inequality completes a square centered at k times c divided by h = a + |k|². For this center p the signed squared radius is (ae − |c|² + h|p|²) / h. For zero a and nonzero k, the only candidate is kc / |k|², and its squared modulus must be at most e. If both a and k vanish, c must vanish and the squared radius is e about the origin. Negative a or a negative squared radius gives an empty set. The left and right blocks exchange the two endpoint couplings.

For disk centers p and q, squared radii r and s, and squared center distance d, select the point on the segment at parameter (d + r - s) / (2d) clipped to the interval from zero to one. At coincident centers the selected point is their common center. The weighted squared-distance identity shows this point belongs to both disks whenever their intersection is nonempty.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/Marginals/FibCoherentDisks.extendible_iff_selected`
- Dependency: [D5/S3/Quantum/Entanglement/Marginals/FibCoherentExtension](FibCoherentExtension.md)
