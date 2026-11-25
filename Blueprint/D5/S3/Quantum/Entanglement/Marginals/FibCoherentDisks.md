# The two residual disks for Fibonacci marginals

## Abstract

A closed-form choice of coupling for coherent marginals on three Fibonacci sites.

**Theorem 1.1 (Testing one prescribed coupling).**

Lean statement: `D5/S3/Quantum/Entanglement/Marginals/FibCoherentDisks.extendible_iff_selected`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Marginals/FibCoherentDisks.extendible_iff_selected` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A common positive semidefinite trace-one extension exists exactly when the middle occupation is nonnegative, the two endpoint block traces equal one minus the middle occupation, the coupling row at the prescribed coupling vanishes if the middle occupation is zero, and both Schur residuals at that coupling are positive semidefinite.

At zero middle occupation the prescribed coupling is zero. The correction vanishes, so the residuals are the endpoint blocks. At positive middle occupation, a positive semidefinite residual and the subtracted outer-product marginal are both Hermitian. Their sum forces the corresponding endpoint block to be Hermitian.

After scaling by the middle occupation, either residual has a fixed upper diagonal a, a lower diagonal e minus the squared modulus of z, and upper off-diagonal c minus the conjugate of k times z. For positive a, the determinant inequality completes a square centered at k times c divided by h = a + |k|². For this center p the signed squared radius is (ae − |c|² + h|p|²) / h. For zero a and nonzero k, the only candidate is kc / |k|², and its squared modulus must be at most e. If both a and k vanish, c must vanish and the squared radius is e about the origin. Negative a or a negative squared radius gives an empty set. The left and right blocks exchange the two endpoint couplings.

For disk centers p and q, squared radii r and s, and squared center distance d, select the point on the segment at parameter (d + r - s) / (2d) clipped to the interval from zero to one. At coincident centers the selected point is their common center. The weighted squared-distance identity shows this point belongs to both disks whenever their intersection is nonempty.

**Theorem 1.2 (Rational common extensions).**

Lean statement: `D5/S3/Quantum/Entanglement/Marginals/FibCoherentDisks.rational_coherent_extendible_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Marginals/FibCoherentDisks.rational_coherent_extendible_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Suppose the two endpoint blocks and the three observed couplings have rational real and imaginary parts. A positive trace-one common extension exists exactly when there is one with rational entries whose unobserved coupling is the selected point of the two residual disks.

Normalization gives the middle occupation as one minus the trace of the left endpoint block. In the positive case the disk centers and squared radii use only rational operations on the measured data. The clipped segment parameter preserves rationality, including at tangency. At zero occupation the selected coupling is zero. The rational Schur construction then gives the whole density.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/Marginals/FibCoherentDisks.extendible_iff_selected`
- Truth anchor: `D5/S3/Quantum/Entanglement/Marginals/FibCoherentDisks.rational_coherent_extendible_iff`
- Dependency: [D5/S3/Quantum/Entanglement/Marginals/FibCoherentExtension](FibCoherentExtension.md)
- Dependency: [D5/S3/Quantum/Entanglement/Marginals/FibRationalPureExtension](FibRationalPureExtension.md)
