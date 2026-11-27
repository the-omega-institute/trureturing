# The scalar corner inequality for the refined BMV lower bound

## Abstract

The scalar corner inequality for the refined BMV lower bound

**Theorem 1.1 (The centered residual is nonnegative for every exponent).**

Lean statement: `D5/S3/Quantum/Analysis/RefinedBMVUniformCorner.defect_corner`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/RefinedBMVUniformCorner.defect_corner` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Daniel Hägele (2026). *On the lower bound of the refined Bessis–Moussa–Villani conjecture: proof of the cases S6,3 and S7,3 for 3 × 3 matrices*. DOI: [10.48550/arXiv.2611.00129](https://doi.org/10.48550/arXiv.2611.00129). URL: <https://arxiv.org/abs/2611.00129v1>.

*Commentary.*

For three nonnegative cube roots a, x and y and any number of first factors, the mixed defect is at least the geometric mean of the repeated-root defects at (a,a,y) and (x,x,y). The triangular coefficient matrix of the complete homogeneous polynomial has nonpositive two-by-two minors. Cauchy–Binet gives the corresponding reverse Cauchy–Schwarz comparison after compression to the two root vectors. Ordinary Cauchy–Schwarz then transfers the comparison through subtraction of the geometric term.

**Theorem 1.2 (Equality at degree zero or a repeated root).**

Lean statement: `D5/S3/Quantum/Analysis/RefinedBMVUniformCorner.defect_corner_eq_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/RefinedBMVUniformCorner.defect_corner_eq_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Daniel Hägele (2026). *On the lower bound of the refined Bessis–Moussa–Villani conjecture: proof of the cases S6,3 and S7,3 for 3 × 3 matrices*. DOI: [10.48550/arXiv.2611.00129](https://doi.org/10.48550/arXiv.2611.00129). URL: <https://arxiv.org/abs/2611.00129v1>.

*Commentary.*

At positive degree, the minor using the zero and highest degrees gives a strictly negative contribution to the compressed determinant whenever a and x differ. This makes the corner inequality strict, including when a root is zero. Equality holds exactly when the first two roots coincide or the degree is zero.

## References

- Truth anchor: `D5/S3/Quantum/Analysis/RefinedBMVUniformCorner.defect_corner`
- Truth anchor: `D5/S3/Quantum/Analysis/RefinedBMVUniformCorner.defect_corner_eq_iff`
- Dependency: [D5/S3/Quantum/Schatten/CompoundMatrices](../Schatten/CompoundMatrices.md)
