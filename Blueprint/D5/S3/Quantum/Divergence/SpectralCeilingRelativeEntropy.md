# Spectral ceilings and the strong Klein remainder

## Abstract

A common spectral ceiling controls the actual trace-log remainder in Hilbert--Schmidt distance.

**Theorem 1.1 (Complete spectra, including every kernel mode).**

Lean statement: `D5/S3/Quantum/Divergence/SpectralCeilingRelativeEntropy.actual_matrix_spectral_ceiling_strong_klein`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/SpectralCeilingRelativeEntropy.actual_matrix_spectral_ceiling_strong_klein` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let A and B be positive semidefinite complex matrices on any finite index type, with ker B contained in ker A. If M>0 and both A and B are at most M I in Loewner order, then Tr((A-B)* (A-B)).re/(2M) is at most Tr(A(log A-log B)).re-Tr(A).re+Tr(B).re. The star in the quadratic expression denotes the adjoint. Equal traces cancel the final correction. In particular, for actual density states with support inclusion this is the finite trace-log relative entropy bound. The norm quantity is the explicit Hilbert--Schmidt square, not the default matrix norm.

The proof retains the complete eigenbases of both matrices. Their squared overlaps form a doubly stochastic matrix by Parseval. The scalar logarithmic tangent remainder has curvature at least 1/M on the spectral interval. If a B eigenvalue is zero, support inclusion kills its overlap against each positive A eigenvector before the scalar estimate is used. Zero A modes remain present and supply their necessary B and B-squared terms. The weighted sums are identified with actual CFC trace products and the adjoint-square trace. No commutation or invertibility assumption is imposed.

The public rank-one trace-product supplier is reused from the existing Lieb-overlap proof. The kernel-overlap argument follows the existing supported relative-modular construction, now shared with that construction as a generic kernel-eigenvector supplier, with the full zero/positive weighted split.

For the actual original application, take P a density state, U=XX, B=UPU*, w=(1+a)/2, R=wP+(1-w)B, and T=(P-B)/2. Here 0<=a<=1 and P<=M I. Unitary conjugation gives B<=M I and equal endpoint entropies; convexity of the Loewner interval gives R<=M I. If a<1, positivity of both weights gives supp P and supp B contained in supp R. Apply the general comparison to (P,R) and (B,R), with weights w and 1-w. Their trace corrections cancel, and their weighted trace-log divergences equal g=S(R)-S(P). Since P-R=(1-a)T, B-R=-(1+a)T, and w(1-a)^2+(1-w)(1+a)^2=1-a^2, the result is g>=(1-a^2) Tr(T* T).re/(2M). At a=1, R=P and both sides vanish. The argument applies to arbitrary complex density matrices P and unitary U, including singular P and a=0.

For the original deficit, this estimate supplies its global entropy gain while the full endpoint mutual informations I(P) and I(Q) remain in the budget. Completing the spectral-region argument additionally requires the actual marginal-entropy comparison and its spectral-to-marginal bound. This theorem alone does not establish the unrestricted two-qubit deficit, physical sharpness, or literature novelty.

## References

- Truth anchor: `D5/S3/Quantum/Divergence/SpectralCeilingRelativeEntropy.actual_matrix_spectral_ceiling_strong_klein`
- Dependency: [D5/S3/Quantum/Divergence/LiebOverlapResolventIntegralBudget](LiebOverlapResolventIntegralBudget.md)
- Dependency: [D5/S3/Resource/LogDet/PathSpectralClassical](../../Resource/LogDet/PathSpectralClassical.md)
