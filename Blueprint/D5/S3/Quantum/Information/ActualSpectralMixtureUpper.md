# Signed amplitude mixtures

## Abstract

Actual finite density mixtures satisfy the spectral SLD information upper bound.

**Theorem 1.1 (Pointwise extended convexity).**

$$\begin{aligned}&\forall n,J\ \mathrm{finite},\ \rho:J\to\mathbb{R}\to\mathbb{C}^{n\times n},\ g:J\to\mathbb{R}\to\mathbb{R},\ t\in\mathbb{R},\\&(\forall i\in J,\operatorname{DifferentiableAt}(\rho_i,t)\land\operatorname{DifferentiableAt}(g_i,t))\\&\land(\exists \delta_r>0,\forall u\in\mathbb{R},|u-t|<\delta_r\longrightarrow\forall i\in J,\operatorname{PSD}(\rho_i(u))\land\operatorname{tr}(\rho_i(u))=1)\\&\land(\exists \delta_g>0,\forall u\in\mathbb{R},|u-t|<\delta_g\longrightarrow\sum_{i\in J}g_i(u)^2=1)\\&\longrightarrow\quad\mathrm{let}\ M(u)=\sum_{i\in J}g_i(u)^2\cdot\rho_i(u),\\&\exists h_M:\operatorname{PSD}(M(t)),\operatorname{tr}(M(t))=1\land\operatorname{DifferentiableAt}(M,t)\\&\land M'(t)=\sum_{i\in J}(2g_i(t)g_i'(t)\cdot\rho_i(t)+g_i(t)^2\cdot\rho_i'(t))\\&\land Q(M(t),M'(t);h_M)\le\sum_{i\in J}g_i(t)^2Q(\rho_i(t),\rho_i'(t);h_r(i))+4\sum_{i\in J}(g_i'(t))^2\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/ActualSpectralMixtureUpper.actual_spectral_mixture_upper` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* S. Alipour, A. T. Rezakhani (2015). *Quantum Metrology: Extended Convexity of Quantum Fisher Information*. DOI: [10.1103/PhysRevA.91.042104](https://doi.org/10.1103/PhysRevA.91.042104). URL: <https://arxiv.org/abs/1403.8033v2>.

*Commentary.*

Both n and J are arbitrary finite types, with Fintype instances and DecidableEq n; neither is required to be nonempty. Every derivative and DifferentiableAt below is over the real field. The two positive neighborhood radii may differ. PSD means positive semidefinite, tr is the complex matrix trace, and scalar multiplication of matrices is used in the definition and derivative of M. The prime denotes the actual deriv at t. Q(A,B;h) denotes the existing spectralQFI A B h from ActualPureQubitGeometry, with its support-safe zero-denominator convention. Here h_r(i) is the component positivity proof at t extracted from the neighborhood premise. The displayed witness h_M is the mixture positivity proof used by Q.

The conclusion supplies positivity and trace one for M(t), differentiability of M at t, its exact derivative, and the upper bound for the existing support-safe spectralQFI of that actual derivative. Zero amplitudes may have arbitrary derivatives. Singular states, changing ranks, noncommuting components and degenerate finite types remain in the quantified domain.

The proof constructs Hermitian SLDs at the point from two-sided positivity. For the derivative B of a positive matrix curve A, its compression from ker A(t) to ker A(t) vanishes: the quadratic form of B is zero on kernel vectors, and polarization gives every kernel-to-kernel entry zero. This does not assert that B annihilates the kernel; support/kernel coherences may remain, including at rank-changing points. A positive weighted matrix-square estimate compares the mixture SLD with the component SLDs and amplitude derivatives. The trace of each component derivative is zero, which removes the corresponding cross terms. No amplitude is divided by its value.

This repository-derived auxiliary addresses the upper inequality associated with equation 215.17 of CSAQ theorem 215.3. Extended convexity itself is established literature: Alipour and Rezakhani, Quantum Metrology: Extended Convexity of Quantum Fisher Information, equation (4), as recorded in Library/Quantum/alipour2015extended.md. With positive weights g_i squared, the classical Fisher term equals four times the sum of squared amplitude derivatives. The present statement instead explicitly permits signed amplitudes and zero amplitudes with arbitrary derivatives; it does not identify that amplitude term with the pointwise classical Fisher term at a zero weight, or replace the pointwise spectral value by a continuous Bures extension. No literature novelty is claimed. The source's cubic amplitude zeros additionally have zero amplitude derivative; that source-specific condition is not assumed here. This auxiliary supplies no lower measurement bound, common processor construction, exact sharp set, minimum dimension, curvature limit or rank repair, and claims no full theorem 215.3 coverage. Continuously differentiable and analytic source curves imply the pointwise differentiability premises; their source-specific amplitude normalization and common-space construction remain separate obligations.

## References

- Truth anchor: `D5/S3/Quantum/Information/ActualSpectralMixtureUpper.actual_spectral_mixture_upper`
- Dependency: [D5/S3/Quantum/Information/ActualPureQubitGeometry](ActualPureQubitGeometry.md)
- Dependency: [D5/S3/Quantum/Information/SLDSpectralEnergy](SLDSpectralEnergy.md)
