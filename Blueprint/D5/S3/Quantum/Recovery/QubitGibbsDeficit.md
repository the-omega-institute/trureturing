# Exact reducing-qubit Gibbs deficit

## Abstract

For a reducing retained qubit the full Gibbs deficit splits into entropy loss and block gaps.

**Theorem 1.1 (Deficit at an arbitrary joint density).**

Lean statement: `D5/S3/Quantum/Recovery/QubitGibbsDeficit.reducing_qubit_gibbs_deficit`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/QubitGibbsDeficit.reducing_qubit_gibbs_deficit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let E be a nonempty finite environment. In the reducing basis of the retained qubit, the field is block diagonal with two arbitrary Hermitian blocks B_i. Write g_i = log Tr exp(B_i), gamma_i = exp(B_i) / Tr exp(B_i), and m = max(g_0,g_1). The joint comparison density tau is block diagonal with blocks gamma_i / 2. The actual partial trace Phi over E sends tau to I/2, and both reference densities are faithful.

For every joint density rho let P = Phi(rho), let p_i be the diagonal entries of P, and let V(rho) be S(rho) - S(P) plus Re Tr(rho diag(B_0,B_1)). Then m - V(rho) = D(rho || tau) - D(P || Phi(tau)) + sum_i p_i (m - g_i). The trace-log expressions are the finite branches of Umegaki relative entropy because both support inclusions hold. The trial density can be singular and may have off-diagonal retained blocks.

Block functional calculus gives the i-th log(tau) block as B_i - (g_i + log 2) I. Expanding the two relative entropies cancels the scalar log(2) shifts. The trace pairing with the remaining scalar blocks reads the actual populations p_i, whose sum is one.

**Theorem 1.2 (Pure marginals and all maximizing densities).**

Lean statement: `D5/S3/Quantum/Recovery/QubitGibbsDeficit.reducing_qubit_gibbs_argmax`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/QubitGibbsDeficit.reducing_qubit_gibbs_argmax` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The maximum of V over all joint densities is m. Each winning label i achieves m at the density supported on that retained basis vector with environment density gamma_i. Its retained marginal is the rank-one diagonal matrix unit.

For an arbitrary rho, equality V(rho) = m requires every positive p_i to have g_i = m. It also requires rho to be either the block mixture with blocks p_i gamma_i, or the product P tensor gamma_0 when gamma_0 = gamma_1. These conditions together suffice. In particular, at a tie with distinct Gibbs densities the optimizer set is the segment between the two pure-marginal states.

Data processing gives nonnegative conditional loss for the two faithful references. At zero loss the fixed ordinary Petz map of the partial trace recovers rho. Its (i,j) block is P_ij sqrt(gamma_i) sqrt(gamma_j). Taking the partial trace forces either zero off-diagonal marginal or unit trace overlap of the two roots. That overlap forces equal roots by the squared Hilbert-Schmidt norm of their difference. The explicit recovery formula also verifies the converse in both cases.

**Theorem 1.3 (Supporting line for the ordinary Petz objective).**

Lean statement: `D5/S3/Quantum/Recovery/QubitGibbsDeficit.ordinary_petz_reducing_supporting_line`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/QubitGibbsDeficit.ordinary_petz_reducing_supporting_line` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let Q be the environmental partial trace of sigma and let R be the ordinary Petz recovery for this partial trace. For the test observable Y, write z(rho) = Re Tr((rho - R(Phi(rho)))Y) and let Delta(rho) be the conditional loss relative to sigma. On faithful references these are the physical recovery score and Umegaki loss. Cyclicity and partial-trace adjunction identify the score with the expectation of Z = Y - Phi*(R*(Y)).

At a parameter r where log(sigma) - Phi*(log Q) + r Z is block diagonal in the given retained basis, the Gibbs theorem computes the full maximum m of F_r = r z - Delta. A physical optimizer with pure retained marginal attains the largest score on that face. For the diagonal mixture, the score is an average over the winning endpoints. In the common Gibbs density case with tied values, a pure marginal maximizes the product score by compactness and the spectral decomposition of every retained density.

The same trial gives F_s = m + (s - r) z at every s. Whenever that trial satisfies z squared at most C Delta for C > 0, its line is at most C s squared / 4. This supplies the bound on the extremal active line at a reducing field for the integrated-curvature argument.

## References

- Truth anchor: `D5/S3/Quantum/Recovery/QubitGibbsDeficit.ordinary_petz_reducing_supporting_line`
- Truth anchor: `D5/S3/Quantum/Recovery/QubitGibbsDeficit.reducing_qubit_gibbs_argmax`
- Truth anchor: `D5/S3/Quantum/Recovery/QubitGibbsDeficit.reducing_qubit_gibbs_deficit`
- Dependency: [D5/S3/Quantum/Divergence/FannesRootFidelityHolevo](../Divergence/FannesRootFidelityHolevo.md)
- Dependency: [D5/S3/Quantum/Divergence/GibbsVariationalIdentity](../Divergence/GibbsVariationalIdentity.md)
- Dependency: [D5/S3/Quantum/Divergence/LegacyRelativeEntropyBoundary](../Divergence/LegacyRelativeEntropyBoundary.md)
- Dependency: [D5/S3/Quantum/Matrix/CartesianVariance](../Matrix/CartesianVariance.md)
- Dependency: [D5/S3/Quantum/Measurement/OccupationPartialTransposeSpectral](../Measurement/OccupationPartialTransposeSpectral.md)
- Dependency: [D5/S3/Quantum/Recovery/BKMFlagRefinement](BKMFlagRefinement.md)
- Dependency: [D5/S3/Quantum/Recovery/CanonicalPetzEquality](CanonicalPetzEquality.md)
