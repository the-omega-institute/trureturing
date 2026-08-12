# The Log-Determinant Divergence

## Abstract

The log-determinant barrier and divergence satisfy self-vanishing and the proved Bregman identity with its positive trace remainder.

For finite complex matrices, the barrier height of a positive definite matrix is minus the logarithm of the real part of its determinant. The log-det divergence of rho from sigma is the real trace of sigma inverse times rho, minus the logarithm of the real part of that product's determinant, minus the matrix dimension. The source atom cone-v1 definition/11.1 identifies this second quantity as the Bregman divergence of the first.

The Bregman link is proved here, and the sign is essential. Because the barrier is minus a log determinant, its gradient at sigma is minus sigma inverse. Consequently, subtracting the gradient pairing in the Bregman remainder gives a plus sign in front of the trace of sigma inverse times rho minus sigma. The identity holds with this plus sign; the kernel-checked formula rules out the otherwise plausible sign reversal.

Nonnegativity is NOT established in this module. The precise obstacle is that sigma inverse times rho is not Hermitian in general, so an eigenvalue argument must first pass to the congruence sigma to the minus one half times rho times sigma to the minus one half. A route was located but not taken: mathlib supplies the square root through the continuous functional calculus CFC.sqrt, not through a bespoke Matrix.sqrt. Matrix.PosDef.eigenvalues_pos and Matrix.IsHermitian.det_eq_prod_eigenvalues, both in Mathlib/Analysis/Matrix/PosDef.lean rather than the similarly named Mathlib/LinearAlgebra path where a search naturally lands, then give the eigenvalue sum, and Real.log_le_sub_one_of_pos closes it termwise.

These are matrix quantities. No physical or information-theoretic interpretation in terms of states, channels, or distinguishability is asserted.

**Definition 1.1 (Barrier height is minus log determinant).**

$$\operatorname{barrierHeight}(\rho)=-\log (\Re(\operatorname{det}(\rho)))$$

*Formalization.* `D5/S3/Resource/LogDetDivergence.barrierHeight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The barrier height takes the negative real logarithm of the determinant's real part. Positive definiteness is imposed by the theorems that use this total definition, not by the definition itself.

**Definition 1.2 (Log-det divergence is trace minus log determinant minus dimension).**

$$\operatorname{logDetDivergence}(\rho, \sigma)=\Re(\operatorname{tr}(\sigma^{-1} \rho))-\log (\Re(\operatorname{det}(\sigma^{-1} \rho)))-d$$

*Formalization.* `D5/S3/Resource/LogDetDivergence.logDetDivergence` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The divergence is the real part of the trace of sigma inverse times rho, minus the real logarithm of the real part of its determinant, minus the cardinality of the finite matrix index type.

**Theorem 1.3 (Positive definite matrices have zero self-divergence).**

$$\forall n\ [\operatorname{Fintype}(n)] [\operatorname{DecidableEq}(n)], \forall \rho: \operatorname{Matrix}(n, n, \mathbb{C}), \operatorname{PosDef}(\rho) \Rightarrow \operatorname{logDetDivergence}(\rho, \rho)=0$$

*Proof.* Machine-checked in Lean as `D5/S3/Resource/LogDetDivergence.logDetDivergence_self` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A positive definite matrix is invertible, so rho inverse times rho is the identity. Its trace is the dimension, its determinant is one, and the resulting log-det divergence is zero.

**Theorem 1.4 (Log-det divergence is the barrier Bregman remainder).**

$$\begin{gathered}\forall n\ [\operatorname{Fintype}(n)] [\operatorname{DecidableEq}(n)], \forall \rho, \sigma: \operatorname{Matrix}(n, n, \mathbb{C}),\\(\operatorname{PosDef}(\rho) \land \operatorname{PosDef}(\sigma)) \Rightarrow\\\operatorname{logDetDivergence}(\rho, \sigma)=\operatorname{barrierHeight}(\rho)-\operatorname{barrierHeight}(\sigma)+\\\Re(\operatorname{tr}(\sigma^{-1} (\rho-\sigma))).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Resource/LogDetDivergence.barrier_bregman_link` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive definite rho and sigma, determinant multiplicativity and the real logarithm laws identify the log terms, while expanding the trace turns the identity contribution into the dimension. The remainder has a plus sign before the trace term, exactly as dictated by the negative gradient of the barrier.

## References

- Truth anchor: `D5/S3/Resource/LogDetDivergence.barrierHeight`
- Truth anchor: `D5/S3/Resource/LogDetDivergence.barrier_bregman_link`
- Truth anchor: `D5/S3/Resource/LogDetDivergence.logDetDivergence`
- Truth anchor: `D5/S3/Resource/LogDetDivergence.logDetDivergence_self`
