# Finite-mixture top-order obstruction machinery

## Abstract

Finite bias mixtures have uniform scalar leading terms and explicit full pairing-defect limits.

**Definition 1.1 (Scalar moments of a finite mixture).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/TopOrderObstructionCore.scalarMoment`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/TopOrderObstructionCore.scalarMoment` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a finite index set with real values v_z and real weights w_z, define m_j=sum_z w_z v_z^j. No positivity assumption is needed for this definition or for the uniform leading-term estimate. The associated sign model uses N coordinates with conditional mean v_z/sqrt(N).

**Definition 1.2 (Gaussian pairing moments).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/TopOrderObstructionCore.scalarGaussian`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/TopOrderObstructionCore.scalarGaussian` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Define gamma_j(v)=(j-1)!! v^(j/2) for even j, and zero for odd j. The convention at j=0 gives gamma_0(v)=1.

**Definition 1.3 (The scalar pairing defect).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/TopOrderObstructionCore.scalarDefect`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/TopOrderObstructionCore.scalarDefect` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Define d_j=m_j-gamma_j(m_2). This subtracts the perfect-pairing contribution from the scalar j-th moment.

**Definition 1.4 (The number of perfect pairings).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/TopOrderObstructionCore.gaussianPairingCount`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/TopOrderObstructionCore.gaussianPairingCount` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The perfect-pairing count q_j equals (j-1)!! for even j and zero for odd j. In particular q_0=1, so the empty label set is included.

**Definition 1.5 (A uniform error constant).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/TopOrderObstructionCore.mixtureLeadingConstant`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/TopOrderObstructionCore.mixtureLeadingConstant` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For order j define B_j=|m_j| choose(j,2) + q_j floor(j/2) |m_2| max(1,|m_2|)^floor(j/2). The collision comparison and two-label identities are supplied by MixtureMomentLemmas. The first term controls collisions in the distinct-index sum; the second controls the perturbation of the product of pair moments.

**Theorem 1.6 (A uniform leading term for arbitrary bounded coefficients).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/TopOrderObstructionCore.mixture_uniform_leading_bound_all`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/TopOrderObstructionCore.mixture_uniform_leading_bound_all` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let N be positive, let U be a finite label set of cardinality j<=N, and let every coefficient f_i(d) have absolute value at most one. Write a_i=(sum_d f_i(d))/N. The distinct-index moment minus its perfect-pairing polynomial, divided by (sqrt(N))^j, differs from d_j times the product of a_i over U by at most B_j/N. Removing noninjective assignments costs at most choose(j,2) N^(j-1). For each pair the normalized second moment differs from m_2 a_i a_l by at most |m_2|/N. A product perturbation bound and the perfect-pairing count give the second error term. The empty label set satisfies the same estimate exactly. This is the finite-mixture leading-term argument used in Theorem 503.4 of FIBONACCI_ANALYTIC_FRONTIER_INTERFACES_II, with the pairing framework of Lemmas 503.2 and 503.3.

**Theorem 1.7 (The full pairing-defect propagation limit).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/TopOrderObstructionCore.mixture_propagation_limit`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/TopOrderObstructionCore.mixture_propagation_limit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix an order k and a finite real mixture with m_0=1 and m_1=0. Suppose C>=1 bounds |m_r| for 2<=r<k. Then the full unit-coefficient moment minus its full-moment pairing polynomial, divided by (sqrt(N))^k, tends as N grows to sum_(p=0,...,floor(k/2)) choose(k,2p) (2p-1)!! d_(k-2p). A partial pairing with p edges chooses 2p labels and pairs them, giving the displayed multiplicity. Each unit-coefficient edge contributes N. On the remaining j labels the normalized distinct moment is m_j N(N-1)...(N-j+1)/N^j, while the normalized pairing polynomial is gamma_j(m_2) (1-1/N)^floor(j/2). These converge to m_j and gamma_j(m_2). The quadratic transfer remainder is at most a fixed constant times sqrt(1/N)+1/N and tends to zero. This is the propagation mechanism in Theorem 503.4, using Lemmas 503.2 and 503.3 of FIBONACCI_ANALYTIC_FRONTIER_INTERFACES_II. The argument is repo-derived; the odd and even three-point obstructions are treated in TopOrderObstructionFamily.

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/TopOrderObstructionCore.gaussianPairingCount`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/TopOrderObstructionCore.mixtureLeadingConstant`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/TopOrderObstructionCore.mixture_propagation_limit`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/TopOrderObstructionCore.mixture_uniform_leading_bound_all`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/TopOrderObstructionCore.scalarDefect`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/TopOrderObstructionCore.scalarGaussian`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/TopOrderObstructionCore.scalarMoment`
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/MixtureMomentLemmas](MixtureMomentLemmas.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PairingDefectInversion](PairingDefectInversion.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PerfectPairingCount](PerfectPairingCount.md)
