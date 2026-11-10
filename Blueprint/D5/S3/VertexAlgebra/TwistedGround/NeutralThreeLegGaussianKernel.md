# Native normalized neutral three-leg Gaussian kernel

## Abstract

Native normalized neutral three-leg Gaussian kernel

The one-particle carrier is the complex lp space with exponent 2 on Fin N times (Fin 3 times Nat). The three leg labels are source, input and output. Source mode n denotes frequency s=n+1; input and output mode k denote twisted frequency mu=k+1/2. Rank zero gives the empty index set. Equal colors have four nonzero scalar blocks; unequal colors, II and OO vanish. Opposite blocks are holomorphic transposes, with no complex conjugation.

For nonzero complex T and positive alpha,beta,gamma, the SS block is alpha^(s+t) pairScalar(s,t) T^(-2s-2t)/(sqrt(s)sqrt(t)). The SI block is alpha^s sqrt(beta) beta^k sqrt(mu/s) jetScalar(s-1,k) T^(-2k-2s-1). The SO block replaces beta by gamma, uses jetScalar(s-1,-k-1), and has T^(2k-2s+1). The diagonal IO block is sqrt(beta gamma)(beta gamma)^k. Thus the fractional positive attenuation power is expressed by sqrt(beta) beta^k, while every power of T is an integer doubled Hahn power. These are definitions using the original native pairScalar and jetScalar; arbitrary Hahn series are not evaluated.

Put eta=1/(16(N+1)) and r=norm(T)^2. The region is 0<alpha<min(1,eta r), 0<beta<min(1,eta r), 0<gamma<min(1,eta/r). It is nonempty for each nonzero T: take alpha=beta=eta min(1,r)/2 and gamma=eta min(1,1/r)/2. The factored complex ratios alpha/T^2, beta/T^2 and gamma T^2 have norms at most eta. The squared norms of sqrt(beta)/T and sqrt(gamma)T are respectively the norms of the input and output ratios.

The literal jet product has factors -m-3/2-j and denominator n!. For m=k or m=-k-1, the norm of each factor is at most k+2+j. The product of these majorants is n! choose(k+n+1,n), so the jet norm is at most this binomial coefficient and hence 2^(k+n+1), including the empty product. In the normalized squared jet entry, mu/(n+1) is at most k+1, which is at most 2^k. Consequently each mixed source block has squared entry at most 4 eta^3 (1/2)^n (1/2)^k. The estimate follows from 4 rho^2<=1/2 and 8 z^2<=1/2 for the relevant ratio norms rho,z<=eta.

The existing centralWeight norm formula and centralWeight<=1 give the SS factor 1/2 by 2 sqrt(s)sqrt(t)<=s+t. Its squared-entry majorant is eta^4 (1/2)^n (1/2)^m/4. The IO diagonal is bounded by eta^2 (1/2)^k (1/2)^l. Each geometric mode sum is 2. Summing the nine leg blocks and the exact color Kronecker delta gives N(eta^4+64 eta^3+8 eta^2), including both orientations of each mixed block. This is at most M=13 N eta^2<1/4. All sums range over the infinite carriers.

Every literal matrix column therefore belongs to lp with exponent 2, and their squared norms form a summable family. The standard coordinate Hilbert basis is identified with its range as a set in this same space. The native same-space ColumnSynthesis theorem then constructs a bounded complex-linear Hilbert-Schmidt operator with exactly these columns. Its norm is at most sqrt(M)<1/2. This is a contraction of the one-particle kernel.

The finite correctedField coefficient identity, coherent exponential, Gram congruence and coordinate change, both domain conjugations, ground tensor identity and full Fock realization remain separate proof obligations. In an indefinite real Gram case, a complex congruence would choose an auxiliary positive Hermitian completion; it would not establish physical unitarity. Oscillator Hilbert-Schmidt control does not imply Hilbert-Schmidt control after tensoring an infinite ground identity. A coefficient operator with vacuum entry 1 cannot have norm strictly below 1.

**Theorem 1.1 (Literal all-order jet estimate).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/NeutralThreeLegGaussianKernel.jet_binomial_bound`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/NeutralThreeLegGaussianKernel.jet_binomial_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all orders n, all modes k>=0 and either native sign m=k or m=-k-1, norm(jetScalar n m)<=choose(k+n+1,n).

**Theorem 1.2 (Nonempty attenuation region).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/NeutralThreeLegGaussianKernel.damping_nonempty`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/NeutralThreeLegGaussianKernel.damping_nonempty` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every N and every nonzero complex T there exists damping data in the specified strict region with evaluation parameter exactly T.

**Theorem 1.3 (Actual all-frequency matrix square mass).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/NeutralThreeLegGaussianKernel.matrix_square_mass`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/NeutralThreeLegGaussianKernel.matrix_square_mass` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The squared absolute entries of the actual colored three-leg kernel are summable and their full matrix sum is at most 13 N eta^2.

**Theorem 1.4 (Native symmetric one-particle contraction).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/NeutralThreeLegGaussianKernel.operator_realization`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/NeutralThreeLegGaussianKernel.operator_realization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The constructed bounded complex-linear Hilbert-Schmidt operator has the exact native matrix entries, holomorphic transpose symmetry, norm at most sqrt(13 N eta^2) and norm strictly below 1/2.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/NeutralThreeLegGaussianKernel.damping_nonempty`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/NeutralThreeLegGaussianKernel.jet_binomial_bound`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/NeutralThreeLegGaussianKernel.matrix_square_mass`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/NeutralThreeLegGaussianKernel.operator_realization`
- Dependency: [D5/S3/Quantum/Analysis/TraceClass/ColumnSynthesis](../../Quantum/Analysis/TraceClass/ColumnSynthesis.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockFockNormalField](../LatticeHalfFockFockNormalField.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianResolvent](OriginalGaussianResolvent.md)
