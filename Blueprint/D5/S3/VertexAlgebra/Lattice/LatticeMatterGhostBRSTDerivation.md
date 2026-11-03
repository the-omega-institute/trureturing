# The original total charge on all homogeneous coupled fields

## Abstract

Original coupled BRST field superderivation

This owning Scribe accompanies the original all-state total-charge field superderivation, reconciled and natively compiled against released coupled source 9443abecae3e805d68a61bbcbb529117aa4c7d9a. Native compilation does not assert semantic audit validation, independent review, freeze, CI, official acceptance or physical realization.

Let D be an arbitrary original LatticeData, including rank zero, and H an arbitrary complex matrix indexed by Fin D.rank on both sides. State D is literally the original matter Carrier D tensored algebraically with the original countable occupation bc Fock space. Y, the vacuum, translation and ghost parity are precisely LatticeMatterGhostStateField's pointwise finite convolution and original tensor operators. Q is LatticeBRST.totalCharge D H, with no replacement differential or intercept. The imported current is literally omega(D,H) tensor ket{1} plus the matter vacuum tensor the raw original cubic state Jg.

**Theorem 1.1 (All states of fixed ghost parity and every integer mode).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeMatterGhostBRSTDerivation.totalCharge_field_superderivation`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeMatterGhostBRSTDerivation.totalCharge_field_superderivation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every original state s, natural p with P(s)=(-1)^p s, and integer n, the theorem proves the equality of endomorphisms Q Y(s)[n] - (-1)^p Y(s)[n] Q = Y(Qs)[n]. Consequently it acts on every original input state, including inhomogeneous finite sums. When p is odd the left side is an anticommutator. There is no inverse-Gram, positive-rank, rank-26, positivity, full signed Borcherds/Jacobi or global Q-squared-zero premise.

The actual ghost parity suppliers prove that the literal current is odd. Its proven zero mode is Q; original creation gives Q vacuum=0, and original covariance at mode zero gives [T,Q]=0. Original field parity then puts Qs in parity p+1. These facts are derived in the live proof, rather than included as hypotheses.

The narrow missing bridge is signed zero-residue locality. For fields A,B,C and their three signs e,f,g, direct operator expansion expresses [[A,B]_e,C]_(fg) as g[A,C]_f B - e B[A,C]_f + A[B,C]_g - ef[B,C]_g A. The coefficient shifts X=(x-y), Z=(y-z) commute. Pairwise locality kills X^N of this discrepancy and (X+Z)^M Z^L of it. A finite binomial expansion kills Z^(M+N+L), uniformly in every input vector. Extracting the A-mode zero therefore gives locality of [A_0,B]_e against C with sign fg.

The zero-residue field is lower truncated on each x by the two actual tail bounds for B(x) and B(A_0 x). This stage introduces no infinite residue sums, no interchange of sums and no globally finite endomorphism support. The original tensor convolution's pointwise support remains an imported obligation of the hash-bound closed supplier.

Subtract Y(Qs) from the zero-residue field. The discrepancy has covariance, zero nonnegative vacuum coefficients and zero minus-one vacuum coefficient. Translation recursively kills all remaining vacuum coefficients, dividing only by nonzero natural successors in Complex. For each homogeneous x, locality at second mode -1 isolates every discrepancy mode on x. The original parity involution gives x=(x+Px)/2+(x-Px)/2, so these actions vanish on every original input state. Creative uniqueness identifies the actual fields and supplies the exact equation.

All private helpers are consumed by this proof. The only public declaration is the original-charge result; finite-shift organization and direct supplier applications receive no independent content credit. The unsigned reconstruction theorem is a fallible proof pattern, not a signed theorem invocation. Only its sign-free deltaEnd power/iterate identity is applied. Classical locality and creative reconstruction are attributed to the existing Dong/Matsuo--Nagatomo proof lineage and the Scott Carnahan Apache-2.0 supplier. No new literature result or independent physical realization is claimed.

The mirrored Reg source retains the full original telescope, a typed source-equivalence bridge, whole-family variation, role sensitivity and actual observational dependence. Its actual scoped binding verdict is declared_unresolved: IE-C050, source.residual_requires_open, tracked at https://github.com/the-omega-institute/trureturing/issues/26094. The compiled family proofs do not establish semantic audit validation. Independent review, required CI, freeze and official delivery remain later integration obligations; no judge or configuration change is part of this mathematics.

Critical-rank quotient application. Let H be a two-sided inverse of the original complex Gram matrix and let D.rank=26. The existing total_square_anomaly formula then gives Q squared equal to zero; square zero is derived rather than assumed. Set Z=ker Q and take B to be the image of Q on the entire original State D, viewed inside Z. This is the full algebraic BRST quotient Z/B, with no relative or zero-energy restriction. The original parity involution P and odd current give QP=-PQ. Decomposing an arbitrary field state as (s+Ps)/2+(s-Ps)/2 extends the displayed homogeneous theorem to Q(Y(s)[n]x)=Y(Qs)[n]x+Y(Ps)[n](Qx), for every integer n.

For s,x in Z, this identity proves Y(s)[n]x is in Z. Replacing s by s+Qa changes the result by Q(Y(a)[n]x). Replacing x by x+Qb changes it by Q(Y(Ps)[n]b), since Q(Ps)=0 and P squared is the identity. Thus both slots descend, including mixed-parity representatives and every boundary in the full image of Q. The bilinear quotient lift and the original pointwise lower truncation construct a complex-linear map from Z/B to VertexOperator over Z/B, whose modes satisfy Ybar([s])[n][x]=[Y(s)[n]x]. This is an application of the existing original-field derivation and square formula, not an additional independent mathematical declaration or literature novelty. It neither supplies a Jacobi identity nor computes the quotient or a nonzero class.

This algebraic derivation and its quotient application advance the same Monster, VOA/CFT, anomaly, fusion, string and AdS/CFT programme without completing it. It establishes no full coupled three-index Borcherds identity, BRST cohomology computation, nonzero class, no-ghost theorem, positivity or analytic/unitary CFT, physical string realization, fusion construction, Monster identification or AdS/CFT correspondence. Those remain substantive scientific tasks.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeMatterGhostBRSTDerivation.totalCharge_field_superderivation`
- Dependency: [D5/S3/VertexAlgebra/Lattice/LatticeMatterGhostStateField](LatticeMatterGhostStateField.md)
- Dependency: [D5/S3/VertexAlgebra/StateFieldResidueReconstruction](../StateFieldResidueReconstruction.md)
