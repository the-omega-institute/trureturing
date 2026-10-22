# The Original Leech Quadratic Space

## Abstract

The original Leech quadratic refinement has a literal hyperbolic basis.

**Theorem 1.1 (The Original Leech Quadratic Space).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/LeechQuadratic.frame_independent`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/LeechQuadratic.frame_independent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let D be the literal ExplicitLeechLattice.data, with gramMatrix in its original lattice-charge coordinates. The form q(v) is the diagonal of the original modTwoCocycle, not a function on ambient Euclidean coordinates. For every integral charge a, q(reduceCharge(a)) is the reduction of bilinear(D,a,a)/2. Its polar form is the original modTwoPairing.

The literalIntegralVectors have the order p0,...,p11,f0,...,f11. Their twenty-four singular values and all 576 polar pairings give q(p_i)=q(f_i)=0, B(p_i,p_j)=B(f_i,f_j)=0 and B(p_i,f_j)=delta_ij. The integer matrix of their Gram rows is kernel-checked against literalIntegralVectors times the original gramMatrix; it only factors the same exact arithmetic. Evaluation against partners isolates each coefficient of a linear dependence. Equality of dimension and index cardinality gives an actual basis, without enumerating the 2^24 charges. This is plus type on the original quadratic space.

The literal frame vectors are taken from the completed mod-two hyperbolic-frame design. The general reduction and half-norm identities reuse LatticeTwistedGroundRealization.cocycle_reduction and integral_cocycle_square. The Gram data and lattice construction remain those of ExplicitLeechBasis and ExplicitLeechLattice.

The new linear-independence argument is frame_independent, consumed by hyperbolicBasis. The original_plus_type theorem packages the existing literal certificate and integral identity; it is a consumed bind-only helper, not additional mathematical novelty. NativeHyperbolicActions.correction_diagonal consumes its singularity statement on the original charge space.

The standalone literalGramRows_eq and literal_certificate are positive fixed finite certified instances, not generic checker soundness theorems. Their mathematical validity and downstream use do not establish their retention admissibility under the computational-content rule: neither supplies a verified refutation, and utility:none does not describe their actual shape. The structural independence proof does not remove that prerequisite retention gap. The exact literal vectors, original Gram matrix and certificate proofs remain unchanged.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/LeechQuadratic.frame_independent`
- Dependency: [D5/S3/VertexAlgebra/GolayLeech/ExplicitLeechLattice](../GolayLeech/ExplicitLeechLattice.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/LeechHyperbolicCertificate](LeechHyperbolicCertificate.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/LeechQuadraticReduction](LeechQuadraticReduction.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/OperatorAlgebra](OperatorAlgebra.md)
