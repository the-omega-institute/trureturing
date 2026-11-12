# Whole pure carriers and original ROG frames

## Abstract

The whole normalized pure carrier of a native real or complex ROG PSD section is exactly its unit rank one family, and each such point extends to a full original orthonormal rank one frame.

F is the real or complex field, J is a finite index type with decidable equality, H is the real trace inner product space H of native Hermitian matrices, with pairing Re tr(AB) and the compatible Frobenius norm, and L is a real linear subspace of H. Every vector belongs to the Euclidean space over its original field F. In the real case H is the symmetric matrix space. Complex rank one matrices are not realified. All positive matrices, states and rank one points remain in the same L.

**Definition 1.1 (Native rank one matrices).**

Lean statement: `D5/S3/Quantum/Foundation/SectionROGFrame.rankOne`

*Formalization.* `D5/S3/Quantum/Foundation/SectionROGFrame.rankOne` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every vector v in F to the power J, rankOne(v) is vv*, with star the transpose over the reals and conjugate transpose over the complexes. The zero vector is allowed here. Complex rank one is retained over the complex field.

**Theorem 1.2 (Positivity of the native outer product).**

Lean statement: `D5/S3/Quantum/Foundation/SectionROGFrame.rankOne_nonneg`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/SectionROGFrame.rankOne_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every native vector v, rankOne(v) is PSD. This applies the existing Matrix.posSemidef_vecMulVec_self_star inside the effect and ROG proofs.

**Theorem 1.3 (Trace pairing is the native quadratic reading).**

Lean statement: `D5/S3/Quantum/Foundation/SectionROGFrame.pair_rankOne`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/SectionROGFrame.pair_rankOne` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every A in H and every native vector v, the real number <A,rankOne(v)> embedded into F equals v*Av. The original field is used throughout. This identity is consumed when testing positivity of the global extension and when computing the confirming and zero readings.

**Definition 1.4 (The entire normalized base).**

Lean statement: `D5/S3/Quantum/Foundation/SectionROGFrame.base`

*Formalization.* `D5/S3/Quantum/Foundation/SectionROGFrame.base` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

base(L) is exactly the set of all X in H with X in L, X PSD and tr(X)=1. This is the whole original base embedded by the inclusion of L in H; it is not a chosen set of preparations.

**Definition 1.5 (ROG on every original positive matrix).**

Lean statement: `D5/S3/Quantum/Foundation/SectionROGFrame.ROG`

*Formalization.* `D5/S3/Quantum/Foundation/SectionROGFrame.ROG` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

ROG(L) means that every X in L which is PSD admits a finite list of nonzero native vectors w(j), each w(j)w(j)* in L, whose rank one matrices sum exactly to X. The list is indexed by Fin(m) for some natural m. Zero has an empty decomposition. This is finite generation by original native rank one PSD matrices, with no Jordan closure or supplied frame.

**Definition 1.6 (All normalized native rank one points).**

Lean statement: `D5/S3/Quantum/Foundation/SectionROGFrame.pureRanks`

*Formalization.* `D5/S3/Quantum/Foundation/SectionROGFrame.pureRanks` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

pureRanks(L) consists of every X for which there exists a native Euclidean vector v with norm one, vv*=X and X in L. No proper subconfiguration is selected.

**Theorem 1.7 (Real scaling of native outer products).**

Lean statement: `D5/S3/Quantum/Foundation/SectionROGFrame.rankOne_real_smul`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/SectionROGFrame.rankOne_real_smul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every native vector v and real scalar r, rankOne(r v) equals (r r) rankOne(v). The original declaration is public for the same-Psi rank-one reconstruction consumer in OriginalUnitNormalization; this is an existing algebraic identity.

**Theorem 1.8 (Rank one trace is squared native vector norm).**

$$\forall F \in Type,\; \forall J \in Type,\; [\operatorname{RCLike}\left(F\right)] [\operatorname{Fintype}\left(J\right)] [\operatorname{DecidableEq}\left(J\right)] \forall v \in \operatorname{EuclideanSpace}\left(F, J\right),\; \operatorname{trace}\left(\operatorname{rankOne}\left(v\right)\right) = \Vert v\Vert^{2}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/SectionROGFrame.rankOne_trace_norm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real or complex native field F, finite index type J with decidable equality, and vector v in the native Euclidean space, the real trace of vv* equals the squared norm of v. The vector may be zero. The original declaration supplies the trace estimate for congruence on a projective ROG join.

**Theorem 1.9 (Extreme points equal the entire rank one family).**

Lean statement: `D5/S3/Quantum/Foundation/SectionROGFrame.whole_pure_carrier`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/SectionROGFrame.whole_pure_carrier` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real subspace L satisfying ROG(L), the real extreme points of the entire base(L) equal pureRanks(L). No assumption I in L is needed for this equality. Normalize every nonzero ROG term w(j) by its Euclidean norm and use its squared norm as the positive coefficient. The trace-one equation makes the coefficients sum to one, proving base(L)=convexHull(pureRanks(L)). Conversely a unit rank one p is extreme: the trace pairing <p,X> is at most one for every normalized PSD X, and equality forces X=p by the trace bound <X,X><=tr(X)^2 and the squared norm of X-p. A nontrivial segment decomposition of p therefore has both endpoints equal to p. This equality is consumed in rog_frame to identify every frame point as an original pure state.

**Theorem 1.10 (A full orthonormal frame with the prescribed entry).**

Lean statement: `D5/S3/Quantum/Foundation/SectionROGFrame.rog_frame`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/SectionROGFrame.rog_frame` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every L containing I and satisfying ROG(L), every native Euclidean unit vector v with vv* in L, and every designated index i in J, there exists an orthonormal basis b indexed by J such that b(i)=v, each b(j)b(j)* belongs to L, every such matrix is an extreme point of the whole base(L), and the sum over all j of b(j)b(j)* is I. Taking J=Fin(n) and i=0 gives exactly the frame with first vector v for every n>=1, including n=1 without dividing by n-1. Extend the singleton v to a maximal orthonormal subset whose rank one matrices stay in L. The projector onto its span is a sum of its original rank one matrices, so the residual complementary projector belongs to L. If that residual is nonzero, ROG gives a nonzero original rank one summand below it. Testing on the old span forces the summand vector into its orthogonal complement; normalization yields another allowed unit vector and contradicts maximality. Thus the complement is zero and the family is a full basis. Reindexing places v at the designated coordinate. No Jordan closure premise or chosen frame replaces ROG.

## Whole-section positive lift applications

### The entire original positive cone

cone(L) is the pointed cone on the real subtype L consisting of every X in L whose underlying native matrix is PSD.

### The trace unit

unit(L) is the real linear functional on all of L taking X to its real trace.

### Whole-cone proper effects

For any real linear f from L to the reals, Proper(f) means that 0 <= f(X) <= tr(X) for every X in the entire cone(L), including zero and all unnormalized positive matrices. No ambient positive contraction representative is required.

### All same-unit positive lifts

lifts(L) consists exactly of all M in H such that M is PSD and M-I belongs to the real trace orthogonal complement of L. Thus it is (I+L-perp) intersect PSD.

### Every original positive functional has a PSD lift

For every L containing I and every real linear f:L to R that is nonnegative on every original X in cone(L), there exists E in H with E PSD and f(X)=<E,X> for every X in L. Ambient majorization ranges over every Hermitian Y, not just Y in L: the sum of absolute eigenvalues of -Y gives t>=0 with Y+tI PSD. Riesz positive extension applies to the original partial functional. Finite dimensional continuity and the existing trace inner product give E; testing every ambient vv*, including those outside L, proves E PSD.

### Deflation below the same positive matrix

For every PSD M and every native vector v satisfying v*Mv=1, E=Mvv*M is PSD and M-E is PSD. No invertibility or unit length of v is assumed in this theorem. With p=vv* and Q=I-pM, the scalar identity gives pMp=p and Q*MQ=M-MpM. PSD congruence proves the complement, including singular M. This congruence supplies the reverse effect-lift implication below; its upper bound is M.

### One original effect exactly matches one common lift

For every unital L, every native vector v with v*v=1 and vv* in L, every natural m, and every list w:Fin(m) to F to the power J with each w(j)w(j)* in L, the following are equivalent. There exists one real linear f on all of L with Proper(f), f(vv*)=1, and f(w(j)w(j)*)=0 for every j. There exists one M in lifts(L) with v*Mw(j)=0 for every j. This equivalence is stronger than the normalized-pure-list clause because the rejected vectors need not have unit length. It includes the empty list and repeated entries. Lifting f and unit-f gives PSD E,F and M=E+F. The zero quadratic values force Fv=0 and Ew(j)=0. Conversely use E=Mvv*M and the complement M-E: on every original positive X their nonnegative readings sum to tr(X), giving whole-cone properness. The scalar readings are one at vv* and |v*Mw(j)| squared at each rejected rank one point. No inequality E<=I is used.

### Compact convex geometry and exact real affine dimension

For every L containing I, lifts(L) is nonempty, compact and convex. Every M in it has tr(M)=card(J). Its affine span has direction exactly L-perp, and hence its real affine dimension is real finrank(L-perp). I supplies nonemptiness. Orthogonality to I gives the trace equation; closedness and the existing PSD trace bound place the set in the compact order interval [0,card(J) I]. For each N in L-perp, ambient majorization gives t>=0 and a=1/(t+1)>0 with I+aN PSD. The direction of the affine span contains aN and therefore N, proving fullness without assuming it.

Parameter correspondence for these applications: F is the RCLike field, J is the Fintype index, H is HermitianMat J F with its real inner product, and L is a Submodule R H containing I. The functional f is a real LinearMap on the whole subtype L, not a list of effect values. A positive functional is nonnegative on every PSD member of L. Properness quantifies every such matrix and bounds f by unit(L)=trace restricted to L. The unit condition and original full carrier are hypotheses throughout; an ambient PSD representative is a conclusion. These conclusions require neither ROG nor a codimension bound. The empty index type is included for the positive-extension and geometry applications; the intended normalized physical carrier has n>=1.

Exact positive-extension substitution: for arbitrary ambient Y, set t=sum_j |eigenvalues(-Y)_j|. Matrix.PosSemidef.le_smul_one_of_eigenvalues_iff applied to (-Y).H, le_abs_self and Finset.single_le_sum give -Y<=t I and hence Y+t I>=0, with t I in L. Apply pinned Mathlib riesz_extension to PointedCone.positive R H and the partial map with domain L and value f; the order-majorizing witness for Y is t I. The resulting real linear extension g is continuous in finite dimension. InnerProductSpace.toDual R H, inverted at g.toContinuousLinearMap, gives E, and InnerProductSpace.toDual_symm_apply identifies its pairing with g. HermitianMat.zero_le_iff and Matrix.posSemidef_iff_dotProduct_mulVec, tested on every ambient rankOne(v), prove E PSD. The consumed native pair_rankOne and Matrix.posSemidef_vecMulVec_self_star supply exactly the quadratic reading and positivity. This is an application of those existing results, with no separate new mathematical declaration.

Exact finite-exclusion correspondence: m is any natural number, w is a function Fin(m) to native vectors, and each w(j)w(j)* lies in L. Unit length is required only for the confirmed vector v, whose vv* is in L. The excluded vectors may be unnormalized or zero, the finite list may be empty, and entries may repeat. Lifting f and unit-f by the preceding extension gives E,F. Matrix.PosSemidef.dotProduct_mulVec_zero_iff turns the zero quadratic readings into Fv=0 and Ew(j)=0. M=E+F has the trace-unit pairing on every X in L; L.mem_orthogonal' identifies this condition with M-I in L-perp. This proves the existential M direction without assuming any PSD lift as input.

For the converse, let M be any PSD matrix with M-I in L-perp and all v*Mw(j)=0. Pairing with vv* gives v*Mv=1. For p=vv*, put Q=I-pM and E=M p M. The scalar normalization gives pMp=p, so expansion gives Q* M Q=M-MpM. Matrix.PosSemidef.conjTranspose_mul_mul_same gives the PSD complement, and HermitianMat.conj_nonneg gives E PSD. This argument includes singular M and uses no inverse or square root. Restrict HermitianMat.innerₗ E to L; HermitianMat.inner_ge_zero applied to E and M-E gives 0<=f(X)<=tr(X) on every original positive X. The quadratic reading at vv* is one, and at each w(j)w(j)* is |v*Mw(j)| squared. The order bound is E<=M; no E<=I conclusion is required.

Exact geometry correspondence: M is the set (I+L-perp) intersect PSD in the same native ambient H. HermitianMat.isClosed_nonneg and Submodule.closed_of_finiteDimensional give closedness. Pairing M-I with I in L gives trace(M)=card(J). HermitianMat.le_trace_smul_one puts the set in [0,card(J) I], and isCompact_Icc.of_isClosed_subset gives compactness. I supplies nonemptiness; linear combinations with nonnegative real coefficients summing to one preserve PSD and the affine constraint, giving convexity. affineSpan_le and AffineSubspace.direction_le give the direction inclusion in L-perp. For each N in L-perp use the same ambient majorization and a=(t+1)^(-1)>0: I+aN is PSD and belongs to M. AffineSubspace.vsub_mem_direction between this point and I, followed by multiplication by a^(-1), yields N. Thus the direction is exactly L-perp and its real finrank is c. All quantifiers include c=0 and the empty ambient type.

The full frame below consumes the native rankOne operands, positivity and quadratic pairing. Its sum identity applies pinned OrthonormalBasis.sum_rankOne_eq_id directly and converts the operator identity by Matrix.toEuclideanLin.symm, InnerProductSpace.symm_toEuclideanLin_rankOne and Matrix.toLpLin_symm_id. The normalization, convex-hull and whole-pure-carrier helpers organize this live construction; they assert no independent mathematical novelty. The new step is the complementary-projector ROG construction of a new allowed orthogonal vector and its contradiction with maximality.

The full original frame and the positive-extension, finite-effect and geometry applications above preserve the normalized 96.1 clauses of QuantumVI Lemma 96.2. The application consequences reuse existing results; the new frame content is the complementary-projector maximality construction. The original arbitrary-unit support and determinant normalization from 93.2/94.2 remains an outside bridge. These results do not establish full Z0, classification, PRE, the separate QuantumVII facet theorem, or section 97 completion. The existing native Hermitian projector and orthonormal-basis results are reused; literature priority is not asserted.

## References

- Truth anchor: `D5/S3/Quantum/Foundation/SectionROGFrame.ROG`
- Truth anchor: `D5/S3/Quantum/Foundation/SectionROGFrame.base`
- Truth anchor: `D5/S3/Quantum/Foundation/SectionROGFrame.pair_rankOne`
- Truth anchor: `D5/S3/Quantum/Foundation/SectionROGFrame.pureRanks`
- Truth anchor: `D5/S3/Quantum/Foundation/SectionROGFrame.rankOne`
- Truth anchor: `D5/S3/Quantum/Foundation/SectionROGFrame.rankOne_nonneg`
- Truth anchor: `D5/S3/Quantum/Foundation/SectionROGFrame.rankOne_real_smul`
- Truth anchor: `D5/S3/Quantum/Foundation/SectionROGFrame.rankOne_trace_norm`
- Truth anchor: `D5/S3/Quantum/Foundation/SectionROGFrame.rog_frame`
- Truth anchor: `D5/S3/Quantum/Foundation/SectionROGFrame.whole_pure_carrier`
