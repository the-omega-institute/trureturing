# Phase rigidity of interior signed kernel levels

## Abstract

Four nonzero signed kernel entries force a single strict phase along the actual chronological prefix.

A word is an arbitrary finite list of Boolean actions, with false denoting M=[[0,1],[1,1]] and true denoting J=[[0,1],[1,0]]. Its head acts first, T([])=I, and T(u++v)=T(v)T(u). Three supplied words w:Fin 3 -> List Bool determine the original cumulative matrices A_i=prefixMatrix(w,i), i=0,1,2,3. Thus A_0=I and A_(i+1)=T(w_i)A_i. Empty multipliers and nonempty words whose matrix is I remain included.

The predicate G_+(w,N) is the unchanged OrientedKernelGenerator: N is a nonzero real rank-one matrix, the full prefix-difference kernel is exactly its real span, and its determinant polar is strictly positive on every entrywise positive rank-one matrix. This kernel condition on the four-dimensional source has rank-three prefix differences. PrimitiveCoordinates consists of nonnegative integers p=(a,b,c,d), gcd(a,b)=gcd(c,d)=1 and t=ac+bd>0. Put f=(a,-b), ell=(c,-d), r=(d,c), F(p)=f ell. These are auxiliary signed columns and rows. Theorem 3.2 supplies N=s F(p) for a positive real s, and integer m_i with m_0=0 and A_i f=f+m_i r at every original index.

P_+ denotes exactly the subset a,b,c,d>0. For a primitive outer product this is equivalent to all four entries being nonzero. Mixed(v) means either v_0>0>v_1 or v_1>0>v_0. Positive(v) means both coordinates are strictly positive.

**Theorem 1.1 (Mixed signed level endpoints are the identity).**

$$\forall u, \forall p\in P_{+}, \operatorname{Mixed}(\operatorname{T}(u)f)\land ell\operatorname{T}(u)f= t\implies \operatorname{T}(u)= I$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/CubicGain/PhaseRigidity.mixed_level_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite native word u and every p in P_+, if v=T(u)f is mixed and c*v_0-d*v_1=t, then its actual matrix T(u) is I. This is an endpoint assertion about the supplied word, and does not assert that the word is empty.

Along any word, the image of f lies either in a closed nonnegative orthant, in a closed nonpositive orthant, or in the coordinate box [-b,a]^2. Both closed orthants are preserved by M and J. For a mixed vector, J exchanges coordinates and M replaces one coordinate by their sum; when the two signs differ that sum lies between the original coordinates. Induction therefore bounds every mixed image in the box. The level t>0 excludes the orientation (-,+). In the remaining orientation, the positive weights c,d and the upper bounds force the vector to equal f.

Write a nonnegative real unimodular matrix fixing f as [[h,u],[g,e]]. The fixed-vector equations imply e>=1 and a*det(A)=a*e+b*u. Since det(A)<=1, positivity of a,b and nonnegativity give u=0 and e=1, then g=0 and h=1. This argument applies to the actual legal word matrix, whose nonnegative entries and either determinant sign come from the legal monoid theorem.

Define w'_i=[J]++w_i++[J] and p'=(b,a,d,c). Then at every original index A'_i=J A_i J, f'=-Jf, ell'=-ell J and F(p')=J F(p) J. In particular an empty multiplier becomes the nonempty identity word [J,J]. The conjugate image is A'_i f'=-J A_i f and its lattice parameter is -m_i. Let Phi(w,p,m) mean m_0=0, all four original lattice equations, Positive(A_i f) at i=1,2,3, and 1<=m_1<m_2<m_3.

**Theorem 1.2 (The original history or its literal conjugate has a strict positive phase).**

$$\forall w,N, G_{+}(w,N)\land \operatorname{allEntriesNonzero}(N)\implies \exists p\in P_{+}, \exists s> 0, \exists m\in \mathbb{Z}^{4}, N= s\operatorname{F}(p)\land \operatorname{m}(0)= 0\land (\forall i\in \operatorname{Fin}(4), A_{i}f= f+ m_{i}r)\land (\forall i\in \operatorname{Fin}(4), A'_{i}= JA_{i}J)\land JNJ= s\operatorname{F}(p')\land (\operatorname{Phi}(w,p,m)\lor \operatorname{Phi}(w',p',-m))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/CubicGain/PhaseRigidity.phase_rigidity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every supplied word triple w and every arbitrary real positively oriented generator N with all four entries nonzero, there exist primitive p in P_+, a positive real scale s and integer parameters m on exactly Fin 4. They satisfy N=s F(p), m_0=0 and all original equations A_i f=f+m_i r. Every conjugate endpoint equals J A_i J. Either Phi(w,p,m) holds, or Phi(w',p',-m) holds. Neither positivity of the noninitial images nor parameter order is assumed. Both conjugate branches retain their actual finite multipliers and the same recorded indices.

The primitive lattice theorem supplies the coordinates, scale and parameters. Nonzero diagonal entries of N force all four coordinates to be positive. The bijective original four-trace map makes the four endpoint matrices distinct, so no noninitial endpoint is I. The mixed-level result excludes a mixed first image. Primitive integer coordinates are preserved by every M or J action, using the coprime swap and addition laws. A zero coordinate would therefore make the other coordinate 1 or -1. Its level would be one of c,-c,d,-d, whereas t>=c+d>max(c,d). Thus the first noninitial image is strictly positive or strictly negative. Every subsequent actual word preserves that strict orthant. In the negative branch, literal conjugation and the coordinate swap make all three images positive.

On a strictly positive column, J preserves coordinate sum and M strictly increases it. Induction proves sum monotonicity along every word, and that equality can occur only when the matrix is I or J. On the lattice line the sum grows with m because c+d>0. Equality of two consecutive parameters would fix the positive column. The I case repeats the endpoint. The J case makes its two coordinates equal; primitivity forces both to be 1, contradicting the level bound. Hence consecutive parameters are strictly increasing. The second coordinate -b+m_1*c>0 and integer m_1 give m_1>=1.

The mixed-level theorem also applies directly to every recorded image satisfying its original level, and therefore excludes every nonidentity mixed-phase endpoint. The four-nonzero-entry assumption belongs to this interior theorem; no claim about zero-entry kernels is inferred from it. These phase statements do not assert the later integer transition normal form or identity-only final-level theorem.

## References

- Truth anchor: `D5/S3/Observer/CubicGain/PhaseRigidity.mixed_level_identity`
- Truth anchor: `D5/S3/Observer/CubicGain/PhaseRigidity.phase_rigidity`
- Dependency: [D5/S3/Observer/CubicGain/PrimitiveKernelLattice](PrimitiveKernelLattice.md)
