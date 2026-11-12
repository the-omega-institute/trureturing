# Whole pure carriers and original ROG frames

## Abstract

The whole normalized pure carrier of a native real or complex ROG PSD section is exactly its unit rank one family, and each such point extends to a full original orthonormal rank one frame.

F is the real or complex field, J is a finite index type with decidable equality, H is the same real trace inner product space of native Hermitian matrices as in SectionPositiveLift, and L is a real linear subspace of H. Every vector belongs to the Euclidean space over its original field F. In the real case H is the symmetric matrix space. Complex rank one matrices are not realified. All positive matrices, states and rank one points remain in the same L.

**Definition 1.1 (The entire normalized base).**

Lean statement: `D5/S3/Quantum/Foundation/SectionROGFrame.base`

*Formalization.* `D5/S3/Quantum/Foundation/SectionROGFrame.base` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

base(L) is exactly the set of all X in H with X in L, X PSD and tr(X)=1. This is the whole original base embedded by the inclusion of L in H; it is not a chosen set of preparations.

**Definition 1.2 (ROG on every original positive matrix).**

Lean statement: `D5/S3/Quantum/Foundation/SectionROGFrame.ROG`

*Formalization.* `D5/S3/Quantum/Foundation/SectionROGFrame.ROG` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

ROG(L) means that every X in L which is PSD admits a finite list of nonzero native vectors w(j), each w(j)w(j)* in L, whose rank one matrices sum exactly to X. The list is indexed by Fin(m) for some natural m. Zero has an empty decomposition. This is finite generation by original native rank one PSD matrices, with no Jordan closure or supplied frame.

**Definition 1.3 (All normalized native rank one points).**

Lean statement: `D5/S3/Quantum/Foundation/SectionROGFrame.pureRanks`

*Formalization.* `D5/S3/Quantum/Foundation/SectionROGFrame.pureRanks` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

pureRanks(L) consists of every X for which there exists a native Euclidean vector v with norm one, vv*=X and X in L. No proper subconfiguration is selected.

**Theorem 1.4 (Extreme points equal the entire rank one family).**

Lean statement: `D5/S3/Quantum/Foundation/SectionROGFrame.whole_pure_carrier`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/SectionROGFrame.whole_pure_carrier` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real subspace L satisfying ROG(L), the real extreme points of the entire base(L) equal pureRanks(L). No assumption I in L is needed for this equality. Normalize every nonzero ROG term w(j) by its Euclidean norm and use its squared norm as the positive coefficient. The trace-one equation makes the coefficients sum to one, proving base(L)=convexHull(pureRanks(L)). Conversely a unit rank one p is extreme: the trace pairing <p,X> is at most one for every normalized PSD X, and equality forces X=p by the trace bound <X,X><=tr(X)^2 and the squared norm of X-p. A nontrivial segment decomposition of p therefore has both endpoints equal to p. This equality is consumed in rog_frame to identify every frame point as an original pure state.

**Theorem 1.5 (A full orthonormal frame with the prescribed entry).**

Lean statement: `D5/S3/Quantum/Foundation/SectionROGFrame.rog_frame`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/SectionROGFrame.rog_frame` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every L containing I and satisfying ROG(L), every native Euclidean unit vector v with vv* in L, and every designated index i in J, there exists an orthonormal basis b indexed by J such that b(i)=v, each b(j)b(j)* belongs to L, every such matrix is an extreme point of the whole base(L), and the sum over all j of b(j)b(j)* is I. Taking J=Fin(n) and i=0 gives exactly the frame with first vector v for every n>=1, including n=1 without dividing by n-1. Extend the singleton v to a maximal orthonormal subset whose rank one matrices stay in L. The projector onto its span is a sum of its original rank one matrices, so the residual complementary projector belongs to L. If that residual is nonzero, ROG gives a nonzero original rank one summand below it. Testing on the old span forces the summand vector into its orthogonal complement; normalization yields another allowed unit vector and contradicts maximality. Thus the complement is zero and the family is a full basis. Reindexing places v at the designated coordinate. No Jordan closure premise or chosen frame replaces ROG.

Together with SectionPositiveLift, these are the normalized 96.1 clauses of QuantumVI Lemma 96.2. The original arbitrary-unit support and determinant normalization from 93.2/94.2 remains an outside bridge. These results do not establish full Z0, classification, PRE, the separate QuantumVII facet theorem, or section 97 completion. The existing native Hermitian projector and orthonormal-basis results are reused; literature priority is not asserted.

## References

- Truth anchor: `D5/S3/Quantum/Foundation/SectionROGFrame.ROG`
- Truth anchor: `D5/S3/Quantum/Foundation/SectionROGFrame.base`
- Truth anchor: `D5/S3/Quantum/Foundation/SectionROGFrame.pureRanks`
- Truth anchor: `D5/S3/Quantum/Foundation/SectionROGFrame.rog_frame`
- Truth anchor: `D5/S3/Quantum/Foundation/SectionROGFrame.whole_pure_carrier`
- Dependency: [D5/S3/Quantum/Foundation/SectionPositiveLift](SectionPositiveLift.md)
