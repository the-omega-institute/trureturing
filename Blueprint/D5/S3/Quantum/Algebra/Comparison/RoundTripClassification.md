# Classification from Round-Trip Comparison

## Abstract

Classification from Round-Trip Comparison.

**Theorem 1.1 (Classification from Round-Trip Comparison).**

$$\forall A \in Type,\; [\operatorname{NormedRing}\left(A\right)] [\operatorname{NormedAlgebra}\left(\mathbb{R}, A\right)] [\operatorname{CompleteSpace}\left(A\right)] [\operatorname{FiniteDimensional}\left(\mathbb{R}, A\right)] \forall L \in \operatorname{LieSubalgebra}\left(\mathbb{R}, A\right),\; \forall G \in \operatorname{Subgroup}\left(\operatorname{Units}\left(A\right)\right),\; \forall D \in \operatorname{Data}\left(L, G\right),\; \left(\forall X \in L,\; \operatorname{h}\left(D\right)\left(X, X\right) \ge 0 \land \left(\operatorname{h}\left(D\right)\left(X, X\right) = 0 \Rightarrow X = 0\right)\right) \land \left(\left(\forall t \in \mathbb{R},\; \forall X \in L,\; \operatorname{phi}\left(D\right)\left(\operatorname{exp}\left(D\right)\left((t \cdot X)\right)\right) = \operatorname{cos}\left((t \cdot \operatorname{sqrt}\left(\frac{\operatorname{h}\left(D\right)\left(X, X\right)}{2}\right))\right)^{2}\right) \land \left(\left(\forall t \in \mathbb{R},\; \forall X \in L,\; \operatorname{exp}\left(D\right)\left((t \cdot X)\right) = 1 \Leftrightarrow \left(\exists n \in \mathbb{Z},\; (t \cdot \operatorname{sqrt}\left(\frac{\operatorname{h}\left(D\right)\left(X, X\right)}{2}\right)) = (\pi \cdot n)\right)\right) \land \left(\left(\forall X \in L,\; \forall Y \in L,\; \operatorname{bracket}\left(X, Y\right) = 0 \Rightarrow \left(X = 0 \lor \left(\exists c \in \mathbb{R},\; Y = (c \cdot X)\right)\right)\right) \land \left(\left(\forall C \in L,\; \forall X \in L,\; \forall Y \in L,\; \operatorname{h}\left(D\right)\left(\operatorname{bracket}\left(C, X\right), Y\right)+\operatorname{h}\left(D\right)\left(X, \operatorname{bracket}\left(C, Y\right)\right) = 0\right) \land \left(\left(\operatorname{finrank}\left(\mathbb{R}, L\right) = 0 \lor \left(\operatorname{finrank}\left(\mathbb{R}, L\right) = 1 \lor \operatorname{finrank}\left(\mathbb{R}, L\right) = 3\right)\right) \land \left(\operatorname{finrank}\left(\mathbb{R}, L\right) = 3 \Rightarrow \left(\exists b \in \operatorname{Basis}\left(\operatorname{Fin}\left(3\right), \mathbb{R}, L\right),\; \exists mu \in \mathbb{R},\; mu > 0 \land \left(\left(\forall i \in \operatorname{Fin}\left(3\right),\; \forall j \in \operatorname{Fin}\left(3\right),\; \operatorname{h}\left(D\right)\left(b\left(i\right), b\left(j\right)\right) = \operatorname{if} (i = j) \operatorname{then} 1 \operatorname{else} 0\right) \land \left(\operatorname{bracket}\left(b\left(0\right), b\left(1\right)\right) = (mu \cdot b\left(2\right)) \land \left(\operatorname{bracket}\left(b\left(1\right), b\left(2\right)\right) = (mu \cdot b\left(0\right)) \land \operatorname{bracket}\left(b\left(2\right), b\left(0\right)\right) = (mu \cdot b\left(1\right))\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/Comparison/RoundTripClassification.comparison_classification` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let A be a complete finite-dimensional real normed associative unital algebra, L a real subspace closed under the commutator, and G a subgroup of its units. Assume exp(X) belongs to G for X in L and conjugation by G preserves L. The function phi on G takes values in [0,1], equals 1 precisely at the identity, satisfies phi(g*g)=(2*phi(g)-1)^2, and is invariant under conjugation.

The data also contain a symmetric real bilinear form h on L. As X tends to zero in the inherited norm, phi(exp(X))-(1-h(X,X)/2) is little-o of the squared norm. The neighborhood includes zero; faithfulness already fixes phi(exp(0))=1, so this does not strengthen the punctured germ together with that prescribed value.

In the displayed formula, Data(L,G) is the Lean comparison structure containing exactly these closure assumptions, the function phi, its symmetric form h, and the five comparison properties stated above. The notation h(D), phi(D), and exp(D) denotes respectively the form D.h, the function D.phi, and the exponential D.exp with values in G. The norm in the quadratic-germ condition is the inherited algebra norm.

Then h(X,X) is nonnegative, and vanishes only when X=0. For every real t and X in L, phi(exp(tX))=cos(t*sqrt(h(X,X)/2))^2. The exponential exp(tX) is the identity if and only if t*sqrt(h(X,X)/2)=pi*n for some integer n. This period equivalence includes X=0.

For all C,X,Y in L the form obeys h([C,X],Y)+h(X,[C,Y])=0. Thus the quadratic coefficient is an invariant positive definite form.

On each ray, boundedness forces the quadratic coefficient to be nonnegative. Applying the bounded duplication uniqueness theorem to 2*phi-1 gives the cosine formula. If the coefficient vanishes, faithfulness makes the entire exponential ray constant; its derivative at zero forces X=0. Conjugation invariance of the quadratic germ supplies the infinitesimal identity.

Every commuting pair is linearly dependent. The real dimension of L is zero, one or three. In dimension three there is an h-orthonormal basis b indexed by Fin 3 and a positive real number mu such that [b(0),b(1)]=mu*b(2), [b(1),b(2)]=mu*b(0), and [b(2),b(0)]=mu*b(1). The centralizer-line theorem is combined with the existing rank-one invariant-metric dimension theorem. Its original orthonormal frame is reused to supply the displayed basis; the dimension classification is not reproved here. These are conditional statements about the given algebra, subgroup and function. They impose no group topology beyond the ambient algebra used in the germ, and do not identify a physical comparison function or classify global groups.

Both nonzero dimensions occur. For the unit complex numbers, take the purely imaginary line and phi(g)=(1+Re(g))/2. For the unit quaternions, take the three-dimensional purely imaginary subspace and the same phi. In either case h is one half of the ambient Euclidean inner product. Unit norm bounds the real part and makes Re(g)=1 equivalent to g=1; Re(g squared)=2 Re(g) squared-1 proves duplication, and the real part is invariant under unit conjugation. On purely imaginary X, Re(exp(X))=cos(norm(X)), whose quadratic remainder gives h(X,X)=norm(X) squared/2. These identities provide the stated hypotheses and dimensions one and three. In the quaternion case the h-orthonormal frame is sqrt(2) times i,j,k, and its positive cyclic bracket constant is 2*sqrt(2).

## References

- Truth anchor: `D5/S3/Quantum/Algebra/Comparison/RoundTripClassification.comparison_classification`
- Dependency: [D5/S3/Quantum/Algebra/Comparison/RoundTripRankOne](RoundTripRankOne.md)
- Dependency: [D5/S3/Quantum/Algebra/RankOneInvariantMetric](../RankOneInvariantMetric.md)
