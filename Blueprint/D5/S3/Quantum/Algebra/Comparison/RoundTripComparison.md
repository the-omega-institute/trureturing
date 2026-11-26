# Metric and Periods from Round-Trip Comparison

## Abstract

Metric and Periods from Round-Trip Comparison.

**Theorem 1.1 (Metric and Periods from Round-Trip Comparison).**

$$\forall A \in Type,\; [\operatorname{NormedRing}\left(A\right)] [\operatorname{NormedAlgebra}\left(\mathbb{R}, A\right)] [\operatorname{CompleteSpace}\left(A\right)] [\operatorname{FiniteDimensional}\left(\mathbb{R}, A\right)] \forall L \in \operatorname{LieSubalgebra}\left(\mathbb{R}, A\right),\; \forall G \in \operatorname{Subgroup}\left(\operatorname{Units}\left(A\right)\right),\; \forall D \in \operatorname{Data}\left(L, G\right),\; \left(\forall X \in L,\; \operatorname{h}\left(D\right)\left(X, X\right) \ge 0 \land \left(\operatorname{h}\left(D\right)\left(X, X\right) = 0 \Rightarrow X = 0\right)\right) \land \left(\left(\forall t \in \mathbb{R},\; \forall X \in L,\; \operatorname{phi}\left(D\right)\left(\operatorname{exp}\left(D\right)\left((t \cdot X)\right)\right) = \operatorname{cos}\left((t \cdot \operatorname{sqrt}\left(\frac{\operatorname{h}\left(D\right)\left(X, X\right)}{2}\right))\right)^{2}\right) \land \left(\left(\forall t \in \mathbb{R},\; \forall X \in L,\; \operatorname{exp}\left(D\right)\left((t \cdot X)\right) = 1 \Leftrightarrow \left(\exists n \in \mathbb{Z},\; (t \cdot \operatorname{sqrt}\left(\frac{\operatorname{h}\left(D\right)\left(X, X\right)}{2}\right)) = (\pi \cdot n)\right)\right) \land \left(\forall C \in L,\; \forall X \in L,\; \forall Y \in L,\; \operatorname{h}\left(D\right)\left(\operatorname{bracket}\left(C, X\right), Y\right)+\operatorname{h}\left(D\right)\left(X, \operatorname{bracket}\left(C, Y\right)\right) = 0\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/Comparison/RoundTripComparison.metric_consequences` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let A be a complete finite-dimensional real normed associative unital algebra, L a real subspace closed under the commutator, and G a subgroup of its units. Assume exp(X) belongs to G for X in L and conjugation by G preserves L. The function phi on G takes values in [0,1], equals 1 precisely at the identity, satisfies phi(g*g)=(2*phi(g)-1)^2, and is invariant under conjugation.

The data also contain a symmetric real bilinear form h on L. As X tends to zero in the inherited norm, phi(exp(X))-(1-h(X,X)/2) is little-o of the squared norm. The neighborhood includes zero; faithfulness already fixes phi(exp(0))=1, so this does not strengthen the punctured germ together with that prescribed value.

In the displayed formula, Data(L,G) is the Lean comparison structure containing exactly these closure assumptions, the function phi, its symmetric form h, and the five comparison properties stated above. The notation h(D), phi(D), and exp(D) denotes respectively the form D.h, the function D.phi, and the exponential D.exp with values in G. The norm in the quadratic-germ condition is the inherited algebra norm.

Then h(X,X) is nonnegative, and vanishes only when X=0. For every real t and X in L, phi(exp(tX))=cos(t*sqrt(h(X,X)/2))^2. The exponential exp(tX) is the identity if and only if t*sqrt(h(X,X)/2)=pi*n for some integer n. This period equivalence includes X=0.

For all C,X,Y in L the form obeys h([C,X],Y)+h(X,[C,Y])=0. Thus the quadratic coefficient is an invariant positive definite form.

On each ray, boundedness forces the quadratic coefficient to be nonnegative. Applying the bounded duplication uniqueness theorem to 2*phi-1 gives the cosine formula. If the coefficient vanishes, faithfulness makes the entire exponential ray constant; its derivative at zero forces X=0. Conjugation invariance of the quadratic germ supplies the infinitesimal identity.

These are conditional statements about the given algebra, subgroup and function. They impose no group topology beyond the ambient algebra used in the germ, and do not identify a physical comparison function or classify global groups.

## References

- Truth anchor: `D5/S3/Quantum/Algebra/Comparison/RoundTripComparison.metric_consequences`
- Dependency: [D5/S3/Analytic/Dilation/DuplicationQuadraticGerm](../../../Analytic/Dilation/DuplicationQuadraticGerm.md)
- Dependency: [D5/S3/QuadraticForms/QuadraticGermInvariance](../../../QuadraticForms/QuadraticGermInvariance.md)
