# Commuting Directions Have Rank One

## Abstract

Commuting Directions Have Rank One.

**Theorem 1.1 (Commuting Directions Have Rank One).**

$$\forall A \in Type,\; [\operatorname{NormedRing}\left(A\right)] [\operatorname{NormedAlgebra}\left(\mathbb{R}, A\right)] [\operatorname{CompleteSpace}\left(A\right)] [\operatorname{FiniteDimensional}\left(\mathbb{R}, A\right)] \forall L \in \operatorname{LieSubalgebra}\left(\mathbb{R}, A\right),\; \forall G \in \operatorname{Subgroup}\left(\operatorname{Units}\left(A\right)\right),\; \operatorname{Data}\left(L, G\right) \to \forall X \in L,\; \forall Y \in L,\; \left(X \ne 0 \land \operatorname{bracket}\left(X, Y\right) = 0\right) \Rightarrow \left(\exists c \in \mathbb{R},\; Y = (c \cdot X)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/Comparison/RoundTripRankOne.centralizer_line` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Use the comparison data of RoundTripComparison: a complete finite-dimensional real normed associative unital algebra A, a commutator-closed real subspace L, a subgroup G containing its exponentials and preserving L by conjugation, and the bounded faithful conjugation-invariant function with duplication and symmetric quadratic germ h.

In the displayed formula, Data(L,G) is the Lean structure containing exactly the stated closure, boundedness, faithfulness, duplication, conjugation and symmetric quadratic-germ hypotheses. The anonymous Data(L,G) premise means that such comparison data are given; the conclusion does not otherwise depend on a choice of name for those data.

For every nonzero X in L and every Y in L satisfying [X,Y]=0, there is a real scalar c with Y=cX. In particular, every commuting pair is linearly dependent; if X=0 the latter conclusion is immediate.

The preceding metric theorem makes h an inner product. On the span of X and Y all elements commute, so the points whose exponentials are the identity form an additive subgroup. The exact cosine formula puts the entire h-sphere of radius sqrt(2)*pi in this kernel and excludes its sphere of half that radius. The spherical additive-kernel theorem therefore bounds the dimension of the span by one. Since X is nonzero it spans this space.

The norm induced by h is used only in this finite-dimensional geometric argument. The original quadratic-germ hypothesis remains in the inherited algebra norm; no equality between these norms is assumed. The conclusion concerns infinitesimal commuting directions and asserts no global group classification.

## References

- Truth anchor: `D5/S3/Quantum/Algebra/Comparison/RoundTripRankOne.centralizer_line`
- Dependency: [D5/S3/Geometry/SphericalAdditiveKernel](../../../Geometry/SphericalAdditiveKernel.md)
- Dependency: [D5/S3/Quantum/Algebra/Comparison/RoundTripComparison](RoundTripComparison.md)
