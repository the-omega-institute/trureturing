# Original Compact-Action Reciprocity

## Abstract

The entire original first-order relation forces dimension three on the same compact matrix action.

**Definition 1.1 (The actual matrix tangent Lie algebra).**

$$\operatorname{Lie}\left(G\right)=\{K:\ \exists c:R \to G,\ \operatorname{c}\left(0\right)=1 \land \operatorname{HasDerivAt}\left(\operatorname{originalOperatorCurve}\left(c\right), K, 0\right)\}$$

*Formalization.* `D5/S3/Quantum/Algebra/OriginalCompactReciprocity.curveLieAlgebra` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Fix any finite-dimensional real inner product space W and an actual subgroup G of the units of its continuous endomorphism algebra. The initially chosen inner product is auxiliary; invariance is derived from compactness. The underlying submodule of curveLieAlgebra G consists exactly of all ambient operator derivatives at zero of actual G-valued curves c with c(0)=1. The curves require the displayed ambient derivative at zero; global regularity is not part of this definition. No abstract algebra, chosen smaller representation, rank or dimension is supplied instead.

Products of original curves prove addition of velocities, scalar reparametrization proves scalar closure, and constant conjugation preserves velocities. Differentiate the conjugation of a velocity L by a curve with velocity K. Mathlib's derivative of inversion in a normed algebra gives derivative KL-LK. Difference quotients stay in the actual velocity subspace, which is closed because it is finite dimensional. Thus the original matrix commutator closes on exactly this tangent carrier. Compactness is not needed for this construction.

**Definition 1.2 (Every solution of the original equation).**

$$\operatorname{T}\left(A, x\right)=\operatorname{Image}\left(quotientPair, \operatorname{Ker}\left(evaluationPlusAction\right)\right)$$

*Formalization.* `D5/S3/Quantum/Algebra/OriginalCompactReciprocity.fullRelation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For A in this actual tangent Lie algebra and x in the full W, fullRelation is the submodule image of the kernel of (K,y) maps to Kx+Ay under the product of the two canonical quotient maps by the real spans of A and x. It therefore includes all solutions and makes no selection of a compensation graph. Under Ax=0, changing representatives by real multiples of A and x leaves the equation unchanged. FullReciprocity requires both canonical projections of this entire submodule to be bijective.

**Theorem 1.3 (Both original dimensions are three).**

$$\forall W,G,\ \operatorname{FiniteDimensionalRealInnerProductSpace}\left(W\right) \land \operatorname{SubgroupOfUnitsEnd}\left(G, W\right) \land \operatorname{IsCompact}\left(G\right) \Rightarrow \forall A:\operatorname{Lie}\left(G\right),\ \forall x:W,\ A\neq0 \land x\neq0 \land \operatorname{A}\left(x\right)=0 \land \operatorname{FullReciprocity}\left(G, A, x\right) \Rightarrow \operatorname{finrank}\left(R, W\right)=3 \land \operatorname{finrank}\left(R, \operatorname{Lie}\left(G\right)\right)=3$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/OriginalCompactReciprocity.finrank_eq_three` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume only that the original subgroup is compact and that A and x are nonzero, Ax=0, and FullReciprocity holds. Then the real dimensions of the original W and its actual curve Lie algebra are both three. Nontriviality of W follows from the nonzero witness; all finite dimensions remain in the quantified domain. There is no irreducibility, transitivity, centralizer, rank, dimension or invariant-metric premise.

Injectivity of the two original projections forces ker(A) to be the real line through x, and the kernel of evaluation at x to be the real line through A. Both bijections identify the quotient spaces, so rank-nullity transfers equality of the two original dimensions. The invariant positive form is constructed by OriginalCompactActionMetric.compact_action_metric on this same compact G and full W; every original curve velocity is skew for that form. Commutation with A puts Kx in ker(A), skewness makes that multiple orthogonal to x, and definiteness forces it to zero. Evaluation's kernel then gives the centralizer line through A.

On the actual tangent Lie algebra the proof constructs kappa(K,L)=-one-half times the real trace on W of KL. An orthonormal basis for the derived positive form expresses minus trace(K squared) as a sum of squared norms of K applied to basis vectors, strictly positive for every nonzero faithful operator. Cyclic trace proves symmetry and adjoint invariance. The proof actually applies RankOneInvariantMetric.finrank_eq_one_or_three with this constructed metric and the derived centralizer line. Equality of the original dimensions and Ax=0 exclude dimension one: in that case x spans all of W, making A the zero actual operator. Both dimensions are therefore three.

This is a source-faithful dependency of OMEGAQ-008 Theorem 5.1, Sections 2 through 5, on its actual original matrix action. A formal comparison of the direct curve construction with separately supplied manifold GroupLieAlgebra or exponential-membership conventions is not supplied. Integration to the actual identity component SO, the SO/O group alternatives, the reverse full-relation implication, and the probability frontend remain outside these algebraic theorems.

**Theorem 1.4 (The original action fills the orthogonal Lie algebra).**

$$\forall W,G,\ \operatorname{FiniteDimensionalRealInnerProductSpace}\left(W\right) \land \operatorname{SubgroupOfUnitsEnd}\left(G, W\right) \land \operatorname{IsCompact}\left(G\right) \Rightarrow \forall A:\operatorname{Lie}\left(G\right),\ \forall x:W,\ A\neq0 \land x\neq0 \land \operatorname{A}\left(x\right)=0 \land \operatorname{FullReciprocity}\left(G, A, x\right) \Rightarrow \exists B:\operatorname{InnerProductSpaceCore}\left(R, W\right),\ (\forall h:G,\ \forall u,v:W,\ \operatorname{B}\left(\operatorname{h}\left(u\right), \operatorname{h}\left(v\right)\right)=\operatorname{B}\left(u, v\right)) \land \operatorname{finrank}\left(R, W\right)=3 \land \operatorname{finrank}\left(R, \operatorname{Lie}\left(G\right)\right)=3 \land \operatorname{range}\left(\operatorname{originalAction}\left(G\right)\right)=\operatorname{skewEndomorphisms}\left(B\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/OriginalCompactReciprocity.original_rigidity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under exactly the same compactness, nonzero-witness, annihilation and entire-relation hypotheses, there exists a positive form B invariant under the original G such that both original dimensions are three and the range of the actual inclusion of its curve Lie algebra into End(W) equals all B-skew endomorphisms of that same W. The inclusion is the original matrix action. Neither a supplied representation isomorphism nor a separately assumed dimension or centralizer is used.

The dimension theorem supplies the three-dimensional faithful range. For a positive form on a three-dimensional space, the three off-diagonal coefficients in an orthonormal basis determine a skew endomorphism: the diagonal coefficients vanish and skewness determines the remaining coefficients. This embeds the full skew subspace into three real coordinates, giving its dimension at most three. Every actual curve velocity is B-skew, so the faithful three-dimensional range is a subspace of that skew subspace with the same dimension and therefore equals it.

## References

- Truth anchor: `D5/S3/Quantum/Algebra/OriginalCompactReciprocity.curveLieAlgebra`
- Truth anchor: `D5/S3/Quantum/Algebra/OriginalCompactReciprocity.finrank_eq_three`
- Truth anchor: `D5/S3/Quantum/Algebra/OriginalCompactReciprocity.fullRelation`
- Truth anchor: `D5/S3/Quantum/Algebra/OriginalCompactReciprocity.original_rigidity`
- Dependency: [D5/S3/Quantum/Algebra/OriginalCompactActionMetric](OriginalCompactActionMetric.md)
- Dependency: [D5/S3/Quantum/Algebra/RankOneInvariantMetric](RankOneInvariantMetric.md)
