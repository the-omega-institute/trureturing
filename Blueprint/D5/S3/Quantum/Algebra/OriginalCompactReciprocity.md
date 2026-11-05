# Original Compact-Action Reciprocity

## Abstract

Actual curve-exponential membership and the entire first-order relation on the same compact matrix action.

**Definition 1.1 (The actual matrix tangent Lie algebra).**

$$\forall W,G,\ \operatorname{FiniteDimensionalRealInnerProductSpace}\left(W\right) \land \operatorname{SubgroupOfUnitsEnd}\left(G, W\right) \Rightarrow \forall K:\operatorname{ContinuousEnd}\left(R, W\right),\ \operatorname{Member}\left(K, \operatorname{Carrier}\left(\operatorname{curveLieAlgebra}\left(G\right)\right)\right) \iff \exists c:R \to G,\ \operatorname{c}\left(0\right)=1 \land \operatorname{HasDerivAt}\left(\operatorname{originalOperatorCurve}\left(c\right), K, 0\right)$$

*Formalization.* `D5/S3/Quantum/Algebra/OriginalCompactReciprocity.curveLieAlgebra` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Fix any finite-dimensional real inner product space W and an actual subgroup G of the units of its continuous endomorphism algebra. The initially chosen inner product is auxiliary; invariance is derived from compactness. The underlying submodule of curveLieAlgebra G consists exactly of all ambient operator derivatives at zero of actual G-valued curves c with c(0)=1. The curves require the displayed ambient derivative at zero; global regularity is not part of this definition. No abstract algebra, chosen smaller representation, rank or dimension is supplied instead.

Products of original curves prove addition of velocities, scalar reparametrization proves scalar closure, and constant conjugation preserves velocities. Differentiate the conjugation of a velocity L by a curve with velocity K. Mathlib's derivative of inversion in a normed algebra gives derivative KL-LK. Difference quotients stay in the actual velocity subspace, which is closed because it is finite dimensional. Thus the original matrix commutator closes on exactly this tangent carrier. Compactness is not needed for this construction.

**Definition 1.2 (Every solution of the original equation).**

$$\forall W,G,\ \operatorname{FiniteDimensionalRealInnerProductSpace}\left(W\right) \land \operatorname{SubgroupOfUnitsEnd}\left(G, W\right) \Rightarrow \forall A:\operatorname{Lie}\left(G\right),\ \forall x:W,\ \operatorname{fullRelation}\left(G, A, x\right)=\operatorname{Image}\left(\operatorname{quotientPair}\left(G, A, x\right), \operatorname{Ker}\left(\operatorname{evaluationPlusAction}\left(G, A, x\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Algebra/OriginalCompactReciprocity.fullRelation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For A in this actual tangent Lie algebra and x in the full W, fullRelation is the submodule image of the kernel of (K,y) maps to Kx+Ay under the product of the two canonical quotient maps by the real spans of A and x. It therefore includes all solutions and makes no selection of a compensation graph. Under Ax=0, changing representatives by real multiples of A and x leaves the equation unchanged. FullReciprocity requires both canonical projections of this entire submodule to be bijective.

**Theorem 1.3 (Original curves and all real exponentials).**

$$\forall W,G,\ \operatorname{FiniteDimensionalRealInnerProductSpace}\left(W\right) \land \operatorname{SubgroupOfUnitsEnd}\left(G, W\right) \land \operatorname{IsCompact}\left(G\right) \Rightarrow \forall K:\operatorname{ContinuousEnd}\left(R, W\right),\ (\operatorname{Member}\left(K, \operatorname{velocitySpace}\left(G\right)\right)) \iff (\forall t:R,\ \exists u:\operatorname{UnitsContinuousEnd}\left(R, W\right),\ \operatorname{Member}\left(u, G\right) \land \operatorname{value}\left(u\right)=\operatorname{exp}\left(t\cdot K\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/OriginalCompactReciprocity.mem_velocitySpace_iff_exp` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the same arbitrary finite-dimensional real inner product space W, the same subgroup G of actual units in its continuous endomorphism algebra, and compactness of that original G, an operator K belongs to velocitySpace G exactly when for every real t an actual unit of G has value exp(t K). The forward curve needs only its ambient derivative at zero and value one there. Zero-dimensional W, zero K, zero and negative real time all remain in scope. No manifold, globally differentiable curve, Euler invertibility, equivalent norm or power-bound certificate is assumed.

In the complete ambient endomorphism algebra, Mathlib's strict derivative of exp at zero is the identity. Apply its inverse function theorem to obtain a local inverse ell with ell(1)=0, derivative identity at one, and exp(ell(y))=y near one. Composing only the given actual curve with ell gives derivative K at zero. The native HasFDerivAt.lim rescaling theorem gives n times ell(c(t/n)) tending to t K. Continuity of exp and exp_nsmul turn this into the exact limit c(t/n)^n tending to exp(t K). The value image of the original compact unit subgroup is compact and closed in the ambient algebra; every sampled power is an actual group element. Closedness therefore supplies an actual unit of G at the limit.

For the reverse implication choose the supplied actual units at each time. Unit and subgroup extensionality give the identity at zero; their ambient values are exactly the exponential curve, whose derivative there is K. The proof does not use an unproved Banach-algebra logarithm API or a Lie-group structure on the closed subgroup. This equivalence is used by the original identity-component consumer below; the operational probability frontend requires a separate construction.

**Theorem 1.4 (Both original dimensions are three).**

$$\forall W,G,\ \operatorname{FiniteDimensionalRealInnerProductSpace}\left(W\right) \land \operatorname{SubgroupOfUnitsEnd}\left(G, W\right) \land \operatorname{IsCompact}\left(G\right) \Rightarrow \forall A:\operatorname{Lie}\left(G\right),\ \forall x:W,\ A\neq0 \land x\neq0 \land \operatorname{A}\left(x\right)=0 \land \operatorname{FullReciprocity}\left(G, A, x\right) \Rightarrow \operatorname{finrank}\left(R, W\right)=3 \land \operatorname{finrank}\left(R, \operatorname{Lie}\left(G\right)\right)=3$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/OriginalCompactReciprocity.finrank_eq_three` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume only that the original subgroup is compact and that A and x are nonzero, Ax=0, and FullReciprocity holds. Then the real dimensions of the original W and its actual curve Lie algebra are both three. Nontriviality of W follows from the nonzero witness; all finite dimensions remain in the quantified domain. There is no irreducibility, transitivity, centralizer, rank, dimension or invariant-metric premise.

Injectivity of the two original projections forces ker(A) to be the real line through x, and the kernel of evaluation at x to be the real line through A. Both bijections identify the quotient spaces, so rank-nullity transfers equality of the two original dimensions. The invariant positive form is constructed by OriginalCompactActionMetric.compact_action_metric on this same compact G and full W; every original curve velocity is skew for that form. Commutation with A puts Kx in ker(A), skewness makes that multiple orthogonal to x, and definiteness forces it to zero. Evaluation's kernel then gives the centralizer line through A.

On the actual tangent Lie algebra the proof constructs kappa(K,L)=-one-half times the real trace on W of KL. An orthonormal basis for the derived positive form expresses minus trace(K squared) as a sum of squared norms of K applied to basis vectors, strictly positive for every nonzero faithful operator. Cyclic trace proves symmetry and adjoint invariance. The proof actually applies RankOneInvariantMetric.finrank_eq_one_or_three with this constructed metric and the derived centralizer line. Equality of the original dimensions and Ax=0 exclude dimension one: in that case x spans all of W, making A the zero actual operator. Both dimensions are therefore three.

This is a source-faithful dependency of OMEGAQ-008 Theorem 5.1, Sections 2 through 5, on its actual original matrix action. The curve-exponential equivalence in this document supplies the comparison with the all-real matrix exponential-membership convention. The reverse full-relation implication is constructed below from the full skew range. A separately supplied manifold GroupLieAlgebra identification and the probability frontend require their respective further constructions. The original group theorem below proves the identity-component equality and the SO/O alternatives directly from the actual curve velocities.

**Theorem 1.5 (Original skew exponentials lie in the original component).**

$$\forall W,G,\ \operatorname{FiniteDimensionalRealInnerProductSpace}\left(W\right) \land \operatorname{SubgroupOfUnitsEnd}\left(G, W\right) \land \operatorname{IsCompact}\left(G\right) \Rightarrow \forall A:\operatorname{Lie}\left(G\right),\ \forall x:W,\ A\neq0 \land x\neq0 \land \operatorname{A}\left(x\right)=0 \land \operatorname{FullReciprocity}\left(G, A, x\right) \Rightarrow \exists B:\operatorname{InnerProductSpaceCore}\left(R, W\right),\ (\forall h:G,\ \forall u,v:W,\ \operatorname{B}\left(\operatorname{h}\left(u\right), \operatorname{h}\left(v\right)\right)=\operatorname{B}\left(u, v\right)) \land \operatorname{finrank}\left(R, W\right)=3 \land \operatorname{finrank}\left(R, \operatorname{Lie}\left(G\right)\right)=3 \land \operatorname{range}\left(\operatorname{originalAction}\left(G\right)\right)=\operatorname{skewEndomorphisms}\left(B\right) \land (\forall h:G,\ \operatorname{Member}\left(h, \operatorname{connectedComponent}\left(1, G\right)\right) \Rightarrow \operatorname{det}\left(\operatorname{originalValue}\left(h\right)\right)=1) \land \forall K:\operatorname{ContinuousEnd}\left(R, W\right),\ \operatorname{Member}\left(\operatorname{underlyingLinearMap}\left(K\right), \operatorname{skewEndomorphisms}\left(B\right)\right) \Rightarrow \forall t:R,\ \exists h:G,\ \operatorname{Member}\left(h, \operatorname{connectedComponent}\left(1, G\right)\right) \land \operatorname{originalValue}\left(h\right)=\operatorname{exp}\left(t\cdot K\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/OriginalCompactReciprocity.original_exponential_rigidity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the original compactness and full-relation witness assumptions, the same derived positive form B is invariant under G, both original dimensions are three, and the original inclusion fills all B-skew endomorphisms. Every element in the actual identity connected component has determinant one. For every continuous endomorphism K whose underlying linear map is B-skew and every real t, an actual element of that component has value exp(t K).

The actual curve-exponential equivalence first puts each exponential unit in G. The unit is packaged from Mathlib's isUnit_exp. Its value is exp(t K) and its inverse value is exp(-t K); continuity of both coordinates proves continuity in the actual units topology. The resulting G-valued curve passes through one. Its connected image lies in the connected component of one. The original full-skew range equality supplies membership of each requested K in the actual velocity subspace.

The determinant restriction uses an orthonormal basis for B to identify each original group element with an actual orthogonal matrix, hence its determinant has square one. The determinant is continuous in the original operator topology. On the connected component of one the sign is constant, and the identity fixes it to one. Thus this actual component is contained in SO(W,B), while it contains all skew exponentials. The original group theorem below supplies all of SO(W,B) by products of actual skew exponentials and proves the opposite component inclusion and G=SO or O. This exponential theorem does not assume those conclusions and does not substitute the ambient orthogonal group for the original G.

**Theorem 1.6 (The full reverse Q8 implication).**

$$\forall W,G,B,\ \operatorname{FiniteDimensionalRealInnerProductSpace}\left(W\right) \land \operatorname{SubgroupOfUnitsEnd}\left(G, W\right) \land \operatorname{InnerProductSpaceCore}\left(R, W, B\right) \land \operatorname{finrank}\left(R, W\right)=3 \land \operatorname{range}\left(\operatorname{originalAction}\left(G\right)\right)=\operatorname{skewEndomorphisms}\left(B\right) \Rightarrow \exists A:\operatorname{Lie}\left(G\right),\ \exists x:W,\ A\neq0 \land x\neq0 \land \operatorname{A}\left(x\right)=0 \land \operatorname{FullReciprocity}\left(G, A, x\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/OriginalCompactReciprocity.fullReciprocity_of_full_skew` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the same original matrix subgroup G and its actual curve Lie algebra on the full W, assume W has dimension three and the range of the original inclusion equals all skew endomorphisms for a positive form B. Then there exist nonzero A in that actual Lie algebra and nonzero x in the same W with Ax=0 and both canonical projections of fullRelation G A x bijective. This is the reverse implication of the algebraic rigidity characterization. Compactness is not required again in this direction, since the hypotheses already identify the entire actual velocity range.

A B-orthonormal frame constructs the actual plane rotation T with T(b0)=b1, T(b1)=-b0, and T(b2)=0. Set x=b2 and obtain A from the full original range. The proof establishes ker(A)=R x and range(A)=x-perp. Every original velocity is B-skew, so evaluation at x has image in x-perp. For every y perpendicular to x the rank-two skew map v maps to B(x,v)y-B(y,v)x takes x to y; the full original range supplies its actual velocity. Thus the evaluation image is exactly the same x-perp. Faithfulness bounds the actual Lie algebra dimension by three, and rank-nullity then forces its evaluation kernel to be exactly R A.

Both projection proofs use every pair in the image of the full kernel Kx+Ay=0. For each projection, its zero fiber is trivial by the opposite kernel line. For either requested quotient class, the common image supplies a solution on the other side. These are separate injectivity and surjectivity arguments for the actual two canonical projections. No graph branch is chosen and no smaller representation or source orbit replaces W. This implication does not identify the full original group with SO or O and does not establish the operational probability frontend.

**Theorem 1.7 (The original component and both full-group alternatives).**

$$\forall W,G,\ \operatorname{FiniteDimensionalRealInnerProductSpace}\left(W\right) \land \operatorname{SubgroupOfUnitsEnd}\left(G, W\right) \land \operatorname{IsCompact}\left(G\right) \Rightarrow \forall A:\operatorname{Lie}\left(G\right),\ \forall x:W,\ A\neq0 \land x\neq0 \land \operatorname{A}\left(x\right)=0 \land \operatorname{FullReciprocity}\left(G, A, x\right) \Rightarrow \exists B:\operatorname{InnerProductSpaceCore}\left(R, W\right),\ (\forall h:G,\ \forall u,v:W,\ \operatorname{B}\left(\operatorname{h}\left(u\right), \operatorname{h}\left(v\right)\right)=\operatorname{B}\left(u, v\right)) \land \operatorname{finrank}\left(R, W\right)=3 \land \operatorname{finrank}\left(R, \operatorname{Lie}\left(G\right)\right)=3 \land \operatorname{range}\left(\operatorname{originalAction}\left(G\right)\right)=\operatorname{skewEndomorphisms}\left(B\right) \land \operatorname{Image}\left(\operatorname{subtype}\left(G\right), \operatorname{connectedComponent}\left(1, G\right)\right)=\operatorname{SO}\left(W, B\right) \land ((G=\operatorname{SO}\left(W, B\right)) \lor (G=\operatorname{O}\left(W, B\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/OriginalCompactReciprocity.original_group_rigidity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite-dimensional real inner product space W and actual compact subgroup G of the units of its continuous endomorphism algebra, take nonzero A in the actual curve Lie algebra and nonzero x in W with Ax=0 and FullReciprocity G A x. The theorem constructs the same positive invariant form B, both original dimensions three, and the full original skew range. The image of the intrinsic connected component of one in G under the actual subgroup inclusion is exactly the units preserving B with determinant one. The full original subgroup is either that entire special orthogonal group or the entire orthogonal group. All equalities are in the original ambient unit group, with its original operator norm and topology.

In the formula, O(W,B) denotes precisely the set of original units u satisfying B(u v,u w)=B(v,w) for all v,w in W, and SO(W,B) is its determinant-one subset. The notation does not replace the original action. The component is formed inside G before taking its inclusion image. The initially chosen norm need not be the norm induced by B. Linear maps built using a B-orthonormal frame are converted to continuous maps in the original norm by finite dimensionality.

The bridge is explicit. In any B-orthonormal three-frame, the unital real algebra R times C acts by a real scalar on the first axis and complex multiplication on the other two axes. Its generator (0,i) is an actual B-skew endomorphism. Continuity of the algebra homomorphism and Mathlib's map_exp transport exp(pi times (0,i))=(1,-1) to the actual operator algebra. Thus the line reflection fixing the first axis and negating its orthogonal plane is a skew exponential and belongs to the actual original component. For any nonzero axis, extend its normalized vector to an orthonormal frame. No continuous global choice of frames is required.

Apply Mathlib's LinearIsometryEquiv.reflections_generate_dim to each actual B-isometry. In its reflection word, a zero normal gives the identity and is handled separately. Each nonzero hyperplane reflection is minus its axis halfturn and has determinant minus one. Induction on the whole word constructs a product of halfturns whose underlying linear map, multiplied by the determinant of the word, is the original word. Determinant one removes that factor, placing every original B-isometry with determinant one in the image of the actual component. The earlier determinant restriction supplies the opposite inclusion. Individual hyperplane reflections and minus identity are never assumed to lie in G.

If every element of G has determinant one, the component equality gives G=SO(W,B). Otherwise choose an actual reversing element r of G. Every other reversing B-isometry u has u times inverse(r) in SO(W,B); multiplication by r therefore puts u in G. This proves G=O(W,B). The proof derives the full alternatives instead of assuming connectedness, exponential surjectivity, or a separate classification theorem.

This gives the global group conclusion of OMEGAQ-008 Theorem 5.1 on its original W, G and curve velocities. Operational preparations, probabilities, original effects, control menus and callable processes require their own construction from the original probability rows. The reverse entire-relation theorem in this document supplies the algebraic reverse Q8 direction.

**Theorem 1.8 (The original action fills the orthogonal Lie algebra).**

$$\forall W,G,\ \operatorname{FiniteDimensionalRealInnerProductSpace}\left(W\right) \land \operatorname{SubgroupOfUnitsEnd}\left(G, W\right) \land \operatorname{IsCompact}\left(G\right) \Rightarrow \forall A:\operatorname{Lie}\left(G\right),\ \forall x:W,\ A\neq0 \land x\neq0 \land \operatorname{A}\left(x\right)=0 \land \operatorname{FullReciprocity}\left(G, A, x\right) \Rightarrow \exists B:\operatorname{InnerProductSpaceCore}\left(R, W\right),\ (\forall h:G,\ \forall u,v:W,\ \operatorname{B}\left(\operatorname{h}\left(u\right), \operatorname{h}\left(v\right)\right)=\operatorname{B}\left(u, v\right)) \land \operatorname{finrank}\left(R, W\right)=3 \land \operatorname{finrank}\left(R, \operatorname{Lie}\left(G\right)\right)=3 \land \operatorname{range}\left(\operatorname{originalAction}\left(G\right)\right)=\operatorname{skewEndomorphisms}\left(B\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/OriginalCompactReciprocity.original_rigidity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under exactly the same compactness, nonzero-witness, annihilation and entire-relation hypotheses, there exists a positive form B invariant under the original G such that both original dimensions are three and the range of the actual inclusion of its curve Lie algebra into End(W) equals all B-skew endomorphisms of that same W. The inclusion is the original matrix action. Neither a supplied representation isomorphism nor a separately assumed dimension or centralizer is used.

The dimension theorem supplies the three-dimensional faithful range. For a positive form on a three-dimensional space, the three off-diagonal coefficients in an orthonormal basis determine a skew endomorphism: the diagonal coefficients vanish and skewness determines the remaining coefficients. This embeds the full skew subspace into three real coordinates, giving its dimension at most three. Every actual curve velocity is B-skew, so the faithful three-dimensional range is a subspace of that skew subspace with the same dimension and therefore equals it.

## References

- Truth anchor: `D5/S3/Quantum/Algebra/OriginalCompactReciprocity.curveLieAlgebra`
- Truth anchor: `D5/S3/Quantum/Algebra/OriginalCompactReciprocity.finrank_eq_three`
- Truth anchor: `D5/S3/Quantum/Algebra/OriginalCompactReciprocity.fullReciprocity_of_full_skew`
- Truth anchor: `D5/S3/Quantum/Algebra/OriginalCompactReciprocity.fullRelation`
- Truth anchor: `D5/S3/Quantum/Algebra/OriginalCompactReciprocity.mem_velocitySpace_iff_exp`
- Truth anchor: `D5/S3/Quantum/Algebra/OriginalCompactReciprocity.original_exponential_rigidity`
- Truth anchor: `D5/S3/Quantum/Algebra/OriginalCompactReciprocity.original_group_rigidity`
- Truth anchor: `D5/S3/Quantum/Algebra/OriginalCompactReciprocity.original_rigidity`
- Dependency: [D5/S3/Quantum/Algebra/OriginalCompactActionMetric](OriginalCompactActionMetric.md)
- Dependency: [D5/S3/Quantum/Algebra/RankOneInvariantMetric](RankOneInvariantMetric.md)
