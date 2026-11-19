# Exact relative criterion for three tensor factors

## Abstract

A complete high-digit criterion for the literal three-factor decomposition in the original relative category.

Let K be any field of prime characteristic p, E a finite additive commutative group in an independent universe, and alpha:E->K an injective additive map. Write q=card E and V_d for the ordinary polynomial contragredient of dimension d, restricted along alpha. The relative generator M is the existing literal sum V_p direct-sum V_(2p) direct-sum ... direct-sum V_q. Relative projectivity means an actual equivariant retract of X tensor M; the original witnesses P and X may have arbitrary dimension.

Put i=pa+u, j=pb+v, k=pc+w. Assume 1<=u,v,w, u+v+w<=p+1 and i+j+k<=q+1. The individual bounds u,v,w<p follow from these assumptions. The target T is the actual ((V_i tensor V_j) tensor V_k). The proposed S3 is the literal dependent direct sum over ell:Fin(min u v) and h:Fin(min(u+v-2ell-1,w)), with summand V_(i+j+k-2ell-2h-2). This formulation specifies all summands and their ranges; it does not replace S3 by its highest summand.

**Theorem 1.1 (The top term is an actual equivariant retract).**

Lean statement: `D5/S3/FiniteGroups/GroupAlgebra/EmbeddedTripleTensorCriterion.topProjection_inclusion`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/GroupAlgebra/EmbeddedTripleTensorCriterion.topProjection_inclusion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive u,v,w, the index ell=h=0 exists. The actual direct-sum inclusion of V_(i+j+k-2), followed by the actual component projection, is its identity after restriction along alpha. No retract is assumed in the criterion.

**Theorem 1.2 (Separate the low-degree factors from the high digits).**

Lean statement: `D5/S3/FiniteGroups/GroupAlgebra/EmbeddedTripleTensorCriterion.degree_binomial_product`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/GroupAlgebra/EmbeddedTripleTensorCriterion.degree_binomial_product` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Lucas factorization expresses choose(i+j-2,i-1) times choose(i+j+k-3,i+j-2) as the product of choose(u+v-2,u-1), choose(u+v+w-3,u+v-2), choose(a+b,a) and choose(a+b+c,a+b), all cast into K. The positive-residue and sum assumptions justify every natural subtraction and keep the low degrees below p.

**Theorem 1.3 (The top identity has nonzero trace).**

Lean statement: `D5/S3/FiniteGroups/GroupAlgebra/EmbeddedTripleTensorCriterion.top_dimension_ne_zero`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/GroupAlgebra/EmbeddedTripleTensorCriterion.top_dimension_ne_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The top dimension i+j+k-2 is p(a+b+c)+(u+v+w-2). Its final term lies between 1 and p-1, so its cast into K is nonzero. This is precisely the nonzero identity trace required by the obstruction argument, rather than a division by a tensor-factor dimension.

**Theorem 1.4 (Use the all-map obstruction in positive module dimensions).**

Lean statement: `D5/S3/FiniteGroups/GroupAlgebra/EmbeddedTripleTensorCriterion.trace_zero_of_degree_product_zero`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/GroupAlgebra/EmbeddedTripleTensorCriterion.trace_zero_of_degree_product_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive i,j,k with i+j+k<=q+1, vanishing of the degree-binomial product forces trace(g composed with f)=0 for every equivariant f:V_(i+j+k-2)->T and g:T->V_(i+j+k-2). Replacing i,j,k by n+1,m+1,r+1 translates the exact size bound to the previously proved all-map triple obstruction.

**Theorem 1.5 (Original relative stability forces the high product to be nonzero).**

Lean statement: `D5/S3/FiniteGroups/GroupAlgebra/EmbeddedTripleTensorCriterion.original_relative_necessary_for_embedding`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/GroupAlgebra/EmbeddedTripleTensorCriterion.original_relative_necessary_for_embedding` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Suppose S3 and T are relatively stably isomorphic for the original M. Compose the stable maps with the actual top inclusion and projection. Their inverse error still factors through the same original relatively projective witness. Its trace is zero by the existing relative trace theorem. If choose(a+b,a) times choose(a+b+c,a+b) were zero, the all-map obstruction would make the composite trace zero too, contradicting the nonzero identity trace. Nontriviality of E is derived from the size and positive-index assumptions.

**Theorem 1.6 (Construct the full decomposition and its projective complement).**

Lean statement: `D5/S3/FiniteGroups/GroupAlgebra/EmbeddedTripleTensorCriterion.triple_decomposition`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/GroupAlgebra/EmbeddedTripleTensorCriterion.triple_decomposition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Before restriction, take a natural s with a+b<=s and c<=s. If the high-binomial product is nonzero, the actual translation representation T is equivariantly isomorphic to S3 times an actual relatively projective P for the generator with s p-multiple summands. The proof first decomposes V_i tensor V_j. Its ell-th retained dimension is p(a+b)+(u+v-2ell-1). Tensor each such summand with V_k, apply the second binary decomposition and flatten the resulting dependent direct sum to the specified TripleIndex.

The complement is the direct sum of the second-step remainders, together with the first-step remainder tensored with V_k. Its relative projectivity is proved using actual direct-sum and tensor retracts, associativity and the tensor symmetry. The auxiliary witnesses are not replaced by a trace-radical assertion and are not assumed finite-dimensional.

**Theorem 1.7 (Descend the constructive decomposition to the original relative category).**

Lean statement: `D5/S3/FiniteGroups/GroupAlgebra/EmbeddedTripleTensorCriterion.original_relative_sufficient_for_embedding`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/GroupAlgebra/EmbeddedTripleTensorCriterion.original_relative_sufficient_for_embedding` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The embedding and characteristic give p times (q/p)=q. The total-index bound implies a+b+c<=q/p, supplying the bounds for the actual decomposition. Its projective complement gives stable inverse maps, and restricting those maps along alpha preserves both inverse errors with their original projective and tensor witnesses. Thus nonvanishing of the high product is sufficient without any additional bound or finite-field hypothesis.

**Theorem 1.8 (The complete literal three-factor criterion).**

Lean statement: `D5/S3/FiniteGroups/GroupAlgebra/EmbeddedTripleTensorCriterion.original_relative_iff_for_embedding`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/GroupAlgebra/EmbeddedTripleTensorCriterion.original_relative_iff_for_embedding` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under exactly the displayed assumptions, S3 ~_M T if and only if choose(a+b,a) times choose(a+b+c,a+b) is nonzero in K. Necessity concerns every pair of equivariant stable inverse maps; sufficiency constructs a real decomposition with a relatively projective complement. No decomposition, factorization or top-summand retract is a hypothesis.

Two transient exact applications check different outcomes. In characteristic three over F27, a=b=c=u=v=w=1 gives i=j=k=4: the first high factor is 2 but the second is 3=0, so the literal S3 is not relatively stably isomorphic to T. Over F49 of characteristic seven, a=b=c=1 and u=v=w=2 give i=j=k=9 and a literal S3 with three terms; the high product is 6, and the complete iff gives an actual original-relative stable equivalence. These applications are compiled checks, not additional named library theorems.

The external research anchor is the binary Conjecture 3.7 of Jonathan Elmer and Kazal Kadr, Some formulae relating modular representations of elementary abelian p-groups, DOI 10.1007/s13366-026-00855-9. The present theorem is a three-factor extension of the corrected binary analysis; the paper does not state this triple criterion as its open conjecture. It concerns the explicit polynomial models along alpha, not an additional theorem transporting the triple to an arbitrary faithful W. No worldwide novelty or priority claim is made. The trace-ideal mechanism is classical, while the construction keeps the paper's original relative factorization ideal throughout.

## References

- Truth anchor: `D5/S3/FiniteGroups/GroupAlgebra/EmbeddedTripleTensorCriterion.degree_binomial_product`
- Truth anchor: `D5/S3/FiniteGroups/GroupAlgebra/EmbeddedTripleTensorCriterion.original_relative_iff_for_embedding`
- Truth anchor: `D5/S3/FiniteGroups/GroupAlgebra/EmbeddedTripleTensorCriterion.original_relative_necessary_for_embedding`
- Truth anchor: `D5/S3/FiniteGroups/GroupAlgebra/EmbeddedTripleTensorCriterion.original_relative_sufficient_for_embedding`
- Truth anchor: `D5/S3/FiniteGroups/GroupAlgebra/EmbeddedTripleTensorCriterion.topProjection_inclusion`
- Truth anchor: `D5/S3/FiniteGroups/GroupAlgebra/EmbeddedTripleTensorCriterion.top_dimension_ne_zero`
- Truth anchor: `D5/S3/FiniteGroups/GroupAlgebra/EmbeddedTripleTensorCriterion.trace_zero_of_degree_product_zero`
- Truth anchor: `D5/S3/FiniteGroups/GroupAlgebra/EmbeddedTripleTensorCriterion.triple_decomposition`
- Dependency: [D5/S3/FiniteGroups/GroupAlgebra/ElmerKadrTensorReflection](ElmerKadrTensorReflection.md)
- Dependency: [D5/S3/FiniteGroups/GroupAlgebra/EmbeddedTripleTensorObstruction](EmbeddedTripleTensorObstruction.md)
