# Whole-base facet injection from original mixed-state zero gluing

## Abstract

Whole-base facet injection from original mixed-state zero gluing.

**Theorem 1.1 (exclusion symmetric).**

Lean statement: `D5/S3/Quantum/Foundation/FacetZeroGluing.exclusion_symmetric`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/FacetZeroGluing.exclusion_symmetric` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any original pure p,q, q belongs to the entire D_p if and only if p belongs to the entire D_q. The original proof uses the same proper effect and its complement u-f. OrthogonalJointCompletion.pair_geometry and complete_pair consume this symmetry.

The source is Quantum Origin: Finite Pure Point and Facet Obstructions VII, Theorem 96.2, with the entire original carrier and definitions from VI 89.1 and V 88.1–88.3. This is distinct from VI Chapter 96. The real finite dimensional normed carrier, original cone and strictly positive linear unit determine the entire normalized base, all its extreme points and all original proper effects. Finiteness applies to that complete extreme-point set. No ball, antipodal separation, reciprocal comparison, least effect, selfdual pairing or supplied exposure is assumed.

**Definition 1.2 (All original mixed-state exclusions).**

Lean statement: `D5/S3/Quantum/Foundation/FacetZeroGluing.exclusion`

*Formalization.* `D5/S3/Quantum/Foundation/FacetZeroGluing.exclusion` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For the original p, the exclusion set consists exactly of normalized original x for which some linear functional f is proper on every vector of the entire original cone, has f(p)=1 and f(x)=0. The confirming and zero readings belong to the same effect. The zeroGluing premise is the original full mixed-state midpoint condition owned by WeightedRelationConfirmation.

**Definition 1.3 (Native facets of the whole base).**

Lean statement: `D5/S3/Quantum/Foundation/FacetZeroGluing.facets`

*Formalization.* `D5/S3/Quantum/Foundation/FacetZeroGluing.facets` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A facet is a native PointedCone.Face of the entire original cone whose real linear span has codimension one in the original carrier. Its whole normalized slice uses the original unit. The main theorem proves affdim(K)+1=dim(V). For every nonzero native face, membership in this facet type is equivalent to its normalized slice having affine dimension dim(V)-2. Each facet slice is convex and a native extreme subset of the whole original base. Thus for m=dim(V)-1 its slice has exactly dimension m-1, with the converse dimension criterion included. The theorem assumes dim(V)>=2, exactly the source branch m>=1; the single-point m=0 branch is excluded from facet selection.

**Definition 1.4 (Every actual facet of the whole normalized base).**

Lean statement: `D5/S3/Quantum/Foundation/FacetZeroGluing.baseFacets`

*Formalization.* `D5/S3/Quantum/Foundation/FacetZeroGluing.baseFacets` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This type ranges over every nonempty subset of the entire original base that is convex, is extreme in Mathlib's native sense and has affine dimension dim(V)-2. These are exactly the actual source facets when m=dim(V)-1>=1. Neither exclusion equality nor exposure is part of the definition. The main proof lifts every such face to a native cone face and recovers precisely the same normalized slice. It proves the nonincidence, any-choice injection, cardinal bound and symmetric cross incidence directly for this complete base-facet type.

**Theorem 1.5 (One original effect for the entire exclusion set).**

Lean statement: `D5/S3/Quantum/Foundation/FacetZeroGluing.zero_gluing_common_effect`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/FacetZeroGluing.zero_gluing_common_effect` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On any original finite dimensional carrier, original mixed-state Z0 and nonemptiness of D_p imply existence of one original proper confirmer f with D_p equal to the normalized base intersected with ker(f). This requires neither finite pure points nor a least confirmer. A finite spanning subset of D_p is chosen using Mathlib. Repeated mixed-state midpoints construct a point whose zero reading forces every chosen reading to vanish, by nonnegativity. Applying Z0 along this construction supplies a confirmer vanishing on the spanning subset and hence on all of D_p. The reverse containment uses that very confirmer as the original exclusion witness. This is the common-exposure predecessor from V 88.3, derived without compactness or an exposure input.

**Theorem 1.6 (All actual whole-base facets inject into original pure points).**

Lean statement: `D5/S3/Quantum/Foundation/FacetZeroGluing.whole_facet_injection`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/FacetZeroGluing.whole_facet_injection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume the original cone is closed and generating, its unit is strictly positive away from zero, all original pure points form a finite set, dim(V)>=2, and the original mixed-state Z0 holds. Every actual base facet S has an original pure p with D_p=S and p outside S. Any function choosing such a p for every actual facet is injective. The complete actual base-facet type has cardinality at most the complete original pure type; this bound is also an unconditional conjunct of the theorem. The same statements also hold in the native cone-face representation. For every pair F,G, the chosen p_G lies in F if and only if the chosen p_F lies in G. No global surjection or polarity of the face lattice follows.

The support construction uses the native cone-face property to prove C intersect span(F)=F. A nonzero functional annihilating the codimension-one span is oriented using an original cone vector. A negative reading at another cone vector would yield a positive conic combination in F, forcing the first vector into F and contradicting its positive reading. Maximization ranges over all original pure points, and the normalized support is extended to every original cone vector by the existing cone_bound theorem. The common zero effect has the same codimension-one kernel. For the reverse face correspondence, the positive conic hull of an arbitrary convex extreme base face is enlarged by zero. Normalizing a sum of two nonzero original cone vectors gives an open convex combination of their normalized vectors, so extremeness forces each summand into that cone face. Normalization recovers the original face exactly. Equality of exclusion sets identifies equal choices with equal actual base faces. Complements u-f establish the cross-incidence symmetry, without assuming reciprocity at nonzero comparison values.

The finite-pure coordinate and cone infrastructure integrated from the pinned WeightedRelationConfirmation dependency is prior work. The new mathematical construction is the universal finite zero-test induction, its whole-exclusion consequence and the native facet support and kernel argument. The dimension and whole-face clauses are mathematical consequences within the stated original model. They supply no preparation program, physical effect supplier, new cone classification or physical-source bridge. VII 96.3–96.5 remain outside this result; literature priority is not asserted.

## References

- Truth anchor: `D5/S3/Quantum/Foundation/FacetZeroGluing.baseFacets`
- Truth anchor: `D5/S3/Quantum/Foundation/FacetZeroGluing.exclusion`
- Truth anchor: `D5/S3/Quantum/Foundation/FacetZeroGluing.exclusion_symmetric`
- Truth anchor: `D5/S3/Quantum/Foundation/FacetZeroGluing.facets`
- Truth anchor: `D5/S3/Quantum/Foundation/FacetZeroGluing.whole_facet_injection`
- Truth anchor: `D5/S3/Quantum/Foundation/FacetZeroGluing.zero_gluing_common_effect`
- Dependency: [D5/S3/Quantum/Foundation/WeightedRelationConfirmation](WeightedRelationConfirmation.md)
