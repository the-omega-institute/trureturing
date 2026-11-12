# Attained weighted mixed-state confirmation gap

## Abstract

Attained weighted mixed-state confirmation gap.

Use the same closed generating original cone, strictly positive unit, full normalized base, full pure set P and full proper interval. The entire finite P is bijectively indexed by L disjoint-union R disjoint-union Z. The normalized unique relation has strictly positive left weights alpha and right weights beta, each of total mass one. All Z vertices have zero relation coefficient and remain in the original carrier. The relation nullity is one; no extension from a selected subconfiguration is assumed.

**Definition 1.1 (The full pure coordinate map).**

Lean statement: `D5/S3/Quantum/Foundation/WeightedRelationConfirmation.coordinates`

*Formalization.* `D5/S3/Quantum/Foundation/WeightedRelationConfirmation.coordinates` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every real coefficient function w on all of P, Phi(w)=sum_p w(p)p. No subset of pure points replaces this domain.

**Definition 1.2 (Mixed-state zero gluing).**

Lean statement: `D5/S3/Quantum/Foundation/WeightedRelationConfirmation.zeroGluing`

*Formalization.* `D5/S3/Quantum/Foundation/WeightedRelationConfirmation.zeroGluing` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every original pure p and all x,y in the entire original base K, if an original proper confirmer of p vanishes at x and another original proper confirmer vanishes at y, there exists an original proper confirmer vanishing at (x+y)/2. The two antecedent witnesses may differ. Existence of an excluding effect, rather than only a zero infimum, is the definition.

**Theorem 1.3 (Surjectivity on the original carrier).**

Lean statement: `D5/S3/Quantum/Foundation/WeightedRelationConfirmation.coordinates_surjective`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/WeightedRelationConfirmation.coordinates_surjective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Closedness, strict positivity and generatingness imply that Phi is onto A. Compactness of the original base and pure spanning are derived from the existing cone lemmas.

**Theorem 1.4 (The entire original proper interval).**

Lean statement: `D5/S3/Quantum/Foundation/WeightedRelationConfirmation.full_effect_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/WeightedRelationConfirmation.full_effect_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every assignment v:P to R, there exists a unique original real linear effect f, proper on all of C and satisfying f(p)=v(p) at every original pure point, if and only if every v(p) belongs to [0,1] and sum_p w(p)v(p)=0 for every w in the entire kernel of Phi. Both the values and their complements extend nonnegatively to the entire original cone. Uniqueness follows from surjectivity of Phi.

**Theorem 1.5 (Relations have zero total coefficient).**

Lean statement: `D5/S3/Quantum/Foundation/WeightedRelationConfirmation.relation_sum_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/WeightedRelationConfirmation.relation_sum_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every full pure coefficient vector w with Phi(w)=0, sum_p w(p)=0. This follows by applying the same original unit, whose value is one on every pure point.

**Theorem 1.6 (A universal lower bound with attainment).**

Lean statement: `D5/S3/Quantum/Foundation/WeightedRelationConfirmation.attained_comparison`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/WeightedRelationConfirmation.attained_comparison` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every original cone vector x and reference p, if an original proper confirmer f of p satisfies f(x)<=g(x) for every original proper confirmer g of p, then T_p(x)=f(x). The proof uses the actual infimum defining the original comparison. No attainment assumption is made for unrelated minimization problems.

**Theorem 1.7 (No single extreme point on a relation side).**

Lean statement: `D5/S3/Quantum/Foundation/WeightedRelationConfirmation.no_single_positive`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/WeightedRelationConfirmation.no_single_positive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every full pure coefficient vector w with Phi(w)=0, if w(q)>0 and every other coefficient is nonpositive, there is a contradiction. The negative side expresses q as a convex combination of other original base points, contrary to its native extremality. The normalized gap theorem uses this to prove at least two vertices on both relation sides; the native one-relation obstruction uses it to construct actual alternate excluding effects.

**Definition 1.8 (A full signed relation).**

Lean statement: `D5/S3/Quantum/Foundation/WeightedRelationConfirmation.relationVector`

*Formalization.* `D5/S3/Quantum/Foundation/WeightedRelationConfirmation.relationVector` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

On the three disjoint label groups the coefficients are alpha(i), minus beta(j), and zero. In particular every zero-coefficient original pure vertex is retained.

**Theorem 1.9 (Bounded balanced assignments descend).**

Lean statement: `D5/S3/Quantum/Foundation/WeightedRelationConfirmation.relation_effect`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/WeightedRelationConfirmation.relation_effect` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any assignment v to every label in the full bijection, bounds 0<=v<=1 and equality of the alpha-weighted left and beta-weighted right readings imply existence of an original proper real linear effect realizing all those values. The premise that the displayed relation spans the entire kernel is used here; for the attained-gap theorem it is derived from original nullity one and the actual normalized vector relation.

**Definition 1.10 (The source weighted barycenter).**

Lean statement: `D5/S3/Quantum/Foundation/WeightedRelationConfirmation.barycenter`

*Formalization.* `D5/S3/Quantum/Foundation/WeightedRelationConfirmation.barycenter` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For any finite group J of original pure labels, barycenter is the sum of beta(j)b_j over J divided by its total beta mass. A group containing several vertices is retained as that mixed source barycenter.

**Definition 1.11 (The complete source gap).**

Lean statement: `D5/S3/Quantum/Foundation/WeightedRelationConfirmation.partitionGap`

*Formalization.* `D5/S3/Quantum/Foundation/WeightedRelationConfirmation.partitionGap` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For specified p and J this predicate states membership of both source weighted barycenters in the original base, comparison values zero at each, the exact positive midpoint value t/(2 max(b,1-b)), and actual original proper confirming effects attaining all three values.

**Definition 1.12 (Exchange only the relation sides).**

Lean statement: `D5/S3/Quantum/Foundation/WeightedRelationConfirmation.exchange`

*Formalization.* `D5/S3/Quantum/Foundation/WeightedRelationConfirmation.exchange` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The full pure-point indexing bijection exchanges its left and right nonzero groups and retains the same complete zero-coefficient group.

**Theorem 1.13 (Exact attained original values).**

Lean statement: `D5/S3/Quantum/Foundation/WeightedRelationConfirmation.weighted_gap_after_exchange`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/WeightedRelationConfirmation.weighted_gap_after_exchange` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Both nonzero relation sides have at least two original pure vertices. There exists a label whose positive weight is globally minimal among all alpha and beta weights. If it is a right label, the theorem exchanges the two sides and retains every free vertex. Orient that label as the left p and put t equal to its weight. For every J with J and its complement in the entire right label set both nonempty, put b=sum over J of beta, x=barycenter(J), and y=barycenter(complement J). Then x and y belong to the original K, T_p(x)=T_p(y)=0, and T_p((x+y)/2)=t/(2 max(b,1-b))>0. The theorem also supplies original confirming proper effects attaining each of these three values. All quantifiers retain arbitrary positive weights, arbitrary such J and arbitrary finite Z, including empty Z. Both constructed effects have value one at p, zero at every other left vertex and at every free vertex. On J and its complement, f_x has readings 0 and t/(1-b), while f_y has t/b and 0; thus f_x excludes x and f_y excludes y. Every confirmer has nonnegative weighted column masses whose sum is at least t. Dividing these masses by 2b and 2(1-b) gives the universal bound t/(2 max(b,1-b)). When b>=1-b, f_y attains it; when b<=1-b, f_x attains it, and both attain it at equality.

## References

- Truth anchor: `D5/S3/Quantum/Foundation/WeightedRelationConfirmation.attained_comparison`
- Truth anchor: `D5/S3/Quantum/Foundation/WeightedRelationConfirmation.barycenter`
- Truth anchor: `D5/S3/Quantum/Foundation/WeightedRelationConfirmation.coordinates`
- Truth anchor: `D5/S3/Quantum/Foundation/WeightedRelationConfirmation.coordinates_surjective`
- Truth anchor: `D5/S3/Quantum/Foundation/WeightedRelationConfirmation.exchange`
- Truth anchor: `D5/S3/Quantum/Foundation/WeightedRelationConfirmation.full_effect_iff`
- Truth anchor: `D5/S3/Quantum/Foundation/WeightedRelationConfirmation.no_single_positive`
- Truth anchor: `D5/S3/Quantum/Foundation/WeightedRelationConfirmation.partitionGap`
- Truth anchor: `D5/S3/Quantum/Foundation/WeightedRelationConfirmation.relationVector`
- Truth anchor: `D5/S3/Quantum/Foundation/WeightedRelationConfirmation.relation_effect`
- Truth anchor: `D5/S3/Quantum/Foundation/WeightedRelationConfirmation.relation_sum_zero`
- Truth anchor: `D5/S3/Quantum/Foundation/WeightedRelationConfirmation.weighted_gap_after_exchange`
- Truth anchor: `D5/S3/Quantum/Foundation/WeightedRelationConfirmation.zeroGluing`
- Dependency: [D5/S3/Quantum/Foundation/CircuitBalancedConfirmation](CircuitBalancedConfirmation.md)
