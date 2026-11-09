# Integral weight splitting for finite native matroids

## Abstract

Finite native matroids with a common base admit integral weight splitting with one base globally optimal for both summands.

**Definition 1.1 (Actual integral set weight).**

$$\forall (E: Type_{u}), ([\operatorname{Finite}\left(E\right)], \forall (q: E \to \mathbb{Z}), (\forall (B: \operatorname{Set}\left(E\right)), (\operatorname{weightSum}\left(q, B\right) = \sum_{{e \in \operatorname{toFinite}.\operatorname{toFinset}\left(B\right)}} \operatorname{q}\left(e\right))))$$

*Formalization.* `D5/S3/Combinatorics/Matroids/IntegralWeightSplitting.weightSum` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The sum is over the actual finite set B, using B.toFinite.toFinset. Weights are integers and may be negative, zero or tied.

**Definition 1.2 (Tagged legal native exchanges).**

$$\forall (E: Type_{u}), ([\operatorname{Finite}\left(E\right)], \forall (M1: \operatorname{Matroid}\left(E\right)), (\forall (M2: \operatorname{Matroid}\left(E\right)), (\forall (B: \operatorname{Set}\left(E\right)), (\operatorname{ExchangeArc}\left(M1, M2, B\right) = \{(t, (b, e)) \in \operatorname{Bool}\left(\right) \times E \times E \mid (b \in B) \land ((e \in M1.E \setminus B) \land (\operatorname{Matroid}.\operatorname{IsBase}\left(\operatorname{if} t = true \operatorname{then} M1 \operatorname{else} M2, \operatorname{insert}\left(e, B \setminus \{b\}\right)\right)))\}))))$$

*Formalization.* `D5/S3/Combinatorics/Matroids/IntegralWeightSplitting.ExchangeArc` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An arc stores a tag t and elements b,e. It requires b in B, e in M1.E outside B, and insert e (B minus {b}) to be a base of M1 when t is true and of M2 when t is false. Under equal grounds this is exactly the two native exchange relations.

**Definition 1.3 (The oriented tagged exchange graph).**

$$\forall (E: Type_{u}), ([\operatorname{Finite}\left(E\right)], \forall (M1: \operatorname{Matroid}\left(E\right)), (\forall (M2: \operatorname{Matroid}\left(E\right)), (\forall (B: \operatorname{Set}\left(E\right)), (\forall (a: \operatorname{ExchangeArc}\left(M1, M2, B\right)), ((\operatorname{source}\left(\operatorname{exchangeGraph}\left(M1, M2, B\right), a\right) = \operatorname{if} a.val.1 = true \operatorname{then} a.val.2.1 \operatorname{else} a.val.2.2) \land (\operatorname{target}\left(\operatorname{exchangeGraph}\left(M1, M2, B\right), a\right) = \operatorname{if} a.val.1 = true \operatorname{then} a.val.2.2 \operatorname{else} a.val.2.1))))))$$

*Formalization.* `D5/S3/Combinatorics/Matroids/IntegralWeightSplitting.exchangeGraph` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a true tag the source is b and the target is e; for a false tag the source is e and the target is b. Tags distinguish the two legal exchange types even when both occur for the same pair.

**Definition 1.4 (Asymmetric integral arc weights).**

$$\forall (E: Type_{u}), ([\operatorname{Finite}\left(E\right)], \forall (M1: \operatorname{Matroid}\left(E\right)), (\forall (M2: \operatorname{Matroid}\left(E\right)), (\forall (B: \operatorname{Set}\left(E\right)), (\forall (w: E \to \mathbb{Z}), (\forall (a: \operatorname{ExchangeArc}\left(M1, M2, B\right)), (\operatorname{exchangeWeight}\left(M1, M2, B, w, a\right) = \operatorname{if} a.val.1 = true \operatorname{then} 0 \operatorname{else} \operatorname{w}\left(a.val.2.1\right) - \operatorname{w}\left(a.val.2.2\right)))))))$$

*Formalization.* `D5/S3/Combinatorics/Matroids/IntegralWeightSplitting.exchangeWeight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

First-matroid arcs have weight zero. Second-matroid arcs have weight w(b)-w(e). Walk weight is the sum along the entire edge list, counting repeated edges and vertices with multiplicity.

**Theorem 1.5 (Exchange inequalities imply global base optimality).**

$$\forall (E: Type_{u}), ([\operatorname{Finite}\left(E\right)], \forall (M: \operatorname{Matroid}\left(E\right)), (\forall (q: E \to \mathbb{Z}), (\forall (B: \operatorname{Set}\left(E\right)), ((\operatorname{Matroid}.\operatorname{IsBase}\left(M, B\right)) \Rightarrow ((\forall (b: E), ((b \in B) \Rightarrow (\forall (e: E), ((e \in M.E \setminus B) \Rightarrow ((\operatorname{Matroid}.\operatorname{IsBase}\left(M, \operatorname{insert}\left(e, B \setminus \{b\}\right)\right)) \Rightarrow (\operatorname{q}\left(b\right) \le \operatorname{q}\left(e\right))))))) \Rightarrow (\forall (C: \operatorname{Set}\left(E\right)), ((\operatorname{Matroid}.\operatorname{IsBase}\left(M, C\right)) \Rightarrow (\operatorname{weightSum}\left(q, B\right) \le \operatorname{weightSum}\left(q, C\right)))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/IntegralWeightSplitting.exchange_local_is_global_minimum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any native finite matroid and any integral q, if a base B satisfies q(b)<=q(e) for every legal exchange with b in B and e in M.E outside B, then B has no larger actual q-sum than any base C. The proof establishes that B intersects every real lower threshold in a basis of that threshold and applies native_weighted_base_rank_saturation. An unsaturated threshold would admit an exchange removing b outside the threshold and inserting e inside it, contradicting the assumed exchange inequality.

**Theorem 1.6 (Common-base minimality excludes every positive closed walk).**

$$\forall (E: Type_{u}), ([\operatorname{Finite}\left(E\right)], \forall (M1: \operatorname{Matroid}\left(E\right)), (\forall (M2: \operatorname{Matroid}\left(E\right)), ((M1.E = M2.E) \Rightarrow (\forall (w: E \to \mathbb{Z}), (\forall (B: \operatorname{Set}\left(E\right)), ((\operatorname{Matroid}.\operatorname{IsBase}\left(M1, B\right)) \Rightarrow ((\operatorname{Matroid}.\operatorname{IsBase}\left(M2, B\right)) \Rightarrow ((\forall (C: \operatorname{Set}\left(E\right)), ((\operatorname{Matroid}.\operatorname{IsBase}\left(M1, C\right)) \Rightarrow ((\operatorname{Matroid}.\operatorname{IsBase}\left(M2, C\right)) \Rightarrow (\operatorname{weightSum}\left(w, B\right) \le \operatorname{weightSum}\left(w, C\right))))) \Rightarrow (\forall (s: E), (\forall (p: \operatorname{EdgeGraph}.\operatorname{Walk}\left(\operatorname{exchangeGraph}\left(M1, M2, B\right), s, s\right)), (\operatorname{MaxPlusPotential}.\operatorname{walkWeight}\left(\operatorname{exchangeWeight}\left(M1, M2, B, w\right), p\right) \le 0)))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/IntegralWeightSplitting.optimal_common_base_closedWalk_nonpos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let B be a common base minimizing the actual integral w-sum among all common bases. Every finite closed walk in the exact tagged exchange graph has nonpositive weight. This includes empty walks and walks with repetitions. The proof does not require toggling a cycle to preserve independence. For each tag, average the incidence vectors of its legal exchange bases, using B on edges carrying the other tag, and include one additional copy of B. The closed-walk balance identity makes the two averages identical. This common vector satisfies both native rank-inequality systems and has total coordinate sum equal to the base rank. Its w-cost is w(B) minus the walk weight divided by the edge-list length plus one. The maximum-cardinality face and its minimum-cost exposed face are compact; Krein-Milman supplies an extreme point. The existing intersection-polytope zero-one theorem applies after replacing each M by M restricted upward to univ, which preserves all ranks and adds only loops outside the native ground. The zero-one point has the same cardinality as B and yields an actual common base of no greater cost. Minimality of B therefore forces the walk weight to be nonpositive.

**Theorem 1.7 (Full integral common-base splitting).**

$$\forall (E: Type_{u}), ([\operatorname{Finite}\left(E\right)], \forall (M1: \operatorname{Matroid}\left(E\right)), (\forall (M2: \operatorname{Matroid}\left(E\right)), ((M1.E = M2.E) \Rightarrow ((\exists (B: \operatorname{Set}\left(E\right)), ((\operatorname{Matroid}.\operatorname{IsBase}\left(M1, B\right)) \land (\operatorname{Matroid}.\operatorname{IsBase}\left(M2, B\right)))) \Rightarrow (\forall (w: E \to \mathbb{Z}), (\exists (B: \operatorname{Set}\left(E\right)), (\exists (c: E \to \mathbb{Z}), (\exists (d: E \to \mathbb{Z}), ((\operatorname{Matroid}.\operatorname{IsBase}\left(M1, B\right)) \land ((\operatorname{Matroid}.\operatorname{IsBase}\left(M2, B\right)) \land ((\forall (e: E), (\operatorname{c}\left(e\right) + \operatorname{d}\left(e\right) = \operatorname{w}\left(e\right))) \land ((\forall (C: \operatorname{Set}\left(E\right)), ((\operatorname{Matroid}.\operatorname{IsBase}\left(M1, C\right)) \Rightarrow (\operatorname{weightSum}\left(c, B\right) \le \operatorname{weightSum}\left(c, C\right)))) \land (\forall (D: \operatorname{Set}\left(E\right)), ((\operatorname{Matroid}.\operatorname{IsBase}\left(M2, D\right)) \Rightarrow (\operatorname{weightSum}\left(d, B\right) \le \operatorname{weightSum}\left(d, D\right))))))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/IntegralWeightSplitting.finite_integral_weight_splitting` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every universe u, finite carrier E, native matroids M1 and M2 with equal grounds and at least one common base, and integer weight w, there are a set B and integer functions c,d on all of E. The same B is a base of both matroids, c(e)+d(e)=w(e) for every carrier element, and B minimizes c among every M1-base and d among every M2-base. A minimum-w common base is selected internally from the finite nonempty family of all common bases. Closed-walk nonpositivity supplies an integer potential phi through Maths.MaxPlusPotential.exists_isPotential_iff_forall_closedWalk_nonpos. Set c=phi and d=w-phi. The first arc inequality is c(b)<=c(e), while the second is phi(e)+w(b)-w(e)<=phi(b), equivalently d(b)<=d(e). Apply the local-to-global theorem twice. The split equality is pointwise on E, including elements outside the shared native ground.

The theorem includes empty carriers, empty and proper grounds, empty common bases, rank zero, loops, coloops, nonrepresentable matroids, and tied, negative, zero or arbitrary integral weights whenever the common-base premise holds. It assumes no optimum, splitting, dual prices, representation, algorithm or rank-profile certificate, and makes no algorithmic or complexity claim.

This is a formalization of a published theorem. Frank, A Weighted Matroid Intersection Algorithm, Journal of Algorithms 2 (1981), 328-336, gives integral splitting for fixed-cardinality common independent sets (https://www.cs.elte.hu/~frank/cikkek/FrankJ6.PDF). Frank, Connections in Combinatorial Optimization, author-posted corrected OUP proof, Theorem 13.2.4 and Corollary 13.2.6, pp. 424-425, explicitly treat common bases (https://www.cs.elte.hu/~frank/cikkek/FrankB1.pdf). Those sources use maximum weights; negating weights gives the minimum convention here. The proof above uses the repository's existing primal intersection-polytope integrality and integer-potential suppliers. It is not an originality or open-problem-resolution claim, and does not assert a solution of the separate full joint-exchange event.

## References

- Truth anchor: `D5/S3/Combinatorics/Matroids/IntegralWeightSplitting.ExchangeArc`
- Truth anchor: `D5/S3/Combinatorics/Matroids/IntegralWeightSplitting.exchangeGraph`
- Truth anchor: `D5/S3/Combinatorics/Matroids/IntegralWeightSplitting.exchangeWeight`
- Truth anchor: `D5/S3/Combinatorics/Matroids/IntegralWeightSplitting.exchange_local_is_global_minimum`
- Truth anchor: `D5/S3/Combinatorics/Matroids/IntegralWeightSplitting.finite_integral_weight_splitting`
- Truth anchor: `D5/S3/Combinatorics/Matroids/IntegralWeightSplitting.optimal_common_base_closedWalk_nonpos`
- Truth anchor: `D5/S3/Combinatorics/Matroids/IntegralWeightSplitting.weightSum`
- Dependency: [D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierDual](../Graph/LayeredCirculation/SupplierDual.md)
- Dependency: [D5/S3/Combinatorics/Matroids/FiniteIntersectionPolytope](FiniteIntersectionPolytope.md)
- Dependency: [D5/S3/Combinatorics/Matroids/NativeWeightedBaseRankSaturation](NativeWeightedBaseRankSaturation.md)
