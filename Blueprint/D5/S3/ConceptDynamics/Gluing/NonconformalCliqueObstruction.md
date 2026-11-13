# Nonconformal Clique Obstruction

## Abstract

Every finite nonconformal clique yields finite nonempty relations whose complete pairwise projections agree, although no global tuple realizes them.

E is an arbitrary scope index type, V is a finite variable type, S(e) is a subset of V, and C is a finite subset of V with at least three elements. Every pair of distinct variables in C occurs together in some scope, but no scope contains C. Put q = card(C) - 1. An assignment on a scope U is a function from the subtype U to Fin(q). Empty, repeated, and nested scopes, variables outside C, and variables outside all scopes are allowed.

**Definition 1.1 (Only clique coordinates are constrained).**

$$\forall V: Type, \forall C: \operatorname{Finset}(V), \forall U: \operatorname{Set}(V), \forall q: \mathbb{N}, \forall r: U \to \operatorname{Fin}(q), \operatorname{InjectiveOnClique}(C, U, q, r) \iff \operatorname{Injective}(\operatorname{restrict}(r, \operatorname{intersection}(U, C)))$$

*Formalization.* `D5/S3/ConceptDynamics/Gluing/NonconformalCliqueObstruction.InjectiveOnClique` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The predicate requires injectivity of the scope tuple restricted to U intersect C. It imposes no condition on any coordinate outside C.

**Definition 1.2 (The full finite relation).**

$$\forall V: Type, [\operatorname{Finite}(V)], \forall C: \operatorname{Finset}(V), \forall U: \operatorname{Set}(V), \forall q: \mathbb{N}, \operatorname{cliqueRows}(C, U, q) = \operatorname{toFinset}(\{r: U \to \operatorname{Fin}(q) \mid \operatorname{InjectiveOnClique}(C, U, q, r)\})$$

*Formalization.* `D5/S3/ConceptDynamics/Gluing/NonconformalCliqueObstruction.cliqueRows` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The defining set is converted to a finset using finiteness of V and Fin(q). Every tuple satisfying the injectivity condition is included; values outside C are unrestricted.

**Theorem 1.3 (Complete pairwise consistency without a global tuple).**

$$\forall E: Type, \forall V: Type, [\operatorname{Finite}(V)], \forall S: E \to \operatorname{Set}(V), \forall C: \operatorname{Finset}(V), \begin{gathered}(3 \leq \operatorname{card}(C) \land (\forall x: V, x \in C \to \forall y: V, y \in C \to x \neq y \to \exists e: E, x \in \operatorname{S}(e) \land y \in \operatorname{S}(e)) \land (\forall e: E, \neg (\operatorname{coe}(C) \subseteq \operatorname{S}(e)))) \to \\{}\exists R: (e: E) \to \operatorname{Finset}(\operatorname{S}(e) \to \operatorname{Fin}(\operatorname{card}(C) - 1)),\\{}(\forall e: E, \operatorname{Nonempty}(\operatorname{R}(e))) \land \\{}(\forall e: E, \forall f: E, \operatorname{image}(\operatorname{restrict}(\operatorname{intersection}(\operatorname{S}(e), \operatorname{S}(f))), \operatorname{R}(e)) = \operatorname{image}(\operatorname{restrict}(\operatorname{intersection}(\operatorname{S}(e), \operatorname{S}(f))), \operatorname{R}(f))) \land \\{}(\neg \exists g: V \to \operatorname{Fin}(\operatorname{card}(C) - 1), \forall e: E, \operatorname{restrict}(g, \operatorname{S}(e)) \in \operatorname{R}(e))\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Gluing/NonconformalCliqueObstruction.nonconformal_clique_obstruction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each scope choose the relation R(e) = cliqueRows(C,S(e),q). Noncontainment gives a clique variable missing from S(e), so card(S(e) intersect C) is at most q. The upstream embedding theorem Function.Embedding.nonempty_of_card_le supplies a finite injection into Fin(q), yielding a local tuple.

For an arbitrary admissible tuple on S(e), start with such an injection on S(f) intersect C. Equiv.Perm.exists_extending_pair permutes its colors to agree with all prescribed values on S(e) intersect S(f) intersect C. On overlap coordinates outside C copy the original tuple exactly; choose a default color only on remaining coordinates outside C. This constructs a tuple in R(f) with the same complete overlap restriction. Applying the construction in both directions proves equality of the complete projection images.

If a global tuple restricted into every R(e), any distinct x,y in C would occur together in some scope and hence have different values. Thus the global tuple would inject C into Fin(card(C)-1), contrary to Fintype.card_le_of_injective.

For this specific relation construction the color threshold is sharp: with card(C) colors, inject C into Fin(card(C)) and extend the assignment to V using a default color outside C. Every scope restriction belongs to its full injective-clique relation.

This is a known-result formalization in the classical theory of acyclic database schemes, not a novelty claim: Beeri, Fagin, Maier, and Yannakakis, On the Desirability of Acyclic Database Schemes, Journal of the ACM 30(3), 1983, DOI 10.1145/2402.322389. The Lean proof supplies the indexed-scope and finite-alphabet construction explicitly. It treats only the nonconformal branch; the full classification remains unresolved.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Gluing/NonconformalCliqueObstruction.InjectiveOnClique`
- Truth anchor: `D5/S3/ConceptDynamics/Gluing/NonconformalCliqueObstruction.cliqueRows`
- Truth anchor: `D5/S3/ConceptDynamics/Gluing/NonconformalCliqueObstruction.nonconformal_clique_obstruction`
