# Completion Isomorphism Criterion

## Abstract

The completion map is an equivalence exactly under separation and unique realization.

**Theorem 1.1 (Completion is equivalent to separation and unique realization).**

$$\forall I, X, S: \operatorname{InverseStageSystem}(I), q, \operatorname{CompatibleProjection}(S, q) \Rightarrow 
((\exists e: X \equiv \operatorname{CompatibleFamilies}(S), \operatorname{toFun}(e) = \operatorname{completionMap}(S, q)) \iff 
((\forall x, y: X, (\forall i: I, q_{i}(x) = q_{i}(y)) \Rightarrow x = y) \land 
(\forall a: \operatorname{CompatibleFamilies}(S), \exists! x: X, \forall i: I, q_{i}(x) = a_{i}))).$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/InverseLimits/CompletionIsomorphismCriterion.completion_map_equiv_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let S be a type-valued inverse-stage system with restriction channels satisfying identity and composition. A compatible family has one coordinate at every stage and is preserved by every restriction.

A compatible family of probes q induces the canonical map from X to compatible stage families. That map underlies an equivalence exactly when the probes jointly separate points and every compatible family is realized by a unique point of X.

Pinned Mathlib supplied the exact Equiv.ofBijective constructor, which the backward proof applies after proving injectivity from joint separation and surjectivity from realization. Repository search found a related kernel-quotient theorem and finite itinerary instances, but no theorem with both clauses for the candidate X.

This statement is explicitly at the level of types. In a category with additional structure, an underlying bijection needs separate structure-preservation evidence. Also, surjectivity alone supplies existence rather than uniqueness; uniqueness here follows from the equivalence, or from realization together with joint separation.

## References

- Truth anchor: `D5/S3/ObserverMemory/InverseLimits/CompletionIsomorphismCriterion.completion_map_equiv_iff`
