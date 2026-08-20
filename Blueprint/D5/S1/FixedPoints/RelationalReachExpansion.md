# Relational Reachability Expansion

## Abstract

A transition relation's direct image preserves arbitrary unions, and its reachability least fixed point is the union of all finite stages.

**Theorem 1.1 (Relational reachability expands through finite stages).**

$$\forall X, J: \operatorname{Type},\\R: \operatorname{Set}(X \times X), I: \operatorname{Set}(X), A: J \to \operatorname{Set}(X),\\\operatorname{image}_{R}(\operatorname{union}_{i\in J} A(i)) = \operatorname{union}_{i\in J} \operatorname{image}_{R}(A(i)) \land\\\operatorname{lfp}((S \mapsto I \operatorname{union} \operatorname{image}_{R}(S))) = \operatorname{union}_{n\in \mathbb{N}} (S \mapsto I \operatorname{union} \operatorname{image}_{R}(S))^{[n]}(\emptyset).$$

*Proof.* Machine-checked in Lean as `D5/S1/FixedPoints/RelationalReachExpansion.finite_step_expansion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The transition relation is supplied as a set of state pairs. Its direct image sends a set of current states to all one-step successors. The first public conjunct states preservation of an arbitrary indexed union, including an empty family.

The reachability operator is constructed from the source primitives as Phi(A) = I0 union image_R(A). Reachability is its independently defined least fixed point, rather than a name assigned to the target stage union.

Mathlib's exact SetRel.image_iUnion theorem proves the first conjunct and makes the constructed operator omega-Scott-continuous. The frozen Kleene-stage theorem is then applied directly to obtain the second conjunct.

## References

- Truth anchor: `D5/S1/FixedPoints/RelationalReachExpansion.finite_step_expansion`
- Dependency: [D5/S1/FixedPoints/KleeneStageLimit](KleeneStageLimit.md)
