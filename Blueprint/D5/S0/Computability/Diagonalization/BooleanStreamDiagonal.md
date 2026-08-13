# Boolean Stream Diagonalization

## Abstract

Boolean diagonal negation exceeds every proposed enumeration of infinite streams.

**Theorem 1.1 (The diagonal stream exceeds every history layer).**

$$\forall P: \mathbb{N}\to \mathbb{N}\to \operatorname{Bool}, \text{let } D(h) := \operatorname{not}(P(h,h)); (\forall h, D \neq P(h)) \land \neg\operatorname{Surjective}(P) \land \neg\exists V: \mathbb{N}\to \mathbb{N}\to \operatorname{Bool}, \operatorname{Computable}_2(V) \land \forall trajectory: \mathbb{N}\to \operatorname{Bool}, \operatorname{Computable}(trajectory) \Rightarrow \exists code, V(code) = trajectory.$$

*Proof.* Machine-checked in Lean as `D5/S0/Computability/Diagonalization/BooleanStreamDiagonal.boolean_stream_diagonal_exceeds_every_history` (`✓ std3`). ∎

*Citation.* F. William Lawvere (1969). *Diagonal arguments and cartesian closed categories*. DOI: [10.1007/BFb0080769](https://doi.org/10.1007/BFb0080769).

*Commentary.*

For an arbitrary history-indexed listing P of Boolean streams, define D at index h by negating P's h-th row at its h-th coordinate. Equality D = P(h) would force not(P(h,h)) = P(h,h), so D differs from every listed row. This is the source atom's explicit diagonal property.

The missing diagonal row proves that the full stream space is not exhausted by the history listing. For the program-level clause, take any computable total evaluator V. Its negated diagonal is again a computable Boolean trajectory, so a claim that V outputs every computable trajectory supplies a code e for that diagonal and contradicts V(e,e). This is the source's self-diagonal index e.

Pinned Mathlib and D5 were searched before proving. Mathlib's Function.exists_fixed_point_of_surjective is the exact abstract Lawvere engine used to refute both surjectivity claims. The neighboring D5 theorem SyntaxSemanticsBoundary.same_layer_predicates_not_enumerable treats predicates on an arbitrary code type; it does not expose this Boolean stream witness or the evaluator clause, so it is related but not a duplicate.

## References

- Truth anchor: `D5/S0/Computability/Diagonalization/BooleanStreamDiagonal.boolean_stream_diagonal_exceeds_every_history`
- Dependency: [D5/S0/Computability/SyntaxSemanticsBoundary](../SyntaxSemanticsBoundary.md)
