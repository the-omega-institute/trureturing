# Invariant Origin Recovery Obstruction

## Abstract

A transitive invariant readout cannot recover or duplicate a nontrivial origin.

**Theorem 1.1 (No absolute-origin reconstruction).**

$$\begin{gathered}\forall G, A, Y: Type,\\{}\operatorname{Group}(G) \land \operatorname{MulAction}(G, A) \land \operatorname{IsPretransitive}(G, A) \land \operatorname{Nontrivial}(A),\\{}\forall q: A \to Y, (\forall g: G, a: A, q(\operatorname{smul}(g, a)) = q(a)) \Rightarrow\\{}(\forall a, b: A, q(a) = q(b)) \land\\{}(\neg \exists d: Y \to A, \operatorname{LeftInverse}(d, q)) \land\\{}(\neg \exists C: Y \to A \times A, \forall a: A, C(q(a)) = (a, a)) \land\\{}(\exists a, b: A, a \neq b \land q(a) = q(b)).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Naturality/InvariantOriginRecoveryObstruction.no_absolute_origin_reconstruction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A group G acts transitively on a nontrivial origin type A. The internal readout q is invariant under that action, so every two origins have the same internal description.

The declaration rules out both a left-inverse decoder and a duplicator that would return the ordered pair (a,a) from q(a). It also exposes two distinct origins with equal readout, retaining the relational coordinate distinction in the public statement.

## References

- Truth anchor: `D5/S3/Observer/Naturality/InvariantOriginRecoveryObstruction.no_absolute_origin_reconstruction`
- Dependency: [D5/S3/Observer/Completion/StructuralCompletionSignature](../Completion/StructuralCompletionSignature.md)
