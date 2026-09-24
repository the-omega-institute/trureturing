# Counted group chain recovery windows

## Abstract

One finite matrix chain constructs one equivariant homeomorphism carrying both edge windows and both group-coordinate windows. The transfer is read from that same code.

**Theorem 1.1 (Construct one code with four recovery budgets).**

$$\forall H \in Type, group \in \operatorname{Group}\left(H\right), finite \in \operatorname{Fintype}\left(H\right), topology \in \operatorname{TopologicalSpace}\left(H\right), continuousGroup \in \operatorname{IsTopologicalGroup}\left(H\right), a \in Nat, b \in Nat, L \in Nat, A \in \operatorname{GroupMat}\left(H, a, a\right), B \in \operatorname{GroupMat}\left(H, b, b\right), ch \in \operatorname{ExchangeChain}\left(\operatorname{MonoidAlgebra}\left(Nat, H\right), A, B, L\right),\; \operatorname{Nonempty}\left(\operatorname{WindowGroupConjugacy}\left(A, B, L\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/CountedGroupWindowChain.chain_has_window_group_conjugacy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The elementary map is built from counted group-labelled edge fibers. Its forward edge uses the present and next input, its inverse uses the preceding and present output. The group transfers use the first split label and the preceding inverse split label. Composition adds all four budgets, and induction handles every intermediate matrix dimension.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/CountedGroupWindowChain.chain_has_window_group_conjugacy`
- Dependency: [D5/S3/ConceptDynamics/Coding/CountedGroupOverlap](CountedGroupOverlap.md)
