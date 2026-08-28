# Bare Tower Dimension Classification

## Abstract

A bare orthogonal Hilbert tower is classified by the Hilbert dimensions of its initial block, every shell, and its terminal residual.

**Theorem 1.1 (Block dimensions classify bare towers).**

$$\forall K \in Type, B \in \operatorname{Option}\left(\operatorname{Option}\left(Nat\right)\right) \to Type, Bprime \in \operatorname{Option}\left(\operatorname{Option}\left(Nat\right)\right) \to Type,\; \left(\operatorname{RCLike}\left(K\right) \land \left(\left(\forall i \in \operatorname{Option}\left(\operatorname{Option}\left(Nat\right)\right),\; \operatorname{NormedAddCommGroup}\left(B\left(i\right)\right) \land \left(\operatorname{InnerProductSpace}\left(K, B\left(i\right)\right) \land \operatorname{CompleteSpace}\left(B\left(i\right)\right)\right)\right) \land \left(\forall i \in \operatorname{Option}\left(\operatorname{Option}\left(Nat\right)\right),\; \operatorname{NormedAddCommGroup}\left(Bprime\left(i\right)\right) \land \left(\operatorname{InnerProductSpace}\left(K, Bprime\left(i\right)\right) \land \operatorname{CompleteSpace}\left(Bprime\left(i\right)\right)\right)\right)\right)\right) \Rightarrow \left(\left(\exists U \in \operatorname{LinearIsometryEquiv}\left(K, \operatorname{lp}\left(B, 2\right), \operatorname{lp}\left(Bprime, 2\right)\right),\; \exists u \in \left(\forall i \in \operatorname{Option}\left(\operatorname{Option}\left(Nat\right)\right),\; \operatorname{LinearIsometryEquiv}\left(K, B\left(i\right), Bprime\left(i\right)\right)\right),\; \forall i \in \operatorname{Option}\left(\operatorname{Option}\left(Nat\right)\right), x \in B\left(i\right),\; U\left(\operatorname{single}\left(2, i, x\right)\right) = \operatorname{single}\left(2, i, u\left(i\right)\left(x\right)\right)\right) \Leftrightarrow \left(\left(\exists J \in Type,\; \operatorname{Nonempty}\left(\operatorname{HilbertBasis}\left(J, K, B\left(\operatorname{none}\left(\right)\right)\right)\right) \land \operatorname{Nonempty}\left(\operatorname{HilbertBasis}\left(J, K, Bprime\left(\operatorname{none}\left(\right)\right)\right)\right)\right) \land \left(\left(\forall n \in Nat,\; \exists J \in Type,\; \operatorname{Nonempty}\left(\operatorname{HilbertBasis}\left(J, K, B\left(\operatorname{some}\left(\operatorname{some}\left(n\right)\right)\right)\right)\right) \land \operatorname{Nonempty}\left(\operatorname{HilbertBasis}\left(J, K, Bprime\left(\operatorname{some}\left(\operatorname{some}\left(n\right)\right)\right)\right)\right)\right) \land \left(\exists J \in Type,\; \operatorname{Nonempty}\left(\operatorname{HilbertBasis}\left(J, K, B\left(\operatorname{some}\left(\operatorname{none}\left(\right)\right)\right)\right)\right) \land \operatorname{Nonempty}\left(\operatorname{HilbertBasis}\left(J, K, Bprime\left(\operatorname{some}\left(\operatorname{none}\left(\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Completion/BareTowerDimensionClassification.bare_tower_dimension_classification` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The block index has one initial coordinate, one coordinate for every natural-numbered shell, and one terminal residual coordinate. The ambient carrier is their canonical square-summable Hilbert sum.

Tower equivalence is witnessed by a global unitary together with its unitary computation rule on every canonical block embedding.

Two blocks have the same Hilbert dimension when each admits a Hilbert basis on one common index type. Basis representations construct the block unitaries, and the local square-summable bridge assembles them into the global unitary.

## References

- Truth anchor: `D5/S3/Observer/Completion/BareTowerDimensionClassification.bare_tower_dimension_classification`
