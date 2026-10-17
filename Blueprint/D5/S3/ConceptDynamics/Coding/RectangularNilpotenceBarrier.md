# Rectangular nilpotence barrier

## Abstract

Nilpotence depth cannot change by more than the number of rectangular exchanges.

**Theorem 1.1 (Shared cumulative lag witnesses).**

Lean statement: `D5/S3/ConceptDynamics/Coding/RectangularNilpotenceBarrier.exchange_chain_lag`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/RectangularNilpotenceBarrier.exchange_chain_lag` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an arbitrary universe-polymorphic semiring R and c : ExchangeChain R A B L, the same pair X of size n by m and Y of size m by n satisfies A*X=X*B, B*Y=Y*A, X*Y=A^L and Y*X=B^L. Every length including zero, Fin 0, unequal rectangular intermediate dimensions and singular vertices remain in scope.

This is the cumulative proof from FixedPositivePartitionSseDistance.theorem32_2, shared in the owner of ExchangeChain and rectangular_exchange_power. The nil branch chooses the two identities; a cons extends the tail pair X,Y to U*X,Y*V. Both the partition-distance lower bound and FiniteKernelLadder.Path.lag directly consume this declaration. The extraction reuses existing mathematics and receives no new mathematical-content or owner credit.

**Theorem 1.2 (A depth gap excludes short chains).**

$$\forall R \in Type, ringR \in \operatorname{Semiring}\left(R\right), n \in Nat, m \in Nat, a \in Nat, b \in Nat, L \in Nat, A \in \operatorname{Mat}\left(R, n, n\right), B \in \operatorname{Mat}\left(R, m, m\right), chain \in \operatorname{ExchangeChain}\left(R, A, B, L\right), depthA \in \operatorname{ExactDepth}\left(A, a\right), depthB \in \operatorname{ExactDepth}\left(B, b\right),\; a \le b + L \land b \le a + L$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/RectangularNilpotenceBarrier.chain_depth_barrier` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An elementary exchange has rectangular factors U and V, with potentially different intermediate dimensions. The identity (UV)^(j+1)=U(VU)^j V transfers every zero power with a cost of one exponent.

Induction along the actual matrix chain bounds the two endpoint depths in both directions. The theorem retains every rectangular intermediate dimension and makes no essentiality assumption about intermediate matrices.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/RectangularNilpotenceBarrier.chain_depth_barrier`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/RectangularNilpotenceBarrier.exchange_chain_lag`
