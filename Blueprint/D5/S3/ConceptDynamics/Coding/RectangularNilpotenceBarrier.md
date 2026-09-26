# Rectangular nilpotence barrier

## Abstract

Nilpotence depth cannot change by more than the number of rectangular exchanges.

**Theorem 1.1 (A depth gap excludes short chains).**

$$\forall R \in Type, ringR \in \operatorname{Semiring}\left(R\right), n \in Nat, m \in Nat, a \in Nat, b \in Nat, L \in Nat, A \in \operatorname{Mat}\left(R, n, n\right), B \in \operatorname{Mat}\left(R, m, m\right), chain \in \operatorname{ExchangeChain}\left(R, A, B, L\right), depthA \in \operatorname{ExactDepth}\left(A, a\right), depthB \in \operatorname{ExactDepth}\left(B, b\right),\; a \le b + L \land b \le a + L$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/RectangularNilpotenceBarrier.chain_depth_barrier` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An elementary exchange has rectangular factors U and V, with potentially different intermediate dimensions. The identity (UV)^(j+1)=U(VU)^j V transfers every zero power with a cost of one exponent.

Induction along the actual matrix chain bounds the two endpoint depths in both directions. The theorem retains every rectangular intermediate dimension and makes no essentiality assumption about intermediate matrices.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/RectangularNilpotenceBarrier.chain_depth_barrier`
