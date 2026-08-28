# Static Loss Versus Return Flow

## Abstract

Concrete two-by-two witnesses separate squared static coherence loss from squared return flow into a visible diagonal record.

For real two-by-two matrices, the entrywise square sum is the square of the Frobenius, or Hilbert-Schmidt, norm. Squaring preserves zero and nonzero values, while turning the chosen large and small thresholds into one and one quarter.

The retained record is the diagonal projection. Future dynamics are real linear maps, which excludes a nonzero constant map from manufacturing a return signal without discarded input.

**Theorem 1.1 (Large static loss can have zero return).**

$$\exists X, D, T, D = \operatorname{diag} \land 1 \leq \Vert (I-D)X\Vert^2 \land \Vert D(T((I-D)X))\Vert^2 = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Decoherence/StaticLossVersusReturnFlow.large_static_loss_with_zero_return` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Take one off-diagonal entry equal to two and use zero future dynamics. Its squared static loss is four, hence at least one, while the returned visible strength is exactly zero.

**Theorem 1.2 (Small nonzero static loss can have nonzero return).**

$$\exists X, D, T, D = \operatorname{diag} \land 0 < \Vert (I-D)X\Vert^2 \leq 1/4 \land \Vert D(T((I-D)X))\Vert^2 \neq 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Decoherence/StaticLossVersusReturnFlow.small_static_loss_with_nonzero_return` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Take one off-diagonal entry equal to one half. Its squared static loss is one quarter, while a linear dynamics sends that entry into the visible zero-zero diagonal record with nonzero strength.

**Theorem 1.3 (Static loss and return flow are logically independent).**

$$(\neg\forall X: QubitMatrix, D, T: Dynamics, D = \operatorname{diag} \Rightarrow 1 \leq \Vert (I-D)X\Vert^2 \Rightarrow \Vert D(T((I-D)X))\Vert^2 \neq 0) \land (\neg\forall X: QubitMatrix, D, T: Dynamics, D = \operatorname{diag} \Rightarrow \Vert D(T((I-D)X))\Vert^2 \neq 0 \Rightarrow 1 \leq \Vert (I-D)X\Vert^2)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Decoherence/StaticLossVersusReturnFlow.static_loss_and_return_flow_are_logically_independent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The two witnesses refute both universal one-way implications at the large threshold one. Static decoherence size and later return into the prediction interface are therefore different scalars.

## References

- Truth anchor: `D5/S3/Quantum/Decoherence/StaticLossVersusReturnFlow.large_static_loss_with_zero_return`
- Truth anchor: `D5/S3/Quantum/Decoherence/StaticLossVersusReturnFlow.small_static_loss_with_nonzero_return`
- Truth anchor: `D5/S3/Quantum/Decoherence/StaticLossVersusReturnFlow.static_loss_and_return_flow_are_logically_independent`
