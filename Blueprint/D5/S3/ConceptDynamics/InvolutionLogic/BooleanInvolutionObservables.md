# Boolean Involution Observables

## Abstract

Boolean observables split into flip and invariant parity sectors under an involution.

**Theorem 1.1 (Two flip observables have invariant XOR).**

$$\forall iota: X \to X, p, q: X \to \operatorname{Prop}, (\operatorname{PropFlip}\left(iota, p\right) \land \operatorname{PropFlip}\left(iota, q\right)) \Rightarrow \operatorname{PropInvariant}\left(iota, \operatorname{xorObservable}\left(p, q\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InvolutionLogic/BooleanInvolutionObservables.xor_invariant_of_flips` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each flip hypothesis says that applying the transformation negates the corresponding proposition-valued observable.

Negating both inputs leaves their exclusive-or unchanged. Thus the pointwise XOR belongs to the invariant sector.

No fixed-point-free or inhabited-carrier assumption is needed for this parity identity.

**Theorem 1.2 (A flip observable XOR an invariant observable still flips).**

$$\forall iota: X \to X, p, q: X \to \operatorname{Prop}, (\operatorname{PropFlip}\left(iota, p\right) \land \operatorname{PropInvariant}\left(iota, q\right)) \Rightarrow \operatorname{PropFlip}\left(iota, \operatorname{xorObservable}\left(p, q\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InvolutionLogic/BooleanInvolutionObservables.xor_flip_of_flip_invariant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The first observable changes truth value under the transformation, while the second retains its truth value.

Pointwise exclusive-or therefore changes truth value exactly once, so the resulting observable satisfies PropFlip.

## References

- Truth anchor: `D5/S3/ConceptDynamics/InvolutionLogic/BooleanInvolutionObservables.xor_flip_of_flip_invariant`
- Truth anchor: `D5/S3/ConceptDynamics/InvolutionLogic/BooleanInvolutionObservables.xor_invariant_of_flips`
- Dependency: [D5/S3/ConceptDynamics/InvolutionLogic/InvolutionTransversal](InvolutionTransversal.md)
