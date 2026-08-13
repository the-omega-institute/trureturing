# Dense Phase Escape Identity

## Abstract

Dense fixed-point scaling gives the decay identity only at finitely many realizable exponents.

**Theorem 1.1 (Dense-phase identity on realizable exponents).**

$$\forall Y, f, A, n, k, c, \operatorname{Finite}(Y) \land \operatorname{Nonempty}(Y) \land 2 \leq n \land \operatorname{card}(Y) = n \land 0 < c < 1 \land \operatorname{card}(\operatorname{Fix}(f)) = k \land k = c\,n^{A} \Rightarrow \operatorname{escapeProbability}_{\operatorname{Fin}\,A}(f) = (1 - c)^{A} \land \lim_{B \to \infty}(1 - c)^{B} = 0 \land \exists A_0, A < A_0 \land \forall B, A_0 \leq B \Rightarrow \operatorname{card}(\operatorname{Fix}(f)) \neq c\,n^{B}.$$

*Proof.* Machine-checked in Lean as `D5/S0/Asymptotics/DensePhaseEscapeIdentity.dense_phase_escape_identity_on_realizable_exponents` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact escaped-listing cardinality reduces the repository's uniform escape probability to the stated power whenever the fixed-point count equals c times n to the address exponent.

The power profile converges to zero because zero is less than c and c is less than one. This decay is an abstract profile, not an asymptotic family of realizable transformations.

Indeed, the structural fixed-point bound supplies a finite cutoff A0. Every exponent satisfying the dense equation lies below A0, and the complete hypothesis bundle is witnessed concretely only at A = 1 in this module.

## References

- Truth anchor: `D5/S0/Asymptotics/DensePhaseEscapeIdentity.dense_phase_escape_identity_on_realizable_exponents`
- Dependency: [D5/S0/Asymptotics/DensePhaseUnrealizable](DensePhaseUnrealizable.md)
- Dependency: [D5/S0/Asymptotics/FixedPointFreeEscapeProbability](FixedPointFreeEscapeProbability.md)
