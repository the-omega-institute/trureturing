# Positive trace pairing and logarithmic regularization

## Abstract

Actual bounded logarithmic trace energies on positive trace-class contractions.

**Theorem 1.1 (Noncommuting positive trace pairing).**

$$\forall H \in CompleteComplexHilbertSpace, A \in \operatorname{BoundedComplexOperator}\left(H\right), rho \in \operatorname{TraceClass}\left(H\right),\; \left(\operatorname{Nonnegative}\left(A\right) \land \operatorname{Nonnegative}\left(rho\right)\right) \Rightarrow \operatorname{Nonnegative}\left(\operatorname{Re}\left(\operatorname{tracePairing}\left(A, rho\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/TraceClass/LogRegularization.tracePairing_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mathlib contributors (2026). *Operator logarithms through the continuous functional calculus*. URL: <https://github.com/leanprover-community/mathlib4/tree/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Analysis/SpecialFunctions/ContinuousFunctionalCalculus/ExpLog>.

*Commentary.*

For a bounded positive A and a positive trace-class rho, Re Tr(A rho) is nonnegative. With R equal to sqrt A, the trace-class ideal makes R rho trace class. Bounded-factor cyclicity gives Tr(A rho) = Tr(R rho R), and the latter operator is positive. The argument retains self-adjointness of R and requires no commutation or trace-class square root of rho.

Positivity and normalization also imply rho is an operator contraction: the trace norm equals the real trace, and the operator norm is bounded by the trace norm.

**Theorem 1.2 (Lower semicontinuity of the regularized supremum).**

$$\forall H \in CompleteComplexHilbertSpace, rho \in \operatorname{TraceClass}\left(H\right),\; \operatorname{LowerSemicontinuous}\left(\operatorname{regularizedSupremumAt}\left(rho, \operatorname{Reference}\left(H\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/TraceClass/LogRegularization.lowerSemicontinuous_regularizedSupremum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mathlib contributors (2026). *Operator logarithms through the continuous functional calculus*. URL: <https://github.com/leanprover-community/mathlib4/tree/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Analysis/SpecialFunctions/ContinuousFunctionalCalculus/ExpLog>.

*Commentary.*

The reference space consists of actual positive trace-class contractions and carries the topology from the genuine trace norm. For epsilon positive, B_epsilon(T) = log(1+epsilon) I - log(T+epsilon I) is a bounded positive self-adjoint operator. The pairing Re Tr(B_epsilon(T) rho) is continuous in T for every fixed trace-class rho.

The auxiliary regularizedSupremum is the ENNReal supremum of these actual trace pairings at epsilon_n = 1/(n+1). Continuity of each term gives lower semicontinuity of the supremum. For positive rho the same supremum reverses Loewner order, including noncommuting references.

Its identification with a singular spectral log-energy sum, the zero-kernel projection identity, scaling, self entropy, and finite-entropy cross-energy domination require additional spectral results. These statements are not consequences of the auxiliary definition alone. The logarithm theorems are supplied by pinned Mathlib, and the analytic trace-class infrastructure is attributed to Tom Ole Diem's Physlib.

## References

- Truth anchor: `D5/S3/Quantum/Analysis/TraceClass/LogRegularization.lowerSemicontinuous_regularizedSupremum`
- Truth anchor: `D5/S3/Quantum/Analysis/TraceClass/LogRegularization.tracePairing_nonneg`
- Dependency: [D5/S3/Quantum/Analysis/TraceClass/Pairing](Pairing.md)
