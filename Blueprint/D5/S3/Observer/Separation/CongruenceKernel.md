# Congruence Kernel

## Abstract

The all-iterate pullback of an equivalence is its maximal forward congruence.

**Theorem 1.1 (Maximal forward congruence inside an equivalence).**

$$\forall Y, R,\\\operatorname{Equivalence}(C(R)) \land \forall y, yPrime, (y, yPrime) \in C(R) \Rightarrow (tau(y), tau(yPrime)) \in C(R) \land C(R) \subseteq R \land \forall S, S \subseteq R \Rightarrow C(S) \subseteq C(R) \land C(C(R)) = C(R) \land \forall S, S \subseteq R \land (tau(y), tau(yPrime)) \in S \Rightarrow C(S) \subseteq C(R) \land \forall S, ((tau(y), tau(yPrime)) \in S \Rightarrow R \subseteq C(R)) \Rightarrow (S \subseteq R) \iff (S \subseteq C(R)).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Separation/CongruenceKernel.congruence_kernel_laws` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an update tau and an equivalence R, define C_tau(R) by requiring that every iterate of tau sends a pair into R. The first six conjuncts establish equivalence, forward congruence, contraction, monotonicity, idempotence, and maximality.

The final conjunct gives the equivalent universal characterization: a forward-congruent relation lies inside R exactly when it lies inside the all-iterate kernel.

## References

- Truth anchor: `D5/S3/Observer/Separation/CongruenceKernel.congruence_kernel_laws`
