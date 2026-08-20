# Congruence Kernel

## Abstract

The all-iterate pullback of an equivalence is its maximal forward congruence.

**Theorem 1.1 (Maximal forward congruence inside an equivalence).**

$$\begin{gathered}\forall Y: \operatorname{Type}, \tau: Y \to Y,\\R: \operatorname{StateRelation}(Y), \operatorname{Equivalence}(R) \Rightarrow\\\operatorname{Equivalence}(C_{\tau}(R)) \land \operatorname{TauCongruence}(\tau, C_{\tau}(R)) \land C_{\tau}(R) \subseteq R \land\\(\forall S: \operatorname{StateRelation}(Y), S \subseteq R \Rightarrow C_{\tau}(S) \subseteq C_{\tau}(R)) \land C_{\tau}(C_{\tau}(R)) = C_{\tau}(R) \land\\(\forall S: \operatorname{StateRelation}(Y), \operatorname{TauCongruence}(\tau, S) \Rightarrow S \subseteq R \Rightarrow S \subseteq C_{\tau}(R)) \land\\(\forall S: \operatorname{StateRelation}(Y), \operatorname{TauCongruence}(\tau, S) \Rightarrow ((S \subseteq R) \iff (S \subseteq C_{\tau}(R)))).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Separation/CongruenceKernel.congruence_kernel_laws` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an update tau and an equivalence R, define C_tau(R) by requiring that every iterate of tau sends a pair into R. The first six conjuncts establish equivalence, forward congruence, contraction, monotonicity, idempotence, and maximality.

The final conjunct gives the equivalent universal characterization: a forward-congruent relation lies inside R exactly when it lies inside the all-iterate kernel.

## References

- Truth anchor: `D5/S3/Observer/Separation/CongruenceKernel.congruence_kernel_laws`
