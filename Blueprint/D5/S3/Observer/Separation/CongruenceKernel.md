# Congruence Kernel

## Abstract

The all-iterate pullback of an equivalence is its maximal forward congruence.

**Definition 1.1 (A tau-congruence is preserved by one forward update).**

$$\forall Y: \operatorname{Type}, \tau: Y \to Y, S: \operatorname{StateRelation}(Y),\\{}\operatorname{TauCongruence}(\tau, S) \iff \forall y, yprime: Y, \operatorname{pair}(y, yprime) \in S \Rightarrow \operatorname{pair}(\tau(y), \tau(yprime)) \in S.$$

*Formalization.* `D5/S3/Observer/Separation/CongruenceKernel.TauCongruence` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A state relation S is a congruence for tau exactly when membership of an ordered pair (y,y') in S implies membership of the updated pair (tau(y),tau(y')).

**Definition 1.2 (The congruence kernel pulls a relation back along every iterate).**

$$\forall Y: \operatorname{Type}, \tau: Y \to Y, R: \operatorname{StateRelation}(Y),\\{}\operatorname{congruenceKernel}(\tau, R) = \{pair: Y \times Y \mid \forall k: \mathbb{N}, \operatorname{pair}(\operatorname{iterate}(\tau, k, \operatorname{fst}(pair)), \operatorname{iterate}(\tau, k, \operatorname{snd}(pair))) \in R\}.$$

*Formalization.* `D5/S3/Observer/Separation/CongruenceKernel.congruenceKernel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The congruence kernel of R under tau consists exactly of those state pairs whose two coordinates remain R-related after every natural iterate of tau, including the zeroth iterate.

**Theorem 1.3 (Maximal forward congruence inside an equivalence).**

$$\begin{gathered}\forall Y: \operatorname{Type}, \tau: Y \to Y,\\R: \operatorname{StateRelation}(Y), \operatorname{Equivalence}(R) \Rightarrow\\\operatorname{Equivalence}(C_{\tau}(R)) \land \operatorname{TauCongruence}(\tau, C_{\tau}(R)) \land C_{\tau}(R) \subseteq R \land\\(\forall S: \operatorname{StateRelation}(Y), S \subseteq R \Rightarrow C_{\tau}(S) \subseteq C_{\tau}(R)) \land C_{\tau}(C_{\tau}(R)) = C_{\tau}(R) \land\\(\forall S: \operatorname{StateRelation}(Y), \operatorname{TauCongruence}(\tau, S) \Rightarrow S \subseteq R \Rightarrow S \subseteq C_{\tau}(R)) \land\\(\forall S: \operatorname{StateRelation}(Y), \operatorname{TauCongruence}(\tau, S) \Rightarrow ((S \subseteq R) \iff (S \subseteq C_{\tau}(R)))).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Separation/CongruenceKernel.congruence_kernel_laws` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an update tau and an equivalence R, define C_tau(R) by requiring that every iterate of tau sends a pair into R. The first six conjuncts establish equivalence, forward congruence, contraction, monotonicity, idempotence, and maximality.

The final conjunct gives the equivalent universal characterization: a forward-congruent relation lies inside R exactly when it lies inside the all-iterate kernel.

## References

- Truth anchor: `D5/S3/Observer/Separation/CongruenceKernel.TauCongruence`
- Truth anchor: `D5/S3/Observer/Separation/CongruenceKernel.congruenceKernel`
- Truth anchor: `D5/S3/Observer/Separation/CongruenceKernel.congruence_kernel_laws`
