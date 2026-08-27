# Finite Distinguishing Certificate

## Abstract

A finite operational quotient admits a finite protocol certificate even for an infinite protocol family.

**Theorem 1.1 (Finite quotient classes have a finite separating protocol subfamily).**

$$\begin{gathered}\forall X, P, O, C: \operatorname{Type},\\{}[\operatorname{Finite}(C)],\\{}out: P \to \left(X \to O\right), Q: \operatorname{Set}(P), q: X \to C, surjective: \operatorname{Surjective}(q),\\{}\forall x, y: X, q(x) = q(y) \iff \forall protocol: P \in Q, out(protocol)(x) = out(protocol)(y) \Rightarrow\\{}\exists selected: \operatorname{Finset}(P),\\{}(\operatorname{subset}(selected, Q) \land \forall x, y: X, q(x) = q(y) \iff \forall protocol: P \in selected, out(protocol)(x) = out(protocol)(y)).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/PredictionCertificates/FiniteDistinguishingCertificate.finite_distinguishing_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The available protocol family may be infinite. A finite class carrier and a surjective class map encode exactly when all available protocol readouts agree. Choosing one separating protocol for each pair of distinct classes produces a finite selected subfamily with the same kernel.

The selected family is therefore a finite certificate for the complete quotient, and its finiteness comes from the target class carrier rather than from the protocol syntax.

## References

- Truth anchor: `D5/S3/ObserverMemory/PredictionCertificates/FiniteDistinguishingCertificate.finite_distinguishing_certificate`
