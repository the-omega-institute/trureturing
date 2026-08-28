# Joint Error-and-Erasure Unique Decoding

## Abstract

A code of minimum distance d has a unique legal message whenever twice the unknown-error budget plus the known-erasure budget is below d.

**Theorem 1.1 (The joint error-and-erasure condition gives unique decoding).**

$$\begin{aligned}\forall alpha: \operatorname{Type}, [\operatorname{DecidableEq}\left(alpha\right)],\\n, d, e, s \in \mathbb{N},\\C: \operatorname{Set}\left(\operatorname{Fin}\left(n\right) \to alpha\right), E: \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right),\\c, r: \operatorname{Fin}\left(n\right) \to alpha,\\\operatorname{MinDistanceAtLeast}\left(C, d\right) \land \operatorname{card}\left(E\right) \leq s \land\\2 \times e + s < d \land\\c \in C \land \operatorname{card}\left(\{i: \operatorname{Fin}\left(n\right) \mid \neg(i \in E) \land r(i) \neq c(i)\}\right) \leq e \Rightarrow\\\exists x: \operatorname{Fin}\left(n\right) \to alpha, (x \in C \land \operatorname{card}\left(\{i: \operatorname{Fin}\left(n\right) \mid \neg(i \in E) \land r(i) \neq x(i)\}\right) \leq e) \land\\\forall y: \operatorname{Fin}\left(n\right) \to alpha, (y \in C \land \operatorname{card}\left(\{i: \operatorname{Fin}\left(n\right) \mid \neg(i \in E) \land r(i) \neq y(i)\}\right) \leq e) \Rightarrow y = x.\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Coding/ErrorErasureUniqueDecoding.error_erasure_unique_decoding` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix the known erased-coordinate finset E. A legal candidate is compatible with the received word when it disagrees on at most e coordinates outside E.

Any coordinate where two compatible candidates disagree lies either in E, in the first candidate's unerased error set, or in the second candidate's unerased error set. Their Hamming distance is therefore at most s + e + e. The strict bound 2e + s < d and the code's minimum-distance condition force the candidates to coincide.

## References

- Truth anchor: `D5/S3/Arith/Coding/ErrorErasureUniqueDecoding.error_erasure_unique_decoding`
- Dependency: [D5/S3/Arith/Coding/ResidueCodeErrorDetection](ResidueCodeErrorDetection.md)
