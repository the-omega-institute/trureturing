# Equality in the Green-Class Window Entropy Bound

## Abstract

A naming window reaches its entropy bound exactly when every pinned coordinate law is uniform on the full alphabet.

**Theorem 1.1 (Maximum window entropy characterizes uniform coordinates).**

$$\begin{gathered}H(\operatorname{windowLaw}(\operatorname{coordLaw}(mu))) = n \times \operatorname{namingDim}(O) \times \log{2} \Leftrightarrow\\\forall i \in S, \operatorname{coordLaw}(mu, i) = (a\mapsto \operatorname{card}(O)^{-1}).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/NamingWindow/GreenClassWindowEntropyEquality.shannonEntropy_windowLaw_eq_namingDim_iff_uniform` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

GreenClassWindowEntropy reduces the entropy of a finite naming window to the sum of its coordinate entropies and bounds each summand by log(card O). Equality of the finite sums forces every coordinate summand to attain that same upper bound.

EntropyEquality then identifies each maximizing coordinate law with the uniform law on all of O. Conversely, uniformity at every coordinate makes every summand maximal, so additivity gives equality for the window.

Only coordinates in S are constrained. When S is empty, both the entropy identity and the coordinatewise condition are vacuous, so the equivalence still holds without a separate exception.

## References

- Truth anchor: `D5/S3/Entropy/NamingWindow/GreenClassWindowEntropyEquality.shannonEntropy_windowLaw_eq_namingDim_iff_uniform`
- Dependency: [D5/S3/Entropy/EntropyEquality](../EntropyEquality.md)
- Dependency: [D5/S3/Entropy/NamingWindow/GreenClassWindowEntropy](GreenClassWindowEntropy.md)
