# Primary Pseudoperfect Port Composition

## Abstract

The complementary-prime-divisor sum has a coprime Leibniz rule, which drives port composition and the coprime extension criterion for primary pseudoperfect numbers.

For natural numbers R, c, and B, portDelta(R,c,B) is the truncated natural difference cB - R squarefreeDeriv(B). The theorems below use the squarefreeDeriv and IsPPN definitions from the frozen PrimaryPseudoperfectPorts module.

**Theorem 1.1 (Coprime Leibniz rule).**

$$\forall A, B \in \mathbb{N}, \operatorname{Coprime}\left(A, B\right) \Rightarrow \operatorname{squarefreeDeriv}\left(A \cdot B\right) = A \cdot \operatorname{squarefreeDeriv}\left(B\right) + B \cdot \operatorname{squarefreeDeriv}\left(A\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/PrimeForms/PrimaryPseudoperfectPortComposition.squarefreeDeriv_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Coprimality partitions the prime factors of AB into disjoint factors from A and B. Transporting each complementary divisor across that partition produces the two summands.

**Theorem 1.2 (Port composition law).**

$$\forall A, B, R, c \in \mathbb{N}, \operatorname{Coprime}\left(A, B\right) \Rightarrow \operatorname{portDelta}\left(R, c, A \cdot B\right) = \operatorname{portDelta}\left(R \cdot A, \operatorname{portDelta}\left(R, c, A\right), B\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/PrimeForms/PrimaryPseudoperfectPortComposition.portDelta_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Han Wang (2026). *Port Fillings for Primary Pseudoperfect Numbers*. DOI: [10.48550/arXiv.2605.21518](https://doi.org/10.48550/arXiv.2605.21518).

*Commentary.*

On coprime factors, the Leibniz rule makes the residual through AB equal to the residual obtained by substituting the output at A as the input coefficient at B.

Wang's Lemma 6.2 states this orientation and its symmetric partner for coprime squarefree integers. The Lean theorem is classified as repository-derived with that acknowledgement because it drops both squarefreeness hypotheses and records one orientation.

**Theorem 1.3 (Coprime extension criterion).**

$$\forall K, C \in \mathbb{N}, \operatorname{IsPPN}\left(K\right) \land \operatorname{Squarefree}\left(C\right) \land 1 < C \land \operatorname{Coprime}\left(K, C\right) \Rightarrow (\operatorname{IsPPN}\left(K \cdot C\right) \Leftrightarrow C - K \cdot \operatorname{squarefreeDeriv}\left(C\right) = 1).$$

*Proof.* Machine-checked in Lean as `D5/S3/PrimeForms/PrimaryPseudoperfectPortComposition.isPPN_mul_iff_port` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If K is primary pseudoperfect and C is a nontrivial squarefree factor coprime to K, then KC is primary pseudoperfect exactly when the natural residual C - K squarefreeDeriv(C) equals one.

## References

- Truth anchor: `D5/S3/PrimeForms/PrimaryPseudoperfectPortComposition.isPPN_mul_iff_port`
- Truth anchor: `D5/S3/PrimeForms/PrimaryPseudoperfectPortComposition.portDelta_mul`
- Truth anchor: `D5/S3/PrimeForms/PrimaryPseudoperfectPortComposition.squarefreeDeriv_mul`
- Dependency: [D5/S3/PrimeForms/PrimaryPseudoperfectPorts](PrimaryPseudoperfectPorts.md)
