# Golden Separation Bound

## Abstract

Distinct integer points in a finite golden-slope window have an explicit positive minimum spectral spacing.

**Theorem 1.1 (Finite golden-slope windows are uniformly separated).**

$$\forall H \in \mathbb{N}, 2 \leq H \Rightarrow \frac{1}{\varphi (H - 1)} \leq delta_{\varphi}(H).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/GoldenCoding/GoldenSeparationBound.golden_separation_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Here H is a natural number at least two, R_H is the integer square {1,...,H}^2, and E_phi(m,n)=m phi+n. The Lean definition of delta_phi(H) is the minimum of |E_phi(x)-E_phi(y)| over all distinct x and y in R_H.

For the coordinate differences a and b, the repository's actual golden-integer carrier packages b+a phi. Its real embedding, conjugation, and integer norm give an absolute norm at least one. The conjugate embedding is bounded by phi(H-1), which yields the displayed lower bound for every distinct pair and therefore for the finite minimum.

## References

- Truth anchor: `D5/S3/Observer/GoldenCoding/GoldenSeparationBound.golden_separation_bound`
- Dependency: [D5/S1/Scale/Embedding](../../../S1/Scale/Embedding.md)
