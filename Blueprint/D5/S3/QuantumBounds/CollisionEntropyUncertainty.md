# Collision-Entropy Uncertainty

## Abstract

Collision conservation across a complete finite measurement family gives a summed entropy uncertainty bound.

**Theorem 1.1 (Collision conservation implies the summed entropy bound).**

$$\begin{gathered}\forall d \in \mathbb{N}, 0<d,\\\forall p: \operatorname{Fin}(d+1)\to\operatorname{Fin}(d)\to\mathbb{R},\\\forall purity \in \mathbb{R},\\(\forall b, (\forall i, 0\le p(b,i)) \land \sum_{i} p(b,i)=1),\\\sum_{b} \sum_{i} p(b,i)^{2}=1+purity \Rightarrow\\(d+1)\cdot \log(\frac{d+1}{1+purity}) \le \sum_{b} \operatorname{shannonEntropy}(p(b)).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumBounds/CollisionEntropyUncertainty.collision_entropy_uncertainty` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let d be positive. For d+1 finite measurement laws on d outcomes, assume every law is nonnegative and normalized and that the sum of their squared-probability collision values is one plus the supplied state purity. The conclusion bounds their summed Shannon entropy below by (d+1) times the natural logarithm of (d+1)/(1+purity).

The first finite Jensen application uses each measurement law as its own weights and proves that its Shannon entropy is at least minus the logarithm of its collision value. Zero-probability outcomes have zero weight, so they are assigned the harmless positive logarithm argument one inside that calculation.

A second finite Jensen application uses uniform weights over the d+1 measurements. Collision conservation then replaces their average by (1+purity)/(d+1), giving the displayed bound. The module reuses the repository finite Shannon entropy and mathlib's weighted Jensen theorem; it assumes no unrecorded spectral or numerical certificate.

## References

- Truth anchor: `D5/S3/QuantumBounds/CollisionEntropyUncertainty.collision_entropy_uncertainty`
- Dependency: [D5/S3/Entropy/MaxEntropy](../Entropy/MaxEntropy.md)
