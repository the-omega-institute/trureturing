# Uniform qutrit APPT spectral bound

## Abstract

The first qutrit spectral LMI yields the purity bound 3/(8n) for every n at least 11.

**Theorem 1.1 (K1-only uniform purity estimate).**

$$\forall (k:\mathbb{N}), (8\leq k)\Rightarrow \forall (l:Fin\left(3\cdot (3+k)\right)\to \mathbb{R}), ((Antitone\left(l\right))\land (\forall (i:Fin\left(3\cdot (3+k)\right)), 0\leq l\left(i\right))\land (\sum_{i:Fin\left(3\cdot (3+k)\right)} l\left(i\right)=1)\land (Matrix.PosSemidef\left(QutritSpectralReduction.K1\left(QutritSpectralReduction.boundaryValues\left(k, l\right)\right)\right)))\Rightarrow \sum_{i:Fin\left(3\cdot (3+k)\right)} (l\left(i\right))^{2}\leq \frac{3}{8\cdot ((3+k:\mathbb{N}):\mathbb{R})}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSpectralBound.uniform_spectral_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Here n=3+k with k at least 8. An antitone nonnegative real spectrum of mass one is bounded using K1 alone. The argument extracts two boundary inequalities, reconstructs the spectrum from gaps, transfers a 33-ray cone certificate, and bounds every middle-coordinate mixture. The sum 3+k is formed in the natural numbers before its coercion to the reals; the quotient is real division.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSpectralBound.uniform_spectral_bound`
- Dependency: [D5/S3/Quantum/Entanglement/AbsolutePPT/BoundaryConeDecomposition](BoundaryConeDecomposition.md)
- Dependency: [D5/S3/Quantum/Entanglement/AbsolutePPT/QutritSpectralReduction](QutritSpectralReduction.md)
