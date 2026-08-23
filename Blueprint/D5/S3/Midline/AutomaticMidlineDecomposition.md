# Automatic Midline Decomposition

## Abstract

Half-density unitarity and self-resonance select the same automatic midline.

**Theorem 1.1 (Half-density unitarity is equivalent to self-resonance).**

$$\begin{gathered}\forall A, M: A\to\mathbb{R}, \alpha\in\mathbb{R}, s\in\mathbb{C},\\ (\forall a, 0\le M(a)), (\exists a, M(a)\neq0)\\ \Rightarrow (\forall a, |\operatorname{halfDensityCoefficient}(M,\alpha,s,a)|=1)\\ \Leftrightarrow \operatorname{KernelResonant}(\alpha,s,s). \end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Midline/AutomaticMidlineDecomposition.half_density_unitarity_iff_self_resonance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a nonnegative, nontrivial heat spectrum, coordinatewise unit modulus after half-density normalization is equivalent to self-resonance. Both conditions independently characterize the real line at alpha over two.

The proof is a thin wrapper over the exact half-density and resonance characterizations in the universal heat-trace module.

This is a partial closure of the automatic-midline clause. The square-summability boundary, an independent reflection center, and the named analytic and quasicrystal instances remain open.

## References

- Truth anchor: `D5/S3/Midline/AutomaticMidlineDecomposition.half_density_unitarity_iff_self_resonance`
- Dependency: [D5/S3/Midline/UniversalHeatTrace](UniversalHeatTrace.md)
