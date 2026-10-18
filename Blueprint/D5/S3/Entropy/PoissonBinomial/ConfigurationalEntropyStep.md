# Pairwise Configurational Entropy

## Abstract

Pairwise smoothing increases the entropy of independent Bernoulli coordinates conditional on their sum.

**Theorem 1.1 (Continuity at the boundary).**

$$\forall M: \mathbb{N}, \operatorname{Continuous}\left(F_{M}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/PoissonBinomial/ConfigurationalEntropyStep.continuous_F` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* D. Monkman; J. Sirker (2023). *Symmetry-resolved entanglement: general considerations, calculation from correlation functions, and bounds for symmetry-protected topological phases*. DOI: [10.48550/arXiv.2307.05820](https://doi.org/10.48550/arXiv.2307.05820). URL: <https://arxiv.org/abs/2307.05820>.

*Commentary.*

Each Poisson-binomial mass is a finite sum of products of the Bernoulli parameters and their complements. Continuity of binary entropy and of negative x log x, including zero, therefore gives continuity of F on the whole parameter space.

**Theorem 1.2 (An interior T-transform increases F).**

$$\forall M: \mathbb{N}, \forall x: \operatorname{Fin}\left(M\right) \to \mathbb{R}, \forall y: \operatorname{Fin}\left(M\right) \to \mathbb{R}, \operatorname{InteriorT}\left(x, y\right) \Rightarrow \operatorname{F}\left(x\right)\le\operatorname{F}\left(y\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/PoissonBinomial/ConfigurationalEntropyStep.F_le_interiorT` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* D. Monkman; J. Sirker (2023). *Symmetry-resolved entanglement: general considerations, calculation from correlation functions, and bounds for symmetry-protected topological phases*. DOI: [10.48550/arXiv.2307.05820](https://doi.org/10.48550/arXiv.2307.05820). URL: <https://arxiv.org/abs/2307.05820>.

*Commentary.*

For two distinct coordinates p at least q, move them to p-s and q+s. The other coordinates give a normalized Poisson-binomial law supported through M-2. Removing the pair expresses the full law as its three-point convolution.

At an interior pair p>q, write A=p(1−q) and B=q(1−p), so A−B=p−q. The derivative of F in the smoothing direction factors as (p−q)[(log A−log B)/(A−B)−d], where d is the entropy derivative of the three-point convolution in direction (1,−2,1). The binary part is controlled by the logarithmic bound A1; the convolution part satisfies d≤−log(AB).

The entropy-direction bound for the convolution and the logarithmic divided-difference bound show that the derivative of F is nonnegative up to the midpoint. At equal coordinates the derivative is zero. Coordinate permutation invariance handles steps beyond the midpoint. No strictness or equality characterization is asserted.

## References

- Truth anchor: `D5/S3/Entropy/PoissonBinomial/ConfigurationalEntropyStep.F_le_interiorT`
- Truth anchor: `D5/S3/Entropy/PoissonBinomial/ConfigurationalEntropyStep.continuous_F`
- Dependency: [D5/S3/Entropy/PoissonBinomial/EntropyDirectionBounds](EntropyDirectionBounds.md)
- Dependency: [D5/S3/Entropy/PoissonBinomial/PoissonBinomialStructure](PoissonBinomialStructure.md)
- Dependency: [D5/S3/Geometry/AlphaGeometry/CubeRootSpectralMonotonicity](../../Geometry/AlphaGeometry/CubeRootSpectralMonotonicity.md)
