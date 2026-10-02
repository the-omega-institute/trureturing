# Reduction along the Distinguished Cycle

## Abstract

The first two fundamental images of the distinguished cycle reduce avoidance to conditions on the parameter.

**Theorem 1.1 (Images and avoidance of the cycle family).**

Lean statement: `D5/S3/Combinatorics/FundamentalBijection/ThetaIterateCycleReduction.P_cycle_reduction`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/FundamentalBijection/ThetaIterateCycleReduction.P_cycle_reduction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kassie Archer, Robert P. Laudone (2024). *Pattern avoidance and the fundamental bijection*. DOI: [10.48550/arXiv.2407.06338](https://doi.org/10.48550/arXiv.2407.06338). URL: <https://arxiv.org/abs/2407.06338v1>.

*Commentary.*

For a nonempty parameter permutation r of length h, the first image of P(r) is h plus two followed by r increased by one and then one, and the second image is the fundamental image of r increased by one followed by h plus two and one. Avoidance through the second iterate is equivalent to 132-avoidance of r, its fundamental image and b(r), together with the absence of an increasing positional pair in b(r) straddling the first value of r plus one. The first and last values of P(r) are h plus two and the first value of r plus one, and its values at positions labelled by r are the corresponding shifted successors.

## References

- Truth anchor: `D5/S3/Combinatorics/FundamentalBijection/ThetaIterateCycleReduction.P_cycle_reduction`
- Dependency: [D5/S3/Combinatorics/FundamentalBijection/ThetaBasicInverseBlocks](ThetaBasicInverseBlocks.md)
- Dependency: [D5/S3/Combinatorics/FundamentalBijection/ThetaBasicInverseGeneral](ThetaBasicInverseGeneral.md)
- Dependency: [D5/S3/Combinatorics/FundamentalBijection/ThetaIterateCycle](ThetaIterateCycle.md)
- Dependency: [D5/S3/Combinatorics/FundamentalBijection/ThetaIterateDefs](ThetaIterateDefs.md)
