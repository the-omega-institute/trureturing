# The Increasing Tail Family

## Abstract

A maximal first letter followed by an increasing tail gives an explicit eligible parameter.

**Definition 1.1 (A maximum followed by an increasing tail).**

Lean statement: `D5/S3/Combinatorics/FundamentalBijection/ThetaIterateUFamilies.U`

*Formalization.* `D5/S3/Combinatorics/FundamentalBijection/ThetaIterateUFamilies.U` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Kassie Archer, Robert P. Laudone (2024). *Pattern avoidance and the fundamental bijection*. DOI: [10.48550/arXiv.2407.06338](https://doi.org/10.48550/arXiv.2407.06338). URL: <https://arxiv.org/abs/2407.06338v1>.

*Commentary.*

The word U(h) is h followed by one through h minus one.

**Theorem 1.2 (Images and characterization of the increasing tail).**

Lean statement: `D5/S3/Combinatorics/FundamentalBijection/ThetaIterateUFamilies.U_family`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/FundamentalBijection/ThetaIterateUFamilies.U_family` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kassie Archer, Robert P. Laudone (2024). *Pattern avoidance and the fundamental bijection*. DOI: [10.48550/arXiv.2407.06338](https://doi.org/10.48550/arXiv.2407.06338). URL: <https://arxiv.org/abs/2407.06338v1>.

*Commentary.*

For h at least four, U(h) permutes one through h, its fundamental image is decreasing, its successor word is three through h followed by one and two, and its cycle from h equals its fundamental image. Among first-maximum parameters whose second letter is at most h minus two, the P construction avoids 132 through depth two exactly for U(h).

## References

- Truth anchor: `D5/S3/Combinatorics/FundamentalBijection/ThetaIterateUFamilies.U`
- Truth anchor: `D5/S3/Combinatorics/FundamentalBijection/ThetaIterateUFamilies.U_family`
- Dependency: [D5/S3/Combinatorics/FundamentalBijection/ThetaIterateCycleReduction](ThetaIterateCycleReduction.md)
- Dependency: [D5/S3/Combinatorics/FundamentalBijection/ThetaIterateFirstEndpoint](ThetaIterateFirstEndpoint.md)
- Dependency: [D5/S3/Combinatorics/FundamentalBijection/ThetaIterateFirstScan](ThetaIterateFirstScan.md)
