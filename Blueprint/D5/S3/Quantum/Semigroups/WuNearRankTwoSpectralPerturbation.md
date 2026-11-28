# Near-rank-two spectral perturbation

## Abstract

Conditional near-rank-two spectral perturbation for the unequal-temperature cubic Gibbs deficit.

The product Gibbs eigenvalue at occupation o is occupationWeight(r,o.1) occupationWeight(R,o.2), with occupation order 00, 01, 10, 11. The Gibbs log field averages these four logarithms against the nonnegative frame weights p(i,o) whose sum is one.

**Theorem 1.1 (Product Gibbs eigenvalue bounds).**

Lean statement: `D5/S3/Quantum/Semigroups/WuNearRankTwoSpectralPerturbation.gibbsEigenvalue_bounds`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuNearRankTwoSpectralPerturbation.gibbsEigenvalue_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

For R,r ≥ 1 every product Gibbs eigenvalue lies between a(r)a(R) and b(r)b(R), and the corresponding Gibbs log field lies between the logarithms of those endpoints.

**Theorem 1.2 (Two-root raising loss).**

Lean statement: `D5/S3/Quantum/Semigroups/WuNearRankTwoSpectralPerturbation.deficit_two_root_loss`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuNearRankTwoSpectralPerturbation.deficit_two_root_loss` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

At the tracial spectator, replacing zero roots by values at most ε costs at most 9 ε in the deficit when ε³ ≤ 1/(2(1+R³)). The estimate includes the cubic energy loss and the entropy sign from adding mass below the least Gibbs eigenvalue.

**Theorem 1.3 (Temperature variation).**

Lean statement: `D5/S3/Quantum/Semigroups/WuNearRankTwoSpectralPerturbation.deficit_temperature_change`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuNearRankTwoSpectralPerturbation.deficit_temperature_change` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

At fixed roots and fixed frame, changing the spectator ratio from 1 to r changes the deficit by at most 26 log r. The 26 comes from the energy bound 8 log r and the entropy bound 12 log r multiplied by alpha(R) ≤ 3/4.

**Theorem 1.4 (Combined perturbation lower bound).**

Lean statement: `D5/S3/Quantum/Semigroups/WuNearRankTwoSpectralPerturbation.near_rank_two_deficit_lower`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuNearRankTwoSpectralPerturbation.near_rank_two_deficit_lower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

The two-root and temperature estimates combine to deficit(R,1,...,v₀) − 9ε − 26 log r ≤ deficit(R,r,...,v).

**Theorem 1.5 (Conditional strict rank-two margin transfer).**

Lean statement: `D5/S3/Quantum/Semigroups/WuNearRankTwoSpectralPerturbation.near_rank_two_unequal_temperature`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuNearRankTwoSpectralPerturbation.near_rank_two_unequal_temperature` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

For 1 < R, r ∈ [1,R], 0 ≤ u ≤ v ≤ m ≤ 1, v ≤ ε, ε ≤ min(rankTwoMargin(R)/36, (2(1+R³))^(−1/3)), and log r ≤ rankTwoMargin(R)/104, assume the strict tracial baseline hypothesis hbase: rankTwoMargin(R) · mass ![0,0,m,1] < deficit(R,1,cold,spectator,p,![0,0,m,1]). Then the actual conclusion is rankTwoMargin(R)/2 < deficit(R,r,cold,spectator,p,![u,v,m,1]). The mass factor remains in the hypothesis and is used to convert it to the strict unit-margin baseline.

**Theorem 1.6 (Cubic scaling restoration).**

Lean statement: `D5/S3/Quantum/Semigroups/WuNearRankTwoSpectralPerturbation.deficit_scale`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuNearRankTwoSpectralPerturbation.deficit_scale` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

For h > 0, scaling every spectral root by h scales the deficit by h³, restoring arbitrary positive largest roots from the normalized theorem.

## References

- Truth anchor: `D5/S3/Quantum/Semigroups/WuNearRankTwoSpectralPerturbation.deficit_scale`
- Truth anchor: `D5/S3/Quantum/Semigroups/WuNearRankTwoSpectralPerturbation.deficit_temperature_change`
- Truth anchor: `D5/S3/Quantum/Semigroups/WuNearRankTwoSpectralPerturbation.deficit_two_root_loss`
- Truth anchor: `D5/S3/Quantum/Semigroups/WuNearRankTwoSpectralPerturbation.gibbsEigenvalue_bounds`
- Truth anchor: `D5/S3/Quantum/Semigroups/WuNearRankTwoSpectralPerturbation.near_rank_two_deficit_lower`
- Truth anchor: `D5/S3/Quantum/Semigroups/WuNearRankTwoSpectralPerturbation.near_rank_two_unequal_temperature`
- Dependency: [D5/S3/Quantum/Semigroups/WuCubicThermalBasis](WuCubicThermalBasis.md)
