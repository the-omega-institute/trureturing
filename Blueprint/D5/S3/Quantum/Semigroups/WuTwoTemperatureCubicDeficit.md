# Physical two-temperature cubic deficit

## Abstract

The physical two-temperature cubic deficit and its conditional same-frame margin.

In the unitary frame U, write M = U diag(v) Uᴴ for the matrix of spectral roots. The product Gibbs matrix D(R,r) uses ratio r on the left mode and R on the right. Its positive sixth root G defines the Gibbs sandwich with X = GInv M GInv.

**Theorem 1.1 (Gibbs overlap row normalization).**

Lean statement: `D5/S3/Quantum/Semigroups/WuTwoTemperatureCubicDeficit.referenceProb_sum`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuTwoTemperatureCubicDeficit.referenceProb_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

The row indexed by spectral column i consists of the nonnegative occupation weights referenceProb(U,i,o) = |Uₒᵢ|². The i-th diagonal entry of UᴴU = I gives ∑ₒ referenceProb(U,i,o) = 1.

**Theorem 1.2 (CAR jump weight normalization).**

Lean statement: `D5/S3/Quantum/Semigroups/WuTwoTemperatureCubicDeficit.weight_sum`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuTwoTemperatureCubicDeficit.weight_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

For each jump Jⱼ, the nonnegative weights weight(U,j,i,k) = |(Uᴴ Jⱼ U)ᵢₖ|² sum to 2 over i and k. Unitarity identifies the sum with Re Tr(Jⱼᴴ Jⱼ), and the CAR identity Jⱼ Jⱼᴴ + Jⱼᴴ Jⱼ = I in dimension four gives twice this trace equal to 4.

**Theorem 1.3 (Entropy trace identity).**

Lean statement: `D5/S3/Quantum/Semigroups/WuTwoTemperatureCubicDeficit.entropy_eq_operator`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuTwoTemperatureCubicDeficit.entropy_eq_operator` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

The spectral entropy with the Gibbs log field ∑ₒ |Uₒᵢ|² log Dₒₒ equals Re Tr(M³ (cfc Real.log (M³) − cfc Real.log D)) − τ log τ, where τ = Re Tr(M³) = ∑ᵢ vᵢ³. The identity includes zero spectral roots.

**Theorem 1.4 (Physical deficit identity).**

Lean statement: `D5/S3/Quantum/Semigroups/WuTwoTemperatureCubicDeficit.deficit_eq_operator`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuTwoTemperatureCubicDeficit.deficit_eq_operator` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

For R,r > 0, the spectral deficit with the two actual CAR jump weights and the Gibbs overlap rows equals operatorDeficit(R,r,M). Its energy is (9/8) Re Tr(M² G generator(R,r,X) G), and the deficit subtracts alpha(R) times the entropy trace.

**Theorem 1.5 (Conditional same-frame operator margin).**

Lean statement: `D5/S3/Quantum/Semigroups/WuTwoTemperatureCubicDeficit.near_rank_two_operator_deficit`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuTwoTemperatureCubicDeficit.near_rank_two_operator_deficit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

Let δ = rankTwoMargin(R), with 1 < R, r ∈ [1,R], 0 ≤ u ≤ v ≤ m ≤ 1, v ≤ ε, ε ≤ min(δ/36, (2(1+R³))^(−1/3)), and log r ≤ δ/104. In the same unitary frame U, assume the strict tracial rank-two baseline hbase, namely δ · mass ![0,0,m,1] < operatorDeficit(R,1,spectralMatrix(U,![0,0,m,1])), with mass ![0,0,m,1] = m³ + 1. Then δ/2 < operatorDeficit(R,r,spectralMatrix(U,![u,v,m,1])).

## References

- Truth anchor: `D5/S3/Quantum/Semigroups/WuTwoTemperatureCubicDeficit.deficit_eq_operator`
- Truth anchor: `D5/S3/Quantum/Semigroups/WuTwoTemperatureCubicDeficit.entropy_eq_operator`
- Truth anchor: `D5/S3/Quantum/Semigroups/WuTwoTemperatureCubicDeficit.near_rank_two_operator_deficit`
- Truth anchor: `D5/S3/Quantum/Semigroups/WuTwoTemperatureCubicDeficit.referenceProb_sum`
- Truth anchor: `D5/S3/Quantum/Semigroups/WuTwoTemperatureCubicDeficit.weight_sum`
- Dependency: [D5/S3/Quantum/Semigroups/WuNearRankTwoSpectralPerturbation](WuNearRankTwoSpectralPerturbation.md)
- Dependency: [D5/S3/Quantum/Semigroups/WuTwoTemperatureCubicPhysicalBridge](WuTwoTemperatureCubicPhysicalBridge.md)
