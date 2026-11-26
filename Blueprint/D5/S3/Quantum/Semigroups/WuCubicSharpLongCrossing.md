# Sharp singleton-pair crossing

## Abstract

A sharp lower bound for the symmetric crossing of two columns in the signed two-mode CAR frame.

In occupation order, the two jumps are E₀₂+E₁₃ and −E₀₁+E₂₃. For wᵢⱼ, column ψⱼ is the source and column ψᵢ is the target. The weight is the sum over the two jumps of |⟨ψᵢ,Jψⱼ⟩|². Write W = wᵢⱼ+wⱼᵢ, and let t and s be the odd masses in coordinates 1 and 2 of ψᵢ and ψⱼ, respectively. The angular certificate applies both bounds to columns 0 and 3 in the equal-cap cubic proof of Wu v1 (3.54).

**Theorem 1.1 (Radical lower bound).**

Lean statement: `D5/S3/Quantum/Semigroups/WuCubicSharpLongCrossing.singletonPairWeight_ge_radical`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuCubicSharpLongCrossing.singletonPairWeight_ge_radical` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

Set P = √((1−t)s) and Q = √(t(1−s)). For x = ψᵢ and y = ψⱼ, the even and odd minors are E = x₀y₃−x₃y₀ and O = x₁y₂−x₂y₁. Adding both directed weights gives W = P²+Q²+2 Re(conj(E)O). Complex Cauchy–Schwarz in the two sectors gives |E|² ≤ (1−t)(1−s) and |O|² ≤ ts. Consequently Re(conj(E)O) ≥ −|E||O| ≥ −PQ, so W ≥ (P−Q)².

**Theorem 1.2 (Division-free product bound).**

Lean statement: `D5/S3/Quantum/Semigroups/WuCubicSharpLongCrossing.singletonPairWeight_ge_product`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuCubicSharpLongCrossing.singletonPairWeight_ge_product` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

Since P²−Q² = s−t and (P+Q)² ≤ 2(P²+Q²) ≤ 2(t+s), the radical bound implies 2(t+s)W ≥ (t−s)². At t+s = 0 both masses and both sides are zero.

**Theorem 1.3 (Attaining unitary columns).**

Lean statement: `D5/S3/Quantum/Semigroups/WuCubicSharpLongCrossing.singletonPairWeight_radical_attained`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuCubicSharpLongCrossing.singletonPairWeight_radical_attained` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

For any t,s ∈ [0,1], take columns 0 and 1 to be √(1−t)e₀+√t e₁ and √(1−s)e₃−√s e₂. Complete them with −√t e₀+√(1−t)e₁ and √(1−s)e₂+√s e₃ in the same two coordinate planes. The resulting real orthonormal frame is unitary and has the prescribed odd masses. The relative minus sign produces the amplitude Q−P from column 1 to column 0 under the first jump. The other amplitude and both reverse amplitudes vanish, giving W = (P−Q)².

## References

- Truth anchor: `D5/S3/Quantum/Semigroups/WuCubicSharpLongCrossing.singletonPairWeight_ge_product`
- Truth anchor: `D5/S3/Quantum/Semigroups/WuCubicSharpLongCrossing.singletonPairWeight_ge_radical`
- Truth anchor: `D5/S3/Quantum/Semigroups/WuCubicSharpLongCrossing.singletonPairWeight_radical_attained`
- Dependency: [D5/S3/Quantum/Semigroups/WuCubicRankTwoCut](WuCubicRankTwoCut.md)
