# Signed cubic transfer to a raised middle level

## Abstract

The exact signed transfer of Wu’s normalized cubic deficit with both physical squares retained.

Use the two-mode cubic normalization of Wu v1, Remark 3.15, equations (3.54)–(3.55), with r = exp(β/3). For r ≥ 1 and 0 ≤ m ≤ n ≤ q ≤ 1, use the same complex frame U with UᴴU = I and UUᴴ = I for (m, n, n, 1) and (m, n, q, 1). The jump weight Wᵢⱼ runs from source column j to target row i, with columns numbered from zero.

**Theorem 1.1 (Exact signed increment).**

Lean statement: `D5/S3/Quantum/Semigroups/WuCubicSignedTransfer.signed_increment`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuCubicSignedTransfer.signed_increment` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

Put T(z) = m³ + n³ + z³ + 1 and let R₂ be the occupation imbalance of column 2. The scalar change I is (h + bias·R₂)(q³ − n³) + α[T(q) log(T(q)/4) − T(n) log(T(n)/4) − q³ log(q³) + n³ log(n³)], with the Gibbs coefficients at r and 0 log 0 = 0. For g(v,w) = c(v − w)²(v + w) + e(v − w)³, the gain P sums the four weighted increases in g from raising column 2 against columns 0 and 1, in both directions. The deficit changes by I + P − d₊W₃₂ − d₋W₂₃, where d₊ = g(1,n) − g(1,q) and d₋ = g(n,1) − g(q,1). P, d₊ and d₋ are nonnegative. In the occupation frame at (r,m,n,q) = (6/5,16/25,4/5,81/100), W₃₂ = 0 and W₂₃ = 1, and the measured loss is 983727/136400000.

**Theorem 1.2 (Transferred lower bound with both physical squares).**

Lean statement: `D5/S3/Quantum/Semigroups/WuCubicSignedTransfer.raised_lower_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuCubicSignedTransfer.raised_lower_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

Let L be γr·holder21 + γr²·holder12 + frameRemainder at the repeated-middle spectrum, with γ = 9/[4(1 + r³)]. WuOneModeCubic supplies the one-mode premise of this bound at every r ≥ 1. For u = U.col 3 and v = U.col 2 put A = (d₊ + d₋)/2 and ρ = (d₊ − d₋)/(d₊ + d₋). The new deficit is at least L + I + P − A(1 + ρRᵤ)(1 − ρRᵥ) + A(2 − ρ²)|η|²/4 + A|σ + ρτ|². The weighted identity in WuPhysicalHighHigh gives this exact rewrite of the subtracted loss using the imbalances and the parity and conjugate-twist pairings of u and v. The last three terms vanish when A = 0 under Lean’s real division convention.

**Theorem 1.3 (Strict deficit bound on the raised-middle rectangle).**

Lean statement: `D5/S3/Quantum/Semigroups/WuCubicSignedTransfer.source_deficit_rectangle`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuCubicSignedTransfer.source_deficit_rectangle` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

For every frame U with UᴴU = I and UUᴴ = I, the normalized deficit at (m, n, q, 1) exceeds 1/200 whenever 6/5 ≤ r ≤ 5/4, 23/50 ≤ m ≤ 1/2, 9/10 ≤ n ≤ 23/25, and n ≤ q ≤ n + 1/40. The proof transfers the repeated-middle estimate and uses W₃₂ + W₂₃ ≤ 1 to bound the total loss by (189/400)(q − n).

## References

- Truth anchor: `D5/S3/Quantum/Semigroups/WuCubicSignedTransfer.raised_lower_bound`
- Truth anchor: `D5/S3/Quantum/Semigroups/WuCubicSignedTransfer.signed_increment`
- Truth anchor: `D5/S3/Quantum/Semigroups/WuCubicSignedTransfer.source_deficit_rectangle`
- Dependency: [D5/S3/Quantum/Semigroups/WuOneModeCubic](WuOneModeCubic.md)
- Dependency: [D5/S3/Quantum/Semigroups/WuPhysicalHighHigh](WuPhysicalHighHigh.md)
