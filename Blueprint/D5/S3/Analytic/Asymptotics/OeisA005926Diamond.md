# Vaclav Kotesovec’s summatory conjecture for OEIS A005926

## Abstract

The summatory function of the diamond theta coefficients has leading constant π/48.

**Definition 1.1 (The diamond theta series).**

Lean statement: `D5/S3/Analytic/Asymptotics/OeisA005926Diamond.thetaSeries`

*Formalization.* `D5/S3/Analytic/Asymptotics/OeisA005926Diamond.thetaSeries` (`✓ std3`).

*Citation.* Andrew J. Morris (2026). *Generating function for OEIS A005926*. URL: <https://oeis.org/A005926/internal>.

*Commentary.*

For T(j) = j(j+1)/2, ψ(X) is the formal series with a unit monomial in each degree T(j). Over the integers, the source series is X³(ψ(X⁸)³ + ψ(−X⁸)³). Its coefficient of degree k is a(k). The substitutions use PowerSeries.expand and PowerSeries.rescale.

**Theorem 1.2 (The exact coefficient as a lattice shell).**

Lean statement: `D5/S3/Analytic/Asymptotics/OeisA005926Diamond.theta_coefficient_lattice`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Asymptotics/OeisA005926Diamond.theta_coefficient_lattice` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Vaclav Kotesovec (2026). *Summatory conjecture for OEIS A005926*. URL: <https://oeis.org/A005926/internal>.

*Commentary.*

For each degree k, a(k) is twice the number of ordered integer triples z with ∑ᵢ(4zᵢ+1)² = k and ∑ᵢ zᵢ even. Cauchy products allow each ψ factor to be truncated at triangular indices j ≤ k for this coefficient. The two cubes give weight 1 + (−1)^(T(j₁)+T(j₂)+T(j₃)), which is two for even triangular sum and zero for odd triangular sum. The bijection from integer z to natural j uses j = 2z for z ≥ 0 and j = −2z−1 for z < 0. It gives T(j) = 2z²+z and preserves the required parity.

**Theorem 1.3 (The exact sum through N).**

Lean statement: `D5/S3/Analytic/Asymptotics/OeisA005926Diamond.theta_inclusive_cutoff`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Asymptotics/OeisA005926Diamond.theta_inclusive_cutoff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Vaclav Kotesovec (2026). *Summatory conjecture for OEIS A005926*. URL: <https://oeis.org/A005926/internal>.

*Commentary.*

The shift by three gives a(k)=0 for k<3. Summing the shells for 1 ≤ k ≤ N gives twice the number of ordered integer triples with even coordinate sum and ∑ᵢ(4zᵢ+1)² ≤ N. At N=0 the interval and the lattice region both give zero.

**Theorem 1.4 (The normalized sums tend to π/48).**

$$\lim_{N \to \infty} \frac{\sum_{k=1}^{N} a\left(k\right)}{N^{\frac{3}{2}}} = \frac{\pi}{48}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Asymptotics/OeisA005926Diamond.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a005926-diamond-summatory-asymptotic` (proved) by `D5/S3/Analytic/Asymptotics/OeisA005926Diamond.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a005926-diamond-summatory-asymptotic","declaration_gid":"D5/S3/Analytic/Asymptotics/OeisA005926Diamond.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Vaclav Kotesovec (2026). *Summatory conjecture for OEIS A005926*. URL: <https://oeis.org/A005926/internal>.

*Commentary.*

Vaclav Kotesovec stated the conjecture in OEIS A005926 revision 49 on November 26, 2026. The parity condition partitions the triples into the four residue classes 000, 011, 101, and 110 modulo two. In the squared-norm coordinates these give four translates of the lattice of spacing eight. Each class is counted by a shifted closed ball of radius √N/8, so division by N^(3/2) contributes (4π/3)/8³ per class. The four classes and weight two give π/48 for natural N tending to infinity through all cutoffs.

## References

- Truth anchor: `D5/S3/Analytic/Asymptotics/OeisA005926Diamond.result`
- Truth anchor: `D5/S3/Analytic/Asymptotics/OeisA005926Diamond.thetaSeries`
- Truth anchor: `D5/S3/Analytic/Asymptotics/OeisA005926Diamond.theta_coefficient_lattice`
- Truth anchor: `D5/S3/Analytic/Asymptotics/OeisA005926Diamond.theta_inclusive_cutoff`
- Dependency: [D5/S3/Arith/Lattices/Counting/ShiftedBallCount](../../Arith/Lattices/Counting/ShiftedBallCount.md)
