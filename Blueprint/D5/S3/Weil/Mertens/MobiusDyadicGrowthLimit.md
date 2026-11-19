# Logarithmic growth of the signed Möbius shell energies

## Abstract

The cumulative limit and individual limsup for the signed Möbius shell energies.

In MobiusPartialSumL2Divergence, mobiusPartialSum(x) is the real sum of μ(n)/n over the natural numbers from 1 through the natural floor of x, inclusive. The function MobiusDyadicEnergy.mobiusDyadicDifference(x) is mobiusPartialSum(x) minus mobiusPartialSum(2x). For each natural k, write E(k) for mobiusDyadicShellEnergy(k), the real integral of the square of that difference against Lebesgue measure on (2^k, 2^(k+1)].

Write θ for KappaGap.zeroAbscissa, the real supremum of the real parts of the complex ρ satisfying riemannZeta(ρ) = 0 and 0 < Re(ρ) < 1. These are exactly the zeros selected by ZeroSum.IsNontrivialZero. The logarithms are natural logarithms. Both sequences are defined on all natural indices, and Nat.cast sends the index to ℝ in the denominator. At index zero the quotient equals zero by Lean's real division convention.

**Theorem 1.1 (Cumulative shell growth limit).**

$$\operatorname{Filter.Tendsto}\left((\lambda N: \mathbb{N} \mapsto \frac{\operatorname{log}\left(1 + \sum_{k \in \operatorname{Finset.range}\left(N\right)} E\left(k\right)\right)}{\operatorname{Nat.cast}\left(N\right) \cdot \operatorname{log}\left(2\right)}), \operatorname{Filter.atTop}_{\mathbb{N}}, \operatorname{nhds}\left(2 \cdot \theta - 1\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/MobiusDyadicGrowthLimit.tendsto_log_one_add_sum_mobiusDyadicShellEnergy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The prefix sum ranges over exactly the natural indices k with 0 ≤ k < N. The displayed convergence means that for every real ε > 0 there is a natural N₀ such that for every natural N ≥ N₀ the absolute difference between the quotient and 2θ − 1 is less than ε.

Every nontrivial zero with real part above 1/2 gives an eventual exponential lower bound for the finite shell sum via the signed energy theorem. For θ < 1, the normalized shell convergence for any exponent between 2θ − 1 and 1 bounds each shell by a geometric sequence. At θ = 1 the elementary bound E(k) ≤ 4·2^k gives the upper exponent. The two estimates give the cumulative limit.

**Theorem 1.2 (Individual shell growth limsup).**

$$\operatorname{Filter.limsup}\left((\lambda k: \mathbb{N} \mapsto \frac{\operatorname{log}\left(1 + E\left(k\right)\right)}{\operatorname{Nat.cast}\left(k\right) \cdot \operatorname{log}\left(2\right)}), \operatorname{Filter.atTop}_{\mathbb{N}}\right) = 2 \cdot \theta - 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/MobiusDyadicGrowthLimit.limsup_log_one_add_mobiusDyadicShellEnergy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real ε > 0 the individual quotient is less than 2θ − 1 + ε at all sufficiently large natural k. For every real ε > 0 and every natural K there is a natural k ≥ K where it exceeds 2θ − 1 − ε.

The nonnegative shells bound the individual numerator by the prefix numerator through k, using the same denominator at k. An eventual upper bound for the individual quotient strictly below 2θ − 1 would give a geometric bound for the prefix sum and contradict the cumulative limit.

## References

- Truth anchor: `D5/S3/Weil/Mertens/MobiusDyadicGrowthLimit.limsup_log_one_add_mobiusDyadicShellEnergy`
- Truth anchor: `D5/S3/Weil/Mertens/MobiusDyadicGrowthLimit.tendsto_log_one_add_sum_mobiusDyadicShellEnergy`
- Dependency: [D5/S3/Arith/MoebiusLogarithmic/ReciprocalBound](../../Arith/MoebiusLogarithmic/ReciprocalBound.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/KappaGap](../../Arith/Robin/ForwardKernel/KappaGap.md)
- Dependency: [D5/S3/Weil/Mertens/MobiusDyadicEnergy](MobiusDyadicEnergy.md)
- Dependency: [D5/S3/Weil/ZeroData/UnconditionalCanonicalZeroData](../ZeroData/UnconditionalCanonicalZeroData.md)
- Dependency: [D5/S3/Weil/ZetaPntBounds/MobiusPartialSumL2Divergence](../ZetaPntBounds/MobiusPartialSumL2Divergence.md)
