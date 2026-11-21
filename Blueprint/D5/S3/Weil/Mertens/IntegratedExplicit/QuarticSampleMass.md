# Prime windows and discrete sample mass

## Abstract

Weighted fourth-power samples and the Riemann hypothesis

Let U be the integrated complete Mangoldt remainder CompleteMertensPeak.U. For natural numbers a ≤ b, let S(a,b) be the sum of max(U(n⁴),0)/n³ over all natural n from a through b. The positive part is taken before summing. Let w(n) be this sample weight, with w(0) = 0. The prime-only mass P(a,b) is the integral of max(−Q(x),0)/√x from a⁴ to b⁴, with Q the Chebyshev tail PrimeOnlyTailCorrection.primeTail.

**Theorem 1.1 (Prime-only mass is controlled by the fourth-power samples).**

$$\exists C \in \mathbb{R},\; 0 \le C \land \left(\forall a \in \mathbb{N},\; \forall b \in \mathbb{N},\; \left(2 \le a \land a \le b\right) \Rightarrow \operatorname{P}\left(a, b\right)+15\operatorname{w}\left(b\right) \le 135\operatorname{S}\left(a, b\right)+C(\operatorname{log}\left(b\right)-\operatorname{log}\left(a\right))\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/QuarticSampleMass.prime_mass_le_samples` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a ≥ 2, the prime-only mass plus 15 w(b) is at most 135 S(a,b) plus a uniform nonnegative constant times log b−log a. Between n⁴ and (n+1)⁴ the Mangoldt ramp sum lies below its endpoint chord. The centering error is at most 225n², the cell has length at most 15n³, and x√x is at least n⁶. These estimates bound the complete mass of each cell by 15 times the left sample weight, 120 times the right sample weight, and 3375/n.

Summing cells assigns coefficient at most 135 to each sample weight and keeps the terminal correction 15 w(b) on the left. The errors telescope against the logarithm using 1/n ≤ 2(log(n+1)−log n). The prime-power correction adds another uniform multiple of log b−log a. The restriction a ≥ 2 places the interval in the domain of the complete Chebyshev tail identity.

**Theorem 1.2 (A harmonic upper bound under RH).**

$$RiemannHypothesis \Rightarrow \left(\exists N \in \mathbb{N},\; \forall a \in \mathbb{N},\; N \le a \Rightarrow \left(\forall b \in \mathbb{N},\; a \le b \Rightarrow \operatorname{S}\left(a, b\right) < \frac{1}{a}+\operatorname{log}\left(b\right)-\operatorname{log}\left(a\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/QuarticSampleMass.eventual_logarithmic_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under RH, S(a,b) < 1/a + log b−log a for every sufficiently large a and all b ≥ a. The strict quartic sample estimate puts each sufficiently late sample weight below 1/n. The left endpoint contributes strictly less than 1/a. Each subsequent reciprocal is at most the logarithmic increment from the previous integer.

**Theorem 1.3 (A right-of-line zero forces eventual power growth).**

$$\forall z \in \mathbb{C},\; \left(\operatorname{zeta}\left(z\right) = 0 \land \frac{1}{2} < \operatorname{Re}\left(z\right)\right) \Rightarrow \left(\forall e \in \mathbb{R},\; 0 < e \Rightarrow \left(\exists N \in \mathbb{N},\; \forall k \in \mathbb{N},\; N \le k \Rightarrow k^{16(\operatorname{Re}\left(z\right)-\frac{1}{2})-e} \le \operatorname{S}\left(k^{3}, k^{4}\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/QuarticSampleMass.off_line_zero_forces_sample_mass` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a zeta zero z with Re z > 1/2 and any positive loss ε, S(k³,k⁴) is at least k to the power 16(Re z−1/2)−ε for all sufficiently large natural k. The prime-only lower bound on [k¹²,k¹⁶] gives the factor 16. Part of the exponent loss absorbs both the factor 135 and the logarithmic error in the sample comparison.

**Theorem 1.4 (RH is equivalent to cofinal subpower sample mass).**

$$RiemannHypothesis \Leftrightarrow \left(\forall e \in \mathbb{R},\; 0 < e \Rightarrow \left(\forall A \in \mathbb{N},\; \exists k \in \mathbb{N},\; \operatorname{max}\left(A, 2\right) \le k \land \operatorname{S}\left(k^{3}, k^{4}\right) \le k^{e}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/QuarticSampleMass.rh_iff_subpower_sample_mass` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive η and every natural threshold A, the condition asks for a natural k ≥ max(A,2) with S(k³,k⁴) ≤ k raised to η. Under RH the block bound 1/k³ + log k eventually lies below any positive power of k. Conversely, each right-of-line zero forces eventual growth above some positive power of k, ruling out cofinally many blocks below that power. Excluding those zeros in the right half of the critical strip gives RH.

The subpower condition controls a sum and allows isolated large samples. An unconditional estimate of this sum on cofinally many blocks would therefore prove RH.

## References

- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/QuarticSampleMass.eventual_logarithmic_bound`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/QuarticSampleMass.off_line_zero_forces_sample_mass`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/QuarticSampleMass.prime_mass_le_samples`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/QuarticSampleMass.rh_iff_subpower_sample_mass`
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/PrimeWindowPoleGrowth](PrimeWindowPoleGrowth.md)
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/QuarticSampling](QuarticSampling.md)
