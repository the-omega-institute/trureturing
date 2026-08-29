# Prime Precision Marginal Gain

## Abstract

Each prime-exponent precision layer reveals a geometrically decreasing binary bit.

**Definition 1.1 (Truncated prime readout).**

Lean statement: `D5/S3/Analytic/PrimeProducts/PrimePrecisionMarginalGain.primeTruncatedReadout`

*Formalization.* `D5/S3/Analytic/PrimeProducts/PrimePrecisionMarginalGain.primeTruncatedReadout` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The depth-k readout sends an exponent value to its minimum with k.

**Definition 1.2 (Law of the truncated readout).**

Lean statement: `D5/S3/Analytic/PrimeProducts/PrimePrecisionMarginalGain.primeTruncatedReadoutLaw`

*Formalization.* `D5/S3/Analytic/PrimeProducts/PrimePrecisionMarginalGain.primeTruncatedReadoutLaw` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is the pushforward of the canonical prime-exponent PMF by the truncated readout.

**Definition 1.3 (Entropy of the truncated readout).**

Lean statement: `D5/S3/Analytic/PrimeProducts/PrimePrecisionMarginalGain.primeTruncatedReadoutEntropy`

*Formalization.* `D5/S3/Analytic/PrimeProducts/PrimePrecisionMarginalGain.primeTruncatedReadoutEntropy` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The readout entropy is the countable Shannon entropy of its pushforward law, measured in nats.

**Theorem 1.4 (One precision layer has geometric binary-entropy gain).**

$$\forall s \in \mathbb{R}, p \in \operatorname{Primes}, k \in \mathbb{N},\; 1 < s \Rightarrow primeTruncatedReadoutEntropy\left(s, p, k + 1\right) - primeTruncatedReadoutEntropy\left(s, p, k\right) = (primeEvidence\left(s, p\right))^{k} \cdot binEntropy\left(primeEvidence\left(s, p\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/PrimeProducts/PrimePrecisionMarginalGain.prime_precision_marginal_gain` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix a zeta parameter above one and a prime. The ratio q is the existing primeEvidence value p raised to minus s.

The truncated PMF has the original geometric masses below k and one merged tail mass q^k at k. Splitting that tail at the next depth adds q^k times the binary entropy of q.

**Theorem 1.5 (The first precision layer gains full binary entropy).**

$$primeTruncatedReadoutEntropy\left(s, p, 1\right) - primeTruncatedReadoutEntropy\left(s, p, 0\right) = binEntropy\left(primeEvidence\left(s, p\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/PrimeProducts/PrimePrecisionMarginalGain.first_prime_precision_gain` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At k equal to zero, the geometric prefactor is one.

**Theorem 1.6 (Binary entropy vanishes at both boundary limits).**

$$\operatorname{Tendsto}\left(binEntropy, \operatorname{nhds}\left(0\right), \operatorname{nhds}\left(0\right)\right) \land \operatorname{Tendsto}\left(binEntropy, \operatorname{nhds}\left(1\right), \operatorname{nhds}\left(0\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/PrimeProducts/PrimePrecisionMarginalGain.binary_entropy_boundary_limits` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Continuity and the totalized endpoint values give zero at q approaching zero and at q approaching one.

**Theorem 1.7 (Binary entropy is maximal at one half).**

$$binEntropy\left(\frac{1}{2}\right) = \log\left(2\right) \land \left(\forall q \in \mathbb{R},\; binEntropy\left(q\right) \le \log\left(2\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/PrimeProducts/PrimePrecisionMarginalGain.binary_entropy_half_maximum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At q equal to one half the entropy is log two, its global maximum.

## References

- Truth anchor: `D5/S3/Analytic/PrimeProducts/PrimePrecisionMarginalGain.binary_entropy_boundary_limits`
- Truth anchor: `D5/S3/Analytic/PrimeProducts/PrimePrecisionMarginalGain.binary_entropy_half_maximum`
- Truth anchor: `D5/S3/Analytic/PrimeProducts/PrimePrecisionMarginalGain.first_prime_precision_gain`
- Truth anchor: `D5/S3/Analytic/PrimeProducts/PrimePrecisionMarginalGain.primeTruncatedReadout`
- Truth anchor: `D5/S3/Analytic/PrimeProducts/PrimePrecisionMarginalGain.primeTruncatedReadoutEntropy`
- Truth anchor: `D5/S3/Analytic/PrimeProducts/PrimePrecisionMarginalGain.primeTruncatedReadoutLaw`
- Truth anchor: `D5/S3/Analytic/PrimeProducts/PrimePrecisionMarginalGain.prime_precision_marginal_gain`
- Dependency: [D5/S3/Analytic/ZetaEntropyPlane/PrimeEvidenceSharpThreshold](../ZetaEntropyPlane/PrimeEvidenceSharpThreshold.md)
