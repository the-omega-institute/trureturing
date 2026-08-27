# Weak Prime Evidence Has Finite Total

## Abstract

Prime-indexed weak Bernoulli coordinates have positive, vanishing, summable negative-log affinity evidence.

**Theorem 1.1 (Infinitely many weak coordinates can have finite total evidence).**

$${\forall p: \operatorname{NatPrimes}, 0 < -\log(\operatorname{bhattacharyya}\left(\operatorname{positiveBiasLaw}\left(p^{{-2}}\right), \operatorname{negativeBiasLaw}\left(p^{{-2}}\right)\right))} \land \left(Summable\left((p \mapsto -\log(\operatorname{bhattacharyya}\left(\operatorname{positiveBiasLaw}\left(p^{{-2}}\right), \operatorname{negativeBiasLaw}\left(p^{{-2}}\right)\right)))\right) \land \operatorname{Tendsto}\left((p \mapsto -\log(\operatorname{bhattacharyya}\left(\operatorname{positiveBiasLaw}\left(p^{{-2}}\right), \operatorname{negativeBiasLaw}\left(p^{{-2}}\right)\right))), cofinite, \operatorname{nhds}\left(0\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/TotalVariation/Asymptotics/WeakPrimeEvidenceFiniteTotal.weak_prime_evidence_finite_total` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each prime p, take the canonical symmetric Bernoulli pair with opposite biases p to the power minus two. Its Bhattacharyya affinity is strictly below one, so its negative logarithm is positive.

The frozen second-order expansion bounds the remainder by a constant multiple of p to the power minus eight. The leading term is a multiple of p to the power minus four. Both prime-power series are summable, and summability also forces the evidence terms to vanish along the cofinite filter.

## References

- Truth anchor: `D5/S3/TotalVariation/Asymptotics/WeakPrimeEvidenceFiniteTotal.weak_prime_evidence_finite_total`
- Dependency: [D5/S3/TotalVariation/Asymptotics/FourLocalEvidenceClosedForms](FourLocalEvidenceClosedForms.md)
