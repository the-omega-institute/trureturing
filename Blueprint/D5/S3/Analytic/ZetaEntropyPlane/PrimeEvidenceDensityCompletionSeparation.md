# Prime Count And Evidence Completion Separate

## Abstract

Prime-coordinate count and cumulative evidence have distinct convergence behaviors.

**Theorem 1.1 (Coordinate count does not determine cumulative completion).**

$$\left(\operatorname{Infinite}\left(\operatorname{NatPrimes}\left(\right)\right) \land \left(\left(\forall p \in \operatorname{NatPrimes}\left(\right),\; 0 < -\log(\operatorname{bhattacharyya}\left(\operatorname{positiveBiasLaw}\left(p^{{-2}}\right), \operatorname{negativeBiasLaw}\left(p^{{-2}}\right)\right))\right) \land \left(Summable\left((p \mapsto -\log(\operatorname{bhattacharyya}\left(\operatorname{positiveBiasLaw}\left(p^{{-2}}\right), \operatorname{negativeBiasLaw}\left(p^{{-2}}\right)\right)))\right) \land \operatorname{Tendsto}\left((p \mapsto -\log(\operatorname{bhattacharyya}\left(\operatorname{positiveBiasLaw}\left(p^{{-2}}\right), \operatorname{negativeBiasLaw}\left(p^{{-2}}\right)\right))), cofinite, \operatorname{nhds}\left(0\right)\right)\right)\right)\right) \land \left(\left(\operatorname{Tendsto}\left(naturalCountingRatio\left(primeNaturals\right), atTop, \operatorname{nhds}\left(0\right)\right) \land \neg Summable\left(restrictedPrimeEvidence\left(primeNaturals, 1\right)\right)\right) \land \left(\left(\left(\forall p \in \operatorname{NatPrimes}\left(\right),\; p \in primeNaturals\right) \land Summable\left(restrictedPrimeEvidence\left(primeNaturals, 2\right)\right)\right) \land \left(\operatorname{Tendsto}\left(naturalCountingRatio\left(\emptyset\right), atTop, \operatorname{nhds}\left(0\right)\right) \land Summable\left(restrictedPrimeEvidence\left(\emptyset, 1\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaEntropyPlane/PrimeEvidenceDensityCompletionSeparation.prime_evidence_density_completion_separation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The prime index is infinite, yet the explicit inverse-square weak Bernoulli evidence family is positive, summable, and vanishes along the cofinite filter.

The prime support has zero natural counting ratio while its reciprocal evidence diverges. Full and empty support witnesses then make the density-versus-summability inequivalence explicit.

## References

- Truth anchor: `D5/S3/Analytic/ZetaEntropyPlane/PrimeEvidenceDensityCompletionSeparation.prime_evidence_density_completion_separation`
- Dependency: [D5/S3/Analytic/ZetaEntropyPlane/PrimeDensityEvidenceOrthogonality](PrimeDensityEvidenceOrthogonality.md)
- Dependency: [D5/S3/TotalVariation/Asymptotics/WeakPrimeEvidenceFiniteTotal](../../TotalVariation/Asymptotics/WeakPrimeEvidenceFiniteTotal.md)
