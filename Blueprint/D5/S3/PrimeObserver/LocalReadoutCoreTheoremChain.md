# The Local-Readout Core Theorem Chain

## Abstract

Joint kernels, finite certificates, and CRT phase periods form one theorem chain.

**Theorem 1.1 (Separation, certification, and crossing periods).**

$$JointFaithfulnessTFAE \land {LGResEmpty \iff JointInjective} \land FiniteCertificate \land {m \neq 0 \implies PhasePeriod = PrimePowerPeriodLcm} \land ZeroModulusCounterexample \land FirstReturnSix.$$

*Proof.* Machine-checked in Lean as `D5/S3/PrimeObserver/LocalReadoutCoreTheoremChain.local_readout_core_theorem_chain` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Joint injectivity, point separation, and diagonal kernel intersection are equivalent, and residual emptiness is the same condition.

A finite operational quotient admits a finite distinguishing certificate even when the available protocol family is infinite.

For a nonzero modulus the crossing phase period is the least common multiple of its prime-power periods; zero is an explicit counterexample, while the sandwich phase first returns at six.

## References

- Truth anchor: `D5/S3/PrimeObserver/LocalReadoutCoreTheoremChain.local_readout_core_theorem_chain`
- Dependency: [D5/S3/ConceptDynamics/Faithfulness/LocalGlobalResidualCriterion](../ConceptDynamics/Faithfulness/LocalGlobalResidualCriterion.md)
- Dependency: [D5/S3/Factorization/Periods/CrtPeriodComposition](../Factorization/Periods/CrtPeriodComposition.md)
- Dependency: [D5/S3/ObserverMemory/PredictionCertificates/FiniteDistinguishingCertificate](../ObserverMemory/PredictionCertificates/FiniteDistinguishingCertificate.md)
- Dependency: [D5/S3/PrimeForms/CrossingPeriodicity/SandwichPhasePeriod](../PrimeForms/CrossingPeriodicity/SandwichPhasePeriod.md)
