# Prime Observer Casimir Complete Monotonicity

## Abstract

The split-prime zero-minus-first regulator mode is completely monotone.

**Theorem 1.1 (Alternating derivatives of the split-prime observer Casimir).**

$$\forall phase \in \operatorname{Nat}() \to \operatorname{Real}(),\; \left(\forall p \in \operatorname{Nat}(), k \in \operatorname{Nat}(),\; \left(\operatorname{Prime}(p) \land \left(0 < k \land \operatorname{IsGoldenSplitPrime}(p)\right)\right) \Rightarrow \operatorname{primeObserverCasimirCoefficient}(phase)\left(\operatorname{pow}(p, k)\right) = \operatorname{ofReal}(\frac{2 \times (1 - \operatorname{cos}(k \times phase\left(p\right)))}{k})\right) \land \left(\left(\forall p \in \operatorname{Nat}(),\; \operatorname{Prime}(p) \Rightarrow \left(\operatorname{IsGoldenSplitPrime}(p) \Leftrightarrow \left(\operatorname{mod}(p, 5) = 1 \lor \operatorname{mod}(p, 5) = 4\right)\right)\right) \land \left(\left(\forall sigma \in \operatorname{Real}(),\; \operatorname{goldenObserverCasimir}(phase)\left(sigma\right) = \operatorname{splitRegulatorModeLog}(phase, 0, sigma) - \operatorname{splitRegulatorModeLog}(phase, 1, sigma)\right) \land \left(\left(\forall m \in \operatorname{Nat}(), sigma \in \operatorname{Real}(),\; 1 < sigma \Rightarrow \operatorname{pow}((-1), m) \times \operatorname{iteratedDeriv}(m, \operatorname{goldenObserverCasimir}(phase), sigma) = \sum_{p \in NatPrimes} \sum_{k \in \mathbb{N}} \begin{cases}\frac{2 \times (1 - \operatorname{cos}((k + 1) \times phase\left(p\right)))}{(k + 1)} \times ((k + 1) \times \operatorname{log}(p))^{m} \times p^{{-((k + 1) \times sigma)}},&\operatorname{mod}(p, 5) = 1 \lor \operatorname{mod}(p, 5) = 4\\0,&\text{otherwise}\end{cases}\right) \land \left(\left(\forall m \in \operatorname{Nat}(), p \in \operatorname{Nat}(), k \in \operatorname{Nat}(), sigma \in \operatorname{Real}(),\; \left(\operatorname{IsGoldenSplitPrime}(p) \land \left(0 < k \land 1 < sigma\right)\right) \Rightarrow 0 \le \frac{2 \times (1 - \operatorname{cos}(k \times phase\left(p\right)))}{k} \times (k \times \operatorname{log}(p))^{m} \times p^{{-(k \times sigma)}}\right) \land \left(\forall m \in \operatorname{Nat}(), sigma \in \operatorname{Real}(),\; 1 < sigma \Rightarrow 0 \le \operatorname{pow}((-1), m) \times \operatorname{iteratedDeriv}(m, \operatorname{goldenObserverCasimir}(phase), sigma)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Adelic/PrimeObserverCasimirCompleteMonotonicity.prime_observer_casimir_complete_monotonicity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Golden split primes are the nonramified rational primes whose images are not prime in the golden integers. The phase function supplies their regulator angles.

Each Fourier mode is constructed as a prime-power Dirichlet coefficient. The Casimir is the logarithmic zero-mode reading minus the first-mode reading.

The prime-power coefficient is a nonnegative squared phase distance. Termwise logarithmic differentiation and prime-power support reindexing give the displayed signed double series throughout the half-plane sigma greater than one. The index k + 1 records the source's positive prime-power exponent.

## References

- Truth anchor: `D5/S3/Analytic/Adelic/PrimeObserverCasimirCompleteMonotonicity.prime_observer_casimir_complete_monotonicity`
- Dependency: [D5/S3/PrimeForms/GoldenPrimeClassification](../../PrimeForms/GoldenPrimeClassification.md)
