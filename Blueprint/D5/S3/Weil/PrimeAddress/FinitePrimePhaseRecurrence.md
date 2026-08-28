# Finite Prime Phase Recurrence

## Abstract

Every finite set of prime phases returns arbitrarily close to coherent phase.

**Theorem 1.1 (Finite prime phases recur above every bound).**

$$\forall P: \operatorname{Finset}\left(Primes\right), \varepsilon, B \in \mathbb{R},\\{}0 < \varepsilon \Rightarrow \exists \xi \in \mathbb{R}, B < \xi \land \forall p \in P, \left\lVert \exp(i \xi \log p) - 1 \right\rVert < \varepsilon$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/PrimeAddress/FinitePrimePhaseRecurrence.finite_prime_phase_recurrence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Compactness of the finite product of unit circles gives a convergent subsequence of sampled prime-phase vectors. Quotients of consecutive subsequence terms converge to the coherent phase. Sampling with a step larger than the requested bound makes the resulting recurrence time larger than that bound.

## References

- Truth anchor: `D5/S3/Weil/PrimeAddress/FinitePrimePhaseRecurrence.finite_prime_phase_recurrence`
- Dependency: [D5/S3/Weil/PrimeAddress/PrimeLogIndependence](PrimeLogIndependence.md)
