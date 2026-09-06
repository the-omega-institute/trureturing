# Prime Golden Complex Mode

## Abstract

A first golden prime mode splits into prime-faithful heat amplitude and recurrent unit-circle phase.

**Theorem 1.1 (Positive amplitude identifies primes while phase recurs).**

$$\begin{gathered}\forall s, 0 < s \Rightarrow \forall P, \forall e, 0 < e \Rightarrow \forall b, \forall u,\\{}\operatorname{Injective}(\operatorname{firstGoldenComplexMode}(s, u)) \land\\{}\exists t, b < t \land \forall p \in P, \operatorname{norm}(\operatorname{firstGoldenComplexMode}(0, t, p) - 1) < e.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/GoldenPrimeCircle/PrimeGoldenComplexMode.complex_mode_amplitude_phase_dichotomy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The real coordinate controls modulus and the imaginary coordinate controls rotation.

This is an analytic-time statement and does not identify the parameter with laboratory time.

## References

- Truth anchor: `D5/S3/Observer/GoldenPrimeCircle/PrimeGoldenComplexMode.complex_mode_amplitude_phase_dichotomy`
- Dependency: [D5/S3/ObserverMemory/FourierFibers/PrimeZeckendorfTemporalization](../../ObserverMemory/FourierFibers/PrimeZeckendorfTemporalization.md)
