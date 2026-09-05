# Golden Euler Gap Word Constraints

## Abstract

The deterministic golden Euler frequency word forbids two consecutive short steps and three consecutive long steps, and Euler phase letters inherit the same grammar.

**Theorem 1.1 (A short frequency step forces a following long step).**

$$\forall p: Nat.Primes, \forall v: Nat, \operatorname{goldenWord}(v) = \operatorname{false} \Rightarrow (\operatorname{primeLayerFrequency}(p, v+1) - \operatorname{primeLayerFrequency}(p, v) = \varphi \times \log(p)) \land (\operatorname{primeLayerFrequency}(p, v+1+1) - \operatorname{primeLayerFrequency}(p, v+1) = \varphi^{2} \times \log(p)).$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GoldenEulerGapWordConstraints.short_frequency_forces_next_long` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The golden word identifies true letters with phi-squared prime-log gaps and false letters with phi prime-log gaps. Existing golden desubstitution proves that false-false never occurs, so every short frequency letter is followed by a long one.

The same module proves that three long letters never occur and transports both forbidden-word laws to the Euler phase alphabet. This is a deterministic symbolic constraint; an explicit stochastic non-iid theorem would additionally require a chosen probability measure.

## References

- Truth anchor: `D5/S3/Analytic/GoldenEulerGapWordConstraints.short_frequency_forces_next_long`
- Dependency: [D5/S3/Observer/GoldenPrimeCircle/GoldenEulerStepPhaseLaw](../Observer/GoldenPrimeCircle/GoldenEulerStepPhaseLaw.md)
