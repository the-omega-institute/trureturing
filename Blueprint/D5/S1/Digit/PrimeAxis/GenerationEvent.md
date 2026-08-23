# Generation Event

## Abstract

A legal generation event is a finitely supported vector of prime exponents.

The clause defines a legal generation event as a finitely supported vector on the prime axes. In this repository that finiteness is not a side condition to be checked: the state type carries its digits as a finitely supported function, so support is finite by construction and every axis outside it contributes nothing.

Stating it is still the content of the clause. Without these, a reader has the type but no theorem saying what the type buys, and the definition's own claim - finite support, so only finitely many axes are ever active - is left to be read off a signature.

**Lemma 1.1 (Only finitely many axes are active).**

$$\operatorname{Finite}\left(\operatorname{support}\left(u\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Digit/PrimeAxis/GenerationEvent.support_finite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The support of a finitely supported function is a finite set, which is what the clause asks of a generation event.

**Lemma 1.2 (Outside the support the exponent vanishes).**

$$\operatorname{exponent}\left(u, p\right) = 0$$

*Proof.* Machine-checked in Lean as `D5/S1/Digit/PrimeAxis/GenerationEvent.axisExponent_eq_zero_of_not_mem` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An axis outside the support carries the zero row, and the zero row decodes to exponent zero, so inactive axes contribute nothing to any later reading.

**Theorem 1.3 (A generation event is legal).**

$$\operatorname{Finite}\left(\operatorname{support}\left(u\right)\right) \land \left(\operatorname{exponent}\left(u, p\right) = 0 \land \operatorname{Canonical}\left(\operatorname{digits}\left(u, p\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Digit/PrimeAxis/GenerationEvent.generation_event_is_legal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Finitely supported, zero off the support, canonical on every axis. Replacing the canonicity conjunct by a trivially true one makes the module fail to build, so it is carrying weight rather than padding the conjunction.

## References

- Truth anchor: `D5/S1/Digit/PrimeAxis/GenerationEvent.axisExponent_eq_zero_of_not_mem`
- Truth anchor: `D5/S1/Digit/PrimeAxis/GenerationEvent.generation_event_is_legal`
- Truth anchor: `D5/S1/Digit/PrimeAxis/GenerationEvent.support_finite`
- Dependency: [D5/S1/Digit/PrimeAxis/PrimeAxisNormalizationUnique](PrimeAxisNormalizationUnique.md)
