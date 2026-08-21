# Generation Shadow

## Abstract

Multiplication is the decoded shadow of exponent generation, and motion has length.

The clause reads the kernel's bottom layer as generation on a prime exponent ledger: the state advances by adding a control vector, and integer multiplication appears only as the decoded image of that motion. Multiplication is therefore not primitive here; the ledger step is, and multiplication is its shadow.

The decoder and the normalized step already existed. What is added is the length: a search for a state length on prime-axis tables returned nothing. Each axis contributes its exponent weighted by the prime's logarithm, and a state carrying any positive exponent has positive length, because every prime exceeds one.

**Lemma 1.1 (Generation decodes to multiplication).**

$$\operatorname{n}\left(a + u\right) = \operatorname{n}\left(a\right) \cdot \operatorname{n}\left(u\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Digit/PrimeAxis/GenerationShadow.decode_generation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Adding control codes and renormalizing multiplies the decoded values, which is the existing one-step decoder result named at the generation step.

**Lemma 1.2 (Every prime contributes positive length).**

$$0 < \operatorname{log}\left(p\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Digit/PrimeAxis/GenerationShadow.log_prime_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A prime is at least two, so its logarithm is positive; this is the only arithmetic the length argument needs.

**Lemma 1.3 (The length of a state).**

$$\operatorname{L}\left(a\right) = \operatorname{sum}\left(p, \operatorname{exponent}\left(a, p\right) \cdot \operatorname{log}\left(p\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Digit/PrimeAxis/GenerationShadow.stateLength_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Length sums the exponents against the prime logarithms, and is never negative since each summand is a nonnegative exponent times a positive logarithm.

**Theorem 1.4 (A nonempty state has positive length).**

$$0 < \operatorname{L}\left(a\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Digit/PrimeAxis/GenerationShadow.stateLength_pos_of_axis` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The pointwise lemma the arrow of time rests on. One positive exponent on one axis already exceeds zero, and the remaining summands are nonnegative, so the whole length is positive. Dropping the hypothesis makes the module fail to build, so the statement is not a claim that length is always positive.

## References

- Truth anchor: `D5/S1/Digit/PrimeAxis/GenerationShadow.decode_generation`
- Truth anchor: `D5/S1/Digit/PrimeAxis/GenerationShadow.log_prime_pos`
- Truth anchor: `D5/S1/Digit/PrimeAxis/GenerationShadow.stateLength_nonneg`
- Truth anchor: `D5/S1/Digit/PrimeAxis/GenerationShadow.stateLength_pos_of_axis`
- Dependency: [D5/S1/Digit/PrimeAxis/PrimeAxisNormalizationUnique](PrimeAxisNormalizationUnique.md)
