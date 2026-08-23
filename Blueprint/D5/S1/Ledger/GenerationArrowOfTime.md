# Generation Gives an Arrow of Time

## Abstract

Prime-exponent length is additive, equals the logarithm of the encoded number, and strictly grows under every nonzero generation.

**Lemma 1.1 (Prime-exponent length is additive).**

$$\forall a\in \operatorname{PrimeExponent},\ u\in \operatorname{PrimeExponent},\ \operatorname{length}(a + u) = \operatorname{length}(a) + \operatorname{length}(u)$$

*Proof.* Machine-checked in Lean as `D5/S1/Ledger/GenerationArrowOfTime.length_add` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Adding two prime-exponent states adds their exponent on every prime. The logarithmic weights are fixed, so the weighted finite sum of the combined state splits into the sum of the two lengths.

**Lemma 1.2 (Length is the logarithm of the generated number).**

$$\forall a\in \operatorname{PrimeExponent},\ \operatorname{length}(a) = \log (\operatorname{generatedNumber}(a))$$

*Proof.* Machine-checked in Lean as `D5/S1/Ledger/GenerationArrowOfTime.length_eq_log_generatedNumber` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A prime-exponent state encodes the product of each prime raised to its recorded exponent. Taking the logarithm turns that finite product into exactly the exponent-weighted sum that defines its length.

**Lemma 1.3 (Every nonzero update has positive length).**

$$\forall u\in \operatorname{PrimeExponent},\ u \neq 0 \Rightarrow 0 < \operatorname{length}(u)$$

*Proof.* Machine-checked in Lean as `D5/S1/Ledger/GenerationArrowOfTime.length_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A nonzero state has a positive exponent on at least one prime. Every prime has positive logarithm, so that coordinate contributes strictly positively while all remaining coordinates contribute nonnegatively.

**Theorem 1.4 (Nonzero generation strictly increases length).**

$$\forall a\in \operatorname{PrimeExponent},\ u\in \operatorname{PrimeExponent},\ u \neq 0 \Rightarrow \operatorname{length}(a + u) > \operatorname{length}(a)$$

*Proof.* Machine-checked in Lean as `D5/S1/Ledger/GenerationArrowOfTime.length_strictly_increases_under_generation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Generation adds an update vector to the current ledger state. Additivity says that the new length is the old length plus the update length, and a nonzero update has positive length. Thus every nonzero generation moves strictly forward in this logarithmic coordinate.

## References

- Truth anchor: `D5/S1/Ledger/GenerationArrowOfTime.length_add`
- Truth anchor: `D5/S1/Ledger/GenerationArrowOfTime.length_eq_log_generatedNumber`
- Truth anchor: `D5/S1/Ledger/GenerationArrowOfTime.length_pos`
- Truth anchor: `D5/S1/Ledger/GenerationArrowOfTime.length_strictly_increases_under_generation`
