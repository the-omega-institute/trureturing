# Intertranslation of Event Godel Codes

## Abstract

Prime-power and literal marker codes faithfully encode the same event quadruples.

**Theorem 1.1 (The literal marker event code is injective).**

$$\operatorname{Injective}(\operatorname{encodeEvent}).$$

*Proof.* Machine-checked in Lean as `D5/S0/History/Coding/EventCodeIntertranslation.encode_event_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The frozen marker implementation maps 0 to 00, maps 1 to 01, and places 11 between the source, opcode, argument, and tag fields. A public prefix decoder consumes exactly those pairs until 11, while fixed decoders recover the opcode and final tag.

The decoder is proved to recover every encoded event, so equal marker histories force equality of all four event components. This supplies the injectivity asserted for the low-level implementation.

**Theorem 1.2 (The prime-power event code is injective).**

$$\operatorname{Injective}(\operatorname{eventPrimeCode}).$$

*Proof.* Machine-checked in Lean as `D5/S0/History/Coding/EventCodeIntertranslation.event_prime_code_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An event first becomes the four-entry natural sequence consisting of its source-history code, opcode index, argument-history code, and tag digit. The frozen primeSequenceCode then applies the successive-prime exponent formula with every exponent shifted by one.

Injectivity is obtained by applying the frozen prime_sequence_code_injective theorem twice: once to recover the four components and once within each variable-length marker field. No second proof of the frozen prime-sequence theorem is introduced.

**Theorem 1.3 (Prime and marker implementations intertranslate).**

$$\forall e, \operatorname{primeToMarkerCode}(\operatorname{eventPrimeCode}(e)) = \operatorname{encodeEvent}(e) \land \operatorname{markerToPrimeCode}(\operatorname{encodeEvent}(e)) = \operatorname{eventPrimeCode}(e).$$

*Proof.* Machine-checked in Lean as `D5/S0/History/Coding/EventCodeIntertranslation.event_code_intertranslation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The two translations have different carriers: natural numbers for prime-power codes and marker histories for the literal implementation. Each translation recovers the common event on the image of its source encoder, then applies the other encoder.

The displayed equations specify both directions on every encoded event. Behavior outside the two encoder images is deliberately unspecified; the inverse-on-range construction chooses a default there. This is not a reflexive equivalence disguised as an intertranslation.

Pinned Mathlib searches found Function.leftInverse_invFun and List.map_injective_iff, which are applied for inverse-on-range and digit-list injectivity. No Mathlib or repository declaration matched the event-code bridge itself.

## References

- Truth anchor: `D5/S0/History/Coding/EventCodeIntertranslation.encode_event_injective`
- Truth anchor: `D5/S0/History/Coding/EventCodeIntertranslation.event_code_intertranslation`
- Truth anchor: `D5/S0/History/Coding/EventCodeIntertranslation.event_prime_code_injective`
- Dependency: [D5/S0/History/HistoryCarrier](../HistoryCarrier.md)
- Dependency: [D5/S0/History/PrimeSequenceCode](../PrimeSequenceCode.md)
