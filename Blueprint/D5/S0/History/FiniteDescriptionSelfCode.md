# Finite Description Self-Codes

## Abstract

Finite descriptions correspond exactly to their natural-number self-codes.

**Theorem 1.1 (Finite descriptions have lossless self-codes).**

$$\operatorname{Bijective}(\operatorname{selfEncoding})$$

*Proof.* Machine-checked in Lean as `D5/S0/History/FiniteDescriptionSelfCode.finite_description_self_encoding_bijective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A finite low-level description is represented by a finite bit string. Its code space is not all natural numbers by assertion, but the subtype consisting exactly of natural numbers in the encoder's range. The formal equivalence sends each description to its natural code together with the range witness, and its inverse recovers the original description. Hence the self-encoding map is injective and surjective onto the typed code space. This strengthens the source atom's membership notation into a lossless correspondence without claiming that every natural number is a description code.

The pinned library was searched first. It already supplies the exact encoding-range equivalence as Encodable.equivRangeEncode and bundled bijectivity as Equiv.bijective, so the Lean proof is a declared thin honest wrapper rather than a second encoding proof. Searches for finiteDescriptionSelfCode, kernelSelfCode, and selfEncoding found no dedicated upstream theorem. The source atom is structural and carries no numerical certificate.

## References

- Truth anchor: `D5/S0/History/FiniteDescriptionSelfCode.finite_description_self_encoding_bijective`
