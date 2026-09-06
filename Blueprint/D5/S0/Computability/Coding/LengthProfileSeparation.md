# Length-Profile Separation for Immutable Prefix Codes

## Abstract

Equal codeword lengths and equal Kraft mass do not control immutable extension depth.

For arbitrary d and positive r, the spread family appends r zeroes to every d-bit word, while the packed family prepends the same zero block. Both families are prefix-free and have exactly the same complete multiset of codeword lengths.

The parameters d, r, and every queried depth n are natural numbers, and all words are lists over Fin 2. The displayed mass is a real sum. The val/map expressions retain multiplicity in the full multiset of lengths; Nonempty(freeAt(C,n)) means that a length-n word is incomparable in both prefix directions with every existing word of C.

**Theorem 1.1 (Equal length profiles hide an unbounded extension gap).**

$$\forall d, r, 0 < r \Rightarrow \left(\left(\left(\left(\operatorname{IsPrefixFree}\left(\operatorname{spreadCode}\left(d, r\right)\right) \land \operatorname{IsPrefixFree}\left(\operatorname{packedCode}\left(d, r\right)\right)\right) \land \operatorname{map}\left(\operatorname{val}\left(\operatorname{spreadCode}\left(d, r\right)\right), length\right) = \operatorname{map}\left(\operatorname{val}\left(\operatorname{packedCode}\left(d, r\right)\right), length\right)\right) \land \sum_{w \in \operatorname{spreadCode}\left(d, r\right)} {1 / 2}^{\operatorname{length}\left(w\right)} = {1 / 2}^{r}\right) \land \forall n, \operatorname{Nonempty}\left(\operatorname{freeAt}\left(\operatorname{spreadCode}\left(d, r\right), n\right)\right) \Leftrightarrow d < n\right) \land \forall n, \operatorname{Nonempty}\left(\operatorname{freeAt}\left(\operatorname{packedCode}\left(d, r\right), n\right)\right) \Leftrightarrow 0 < n.$$

*Proof.* Machine-checked in Lean as `D5/S0/Computability/Coding/LengthProfileSeparation.equal_lengths_unbounded_extension_gap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The spread code has Kraft mass (1/2)^r. Equality of the complete length multisets therefore gives the packed code the same mass, although the Lean conjunction records the spread mass explicitly.

At depth n the spread family has a compatible slot exactly when d < n, whereas the packed family has one exactly when 0 < n. Their shortest possible immutable extension lengths are consequently d + 1 and 1, so fixing positive r and increasing d makes the gap unbounded.

## References

- Truth anchor: `D5/S0/Computability/Coding/LengthProfileSeparation.equal_lengths_unbounded_extension_gap`
- Dependency: [D5/S0/Computability/Coding/ImmutableExtension](ImmutableExtension.md)
