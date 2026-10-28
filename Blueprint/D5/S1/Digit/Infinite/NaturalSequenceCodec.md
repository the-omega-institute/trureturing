# Natural sequences as legal infinite digits

## Abstract

Arbitrary natural sequences have literal legal paired unary names and executable prefix recovery.

**Definition 1.1 (Finite blocks).**

Lean statement: `D5/S1/Digit/Infinite/NaturalSequenceCodec.block`

*Formalization.* `D5/S1/Digit/Infinite/NaturalSequenceCodec.block` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every natural a, block(a) is a copies of the two bits 10 followed by 00. In particular, block(0) is 00. Lists retain all zeros and repeated delimiters.

**Definition 1.2 (Concatenated initial blocks).**

Lean statement: `D5/S1/Digit/Infinite/NaturalSequenceCodec.encodedPrefix`

*Formalization.* `D5/S1/Digit/Infinite/NaturalSequenceCodec.encodedPrefix` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a sequence p of arbitrary natural numbers, encodedPrefix(p,n) concatenates block(p(0)) through block(p(n-1)) in that order. It is empty for n=0. Write B(p,n) for this list and length for the number of bits in a list.

**Definition 1.3 (The infinite legal code).**

Lean statement: `D5/S1/Digit/Infinite/NaturalSequenceCodec.encode`

*Formalization.* `D5/S1/Digit/Infinite/NaturalSequenceCodec.encode` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The unary word writeNat(a) consists of a ones followed by a zero. Concatenating these nonempty words gives an infinite unary stream. Encoding replaces each unary bit b by the pair b0. Thus E(p)=encode(p) is the literal infinite concatenation of the blocks. Every odd numbered bit, indexed from zero, is zero; each adjacent pair of positions contains such a bit. The value belongs to SuccessorContinuity.LegalDigits, the existing subtype of streams with no adjacent ones. Random access terminates by decreasing the requested unary index whenever a whole block is skipped. It applies to zero entries and arbitrarily long blocks.

**Definition 1.4 (Finite unary parsing).**

Lean statement: `D5/S1/Digit/Infinite/NaturalSequenceCodec.parsePrefix`

*Formalization.* `D5/S1/Digit/Infinite/NaturalSequenceCodec.parsePrefix` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Given a natural count n and a finite Boolean list, parsePrefix reads n unary numbers using readNat and returns their list, or none if a complete prefix is unavailable. It ignores the unused suffix. For n=0 it returns the empty list.

**Definition 1.5 (Decoding with finite fuel).**

Lean statement: `D5/S1/Digit/Infinite/NaturalSequenceCodec.decodePrefix`

*Formalization.* `D5/S1/Digit/Infinite/NaturalSequenceCodec.decodePrefix` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

decodePrefix(x,n,fuel) reads the first bit of each of fuel consecutive pairs of x, then calls parsePrefix. It queries only the positions 2j for j less than fuel. On an encoded stream, any fuel containing the first n complete blocks succeeds. A successful result persists when the input window is extended. Only recovery on the image is asserted; odd bits are not checked by this parser.

**Definition 1.6 (Executable search on the image).**

Lean statement: `D5/S1/Digit/Infinite/NaturalSequenceCodec.recoverPrefix`

*Formalization.* `D5/S1/Digit/Infinite/NaturalSequenceCodec.recoverPrefix` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For x accompanied by a proof that x is in the image of encode, recoverPrefix(x,n) tests increasing finite fuel until decodePrefix succeeds and returns its result. The implementation uses the computable Nat.find search. Its termination proof and the image membership proof are erased during execution: no preimage sequence is supplied as runtime data. Write R(x,n) for this proof independent result, and take(n,s) for the first n entries of a stream s. Computability here is relative to access to the input sequence or stream; no claim makes an arbitrary noncomputable sequence into a finite computable program.

**Theorem 1.7 (Literal transport and complete prefix recovery).**

$$\forall p:\mathbb{N} \to \mathbb{N}, (\forall n:\mathbb{N}, \operatorname{take}\left(\operatorname{length}\left(\operatorname{B}\left(p, n\right)\right), \operatorname{E}\left(p\right)\right) = \operatorname{B}\left(p, n\right) \land 2n \leq \operatorname{length}\left(\operatorname{B}\left(p, n\right)\right)) \land (\forall n:\mathbb{N}, \operatorname{R}\left(\operatorname{E}\left(p\right), n\right) = \operatorname{take}\left(n, p\right)) \land (\forall q:\mathbb{N} \to \mathbb{N}, \operatorname{E}\left(p\right) = \operatorname{E}\left(q\right) \implies p = q)$$

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/NaturalSequenceCodec.natural_sequence_transport` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural sequence p, every finite block concatenation is exactly an initial segment of E(p), and its length is at least twice its block count. The lengths are therefore unbounded. Every finite prefix of p is recovered from E(p). Equality E(p)=E(q) forces equality of all finite source prefixes, hence p=q. Legality is also part of the codomain of encode.

For each requested n, the finite concatenation of the first n unary words has finite length. At that fuel the existing identity readNat_writeNat recovers each entry in turn. The stream expansion identifies that finite word with the even positions of the actual infinite code. The identity readNat_eq_some shows that successful parsing consumes exactly its unary prefix, so extra input cannot change a successful answer. Extending any successful window to a window containing n full blocks proves soundness of the first successful search result. The proof uses this actual recovery to distinguish arbitrary source sequences.

## References

- Truth anchor: `D5/S1/Digit/Infinite/NaturalSequenceCodec.block`
- Truth anchor: `D5/S1/Digit/Infinite/NaturalSequenceCodec.decodePrefix`
- Truth anchor: `D5/S1/Digit/Infinite/NaturalSequenceCodec.encode`
- Truth anchor: `D5/S1/Digit/Infinite/NaturalSequenceCodec.encodedPrefix`
- Truth anchor: `D5/S1/Digit/Infinite/NaturalSequenceCodec.natural_sequence_transport`
- Truth anchor: `D5/S1/Digit/Infinite/NaturalSequenceCodec.parsePrefix`
- Truth anchor: `D5/S1/Digit/Infinite/NaturalSequenceCodec.recoverPrefix`
- Dependency: [D5/S0/Computability/BinaryMachine/UnaryWords](../../../S0/Computability/BinaryMachine/UnaryWords.md)
- Dependency: [D5/S1/Digit/Infinite/SuccessorContinuity](SuccessorContinuity.md)
