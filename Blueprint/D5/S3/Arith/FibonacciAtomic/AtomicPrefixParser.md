# Literal Atomic Prefix Parser

## Abstract

The literal two-letter tree code has an executable recursive parser with exact suffix boundaries, injective code, prefix-free image, and complete decoding.

Source is the existing FreeMagma Bool of finite nonempty ordered binary trees. The true leaf is alpha and the false leaf is beta. A leaf b is encoded as [true,b], while a branch is encoded as false followed by the concatenation of the left and right codes. The parser uses predecessor fuel for both recursive children and passes the actual remainder returned by the left parse to the right parse. Its public fuel is the input length, and decode accepts only an empty final remainder.

**Definition 1.1 (Literal Tree Code).**

$$(\forall (b : Bool), (\operatorname{code}\left(\operatorname{of}\left(b\right)\right) = [true, b])) \land (\forall (s : Source) (t : Source), (\operatorname{code}\left(\operatorname{mul}\left(s, t\right)\right) = false :: (\operatorname{code}\left(s\right) ++ \operatorname{code}\left(t\right))))$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/AtomicPrefixParser.code` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

$$
code : Source \to List Bool
$$

The two Boolean letters are used directly. Internal nodes begin with false, so the two child codes are parsed without a delimiter or integer encoding.

**Definition 1.2 (Fuelled Suffix Parser).**

$$\forall (w : List Bool), (\operatorname{parse}\left(w\right) = \operatorname{parseFuel}\left(\operatorname{length}\left(w\right), w\right))$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/AtomicPrefixParser.parse` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

$$
parse : List Bool \to \operatorname{Option}\left(Source \times List Bool\right)
$$

Parsing returns either failure or a source tree together with the exact unconsumed suffix. The local recurrence below uses recursion-depth fuel: both child calls receive n, and the right child receives the actual left remainder r. The clauses exhaust the input shapes and recursive outcomes. The public parser derives its fuel from the input length.

$$
parseFuel : Nat \to List Bool \to \operatorname{Option}\left(Source \times List Bool\right)
$$

$$
\forall (w : List Bool), (\operatorname{parseFuel}\left(0, w\right) = none)
$$

$$
\forall (n : Nat) (b : Bool) (r : List Bool), (\operatorname{parseFuel}\left(n + 1, true :: b :: r\right) = \operatorname{some}\left((\operatorname{of}\left(b\right), r)\right))
$$

$$
\forall (n : Nat) (w : List Bool) (s : Source) (r : List Bool) (t : Source) (q : List Bool), (((\operatorname{parseFuel}\left(n, w\right) = \operatorname{some}\left((s, r)\right)) \land (\operatorname{parseFuel}\left(n, r\right) = \operatorname{some}\left((t, q)\right))) \Rightarrow \operatorname{parseFuel}\left(n + 1, false :: w\right) = \operatorname{some}\left((\operatorname{mul}\left(s, t\right), q)\right))
$$

$$
\forall (n : Nat) (w : List Bool), ((\operatorname{parseFuel}\left(n, w\right) = none) \Rightarrow \operatorname{parseFuel}\left(n + 1, false :: w\right) = none)
$$

$$
\forall (n : Nat) (w : List Bool) (s : Source) (r : List Bool), (((\operatorname{parseFuel}\left(n, w\right) = \operatorname{some}\left((s, r)\right)) \land (\operatorname{parseFuel}\left(n, r\right) = none)) \Rightarrow \operatorname{parseFuel}\left(n + 1, false :: w\right) = none)
$$

$$
\forall (n : Nat), ((\operatorname{parseFuel}\left(n + 1, []\right) = none) \land (\operatorname{parseFuel}\left(n + 1, [true]\right) = none))
$$

**Definition 1.3 (Complete Decoder).**

$$\forall (w : List Bool), (\operatorname{decode}\left(w\right) = \operatorname{emptyRemainder}\left(\operatorname{parse}\left(w\right)\right))$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/AtomicPrefixParser.decode` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

$$
decode : List Bool \to Option Source
$$

Here emptyRemainder denotes the mathematical operation defined by the following three cases. Decoding succeeds exactly when the parser consumes the whole input, and then returns the parsed source.

$$
emptyRemainder : \operatorname{Option}\left(Source \times List Bool\right) \to Option Source
$$

$$
(\operatorname{emptyRemainder}\left(none\right) = none) \land (\forall (t : Source), (\operatorname{emptyRemainder}\left(\operatorname{some}\left((t, [])\right)\right) = \operatorname{some}\left(t\right))) \land (\forall (t : Source) (b : Bool) (r : List Bool), (\operatorname{emptyRemainder}\left(\operatorname{some}\left((t, b :: r)\right)\right) = none))
$$

**Theorem 1.4 (Exact Parsing and Prefix-Free Coding).**

$$(\forall (w : List Bool) (t : Source) (r : List Bool), (\operatorname{parse}\left(w\right) = \operatorname{some}\left((t,r)\right) \Leftrightarrow w = \operatorname{append}\left(\operatorname{code}\left(t\right), r\right))) \land (\operatorname{Injective}\left(code\right)) \land (\operatorname{IsPrefixFree}\left(\operatorname{range}\left(code\right)\right)) \land (\forall (w : List Bool) (t : Source), (\operatorname{decode}\left(w\right) = \operatorname{some}\left(t\right) \Leftrightarrow w = \operatorname{code}\left(t\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/AtomicPrefixParser.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The first conjunct is the successful-consumption equivalence for every input, tree, and suffix. Its proof keeps the stronger local induction invariant that any successful fuelled parse consumes exactly one codeword, and the uniform sufficient-fuel invariant that every codeword followed by an arbitrary suffix parses with that suffix unchanged.

The same parser law gives injectivity by applying a local Encoding roundtrip, and gives prefix freedom by parsing one complete codeword in two ways. Full decoding is equivalent to being exactly a codeword; malformed inputs and nonempty suffixes are rejected.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/AtomicPrefixParser.code`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/AtomicPrefixParser.decode`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/AtomicPrefixParser.parse`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/AtomicPrefixParser.result`
- Dependency: [D5/S0/Computability/Coding/PrefixFreeCode](../../../S0/Computability/Coding/PrefixFreeCode.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/GenealogicalFiberTransport](GenealogicalFiberTransport.md)
