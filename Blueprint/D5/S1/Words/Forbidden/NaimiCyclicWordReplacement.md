# Cyclic replacement of adjacent-compatible words

## Abstract

Adjacent compatibility does not guarantee positional cyclic replacement in finite linear words.

**Definition 1.1 (Positional replacement by a bijection).**

Lean statement: `D5/S1/Words/Forbidden/NaimiCyclicWordReplacement.claim`

*Formalization.* `D5/S1/Words/Forbidden/NaimiCyclicWordReplacement.claim` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Section 8 of Ramin Naimi's Swapping Compatible Words, arXiv:2610.31967v2, asks for a cyclic replacement of three or more patterns. The labels have successor i + 1 modulo the cycle size, and patterns may repeat.

The directed border lengths from one pattern to another are the lengths at which a suffix of the first equals a prefix of the second. They include length zero and permit full length. Adjacent labels have equal self-border sets and equal directed sets in the two directions. Equality of the self-border sets forces a common pattern length.

For each host length the claim asks for a single bijection on all hosts over the given finite alphabet. For every host, label, and zero-based start, the input has that occurrence exactly when the output has the successor occurrence at the same start. An occurrence lies on a nonempty interval inside the host, so an empty pattern has no occurrences.

**Theorem 1.2 (Four patterns force conflicting letters).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Forbidden/NaimiCyclicWordReplacement.result` (`✓ std3`). ∎

*Resolves.* `Problems/naimi-2026-cyclic-compatible-word-replacement` (refuted) by `D5/S1/Words/Forbidden/NaimiCyclicWordReplacement.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"naimi-2026-cyclic-compatible-word-replacement","declaration_gid":"D5/S1/Words/Forbidden/NaimiCyclicWordReplacement.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Commentary.*

Use 001, 002, 011 and 021 in that cyclic order over the alphabet of 0, 1 and 2. Every self-border set is {0, 3}. Every adjacent directed border set is {0} in either direction. In particular, the forward edges have the common set {0} required by the alternative in Section 8.

The host 0021 contains 002 at start 0 and 021 at start 1. One output would have to contain 011 at start 0 and 001 at start 1. Offset 1 of the first demand forces the letter 1 at coordinate 1, and offset 0 of the second forces the letter 0 there.

## References

- Truth anchor: `D5/S1/Words/Forbidden/NaimiCyclicWordReplacement.claim`
- Truth anchor: `D5/S1/Words/Forbidden/NaimiCyclicWordReplacement.result`
