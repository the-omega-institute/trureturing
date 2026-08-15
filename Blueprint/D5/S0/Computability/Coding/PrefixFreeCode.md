# Prefix-Free Codes

## Abstract

Prefix-free and suffix-free codes decode uniquely, and finite binary prefix codes satisfy Kraft's inequality.

A code is prefix-free when a codeword can prefix another codeword only if they are equal. Dually, it is suffix-free when the same condition holds for suffixes. The empty word is excluded from nondegenerate decoding.

**Theorem 1.1 (The empty word makes a prefix-free code degenerate).**

$$\operatorname{IsPrefixFree}(S) \land [] \in S \Rightarrow S = \{[]\}.$$

*Proof.* Machine-checked in Lean as `D5/S0/Computability/Coding/PrefixFreeCode.isPrefixFree_eq_singleton_nil` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The empty word prefixes every list. Prefix freedom therefore forces every member of a code containing it to equal the empty word, so the code is exactly the singleton containing that word.

**Theorem 1.2 (A prefix-free concatenation determines its first codeword).**

$$u \in S, v \in S, u \cdot x = v \cdot y \Rightarrow u = v \land x = y.$$

*Proof.* Machine-checked in Lean as `D5/S0/Computability/Coding/PrefixFreeCode.isPrefixFree_first_codeword` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Two leading codewords in equal concatenations are comparable by the prefix relation. Prefix freedom identifies them, and left cancellation then identifies the remaining tails.

**Theorem 1.3 (Prefix-free codes are uniquely decodable).**

$$\operatorname{IsPrefixFree}(S) \land \neg ([] \in S) \Rightarrow \operatorname{UniquelyDecodable}(S).$$

*Proof.* Machine-checked in Lean as `D5/S0/Computability/Coding/PrefixFreeCode.uniquelyDecodable_of_isPrefixFree` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Induction on a list of codewords repeatedly applies first-codeword extraction. The empty-word side condition rules out a nonempty encoding whose flattened message is empty.

**Theorem 1.4 (Reversal sends suffix-free codes to prefix-free codes).**

$$\operatorname{IsSuffixFree}(S) \Rightarrow \operatorname{IsPrefixFree}(\operatorname{reverse image}(S)).$$

*Proof.* Machine-checked in Lean as `D5/S0/Computability/Coding/PrefixFreeCode.isSuffixFree_isPrefixFree_reverse_image` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

List reversal turns a prefix relation between reversed codewords into a suffix relation between the originals. Suffix freedom then identifies the originals, and reversing again identifies their images.

**Theorem 1.5 (Suffix-free codes are uniquely decodable).**

$$\operatorname{IsSuffixFree}(S) \land \neg ([] \in S) \Rightarrow \operatorname{UniquelyDecodable}(S).$$

*Proof.* Machine-checked in Lean as `D5/S0/Computability/Coding/PrefixFreeCode.uniquelyDecodable_of_isSuffixFree` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Reverse every codeword and reverse the codeword order. Flattening this transformed list reverses the flattened message, so prefix-free unique decodability transports back through the involution.

**Theorem 1.6 (Finite binary prefix codes satisfy Kraft's inequality).**

$$\operatorname{IsPrefixFree}(S) \land \neg ([] \in S) \Rightarrow \operatorname{kraft sum}(S) \leq 1.$$

*Proof.* Machine-checked in Lean as `D5/S0/Computability/Coding/PrefixFreeCode.kraft_inequality_of_isPrefixFree` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The prefix-free bridge supplies the unique-decodability hypothesis to the repository's finite_binary_kraft_inequality theorem. The counting argument therefore remains visible through the existing import edge.

**Theorem 1.7 (Unique decodability is strictly weaker than prefix freedom).**

$$\exists S, \operatorname{UniquelyDecodable}(S) \land \neg \operatorname{IsPrefixFree}(S).$$

*Proof.* Machine-checked in Lean as `D5/S0/Computability/Coding/PrefixFreeCode.exists_uniquelyDecodable_not_isPrefixFree` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The binary code `{[0], [0,1]}` is suffix-free and hence uniquely decodable, while `[0]` is a proper prefix of `[0,1]`. This explicit witness proves that the bridge has no converse.

Pinned mathlib and the repository were searched before proving. They provide unique decodability, Kraft-McMillan, and the list reversal lemmas used here, but no existing prefix-code predicate or theorem. The converse Kraft construction, infinite codes, and the halting-set application remain outside this deposit.

## References

- Truth anchor: `D5/S0/Computability/Coding/PrefixFreeCode.exists_uniquelyDecodable_not_isPrefixFree`
- Truth anchor: `D5/S0/Computability/Coding/PrefixFreeCode.isPrefixFree_eq_singleton_nil`
- Truth anchor: `D5/S0/Computability/Coding/PrefixFreeCode.isPrefixFree_first_codeword`
- Truth anchor: `D5/S0/Computability/Coding/PrefixFreeCode.isSuffixFree_isPrefixFree_reverse_image`
- Truth anchor: `D5/S0/Computability/Coding/PrefixFreeCode.kraft_inequality_of_isPrefixFree`
- Truth anchor: `D5/S0/Computability/Coding/PrefixFreeCode.uniquelyDecodable_of_isPrefixFree`
- Truth anchor: `D5/S0/Computability/Coding/PrefixFreeCode.uniquelyDecodable_of_isSuffixFree`
- Dependency: [D5/S0/Computability/KraftInequality](../KraftInequality.md)
