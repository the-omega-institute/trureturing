# Finite Binary Kraft Converse

## Abstract

Every bounded multiset satisfying the finite Kraft bound is realized by a prefix-free binary code.

For lengths bounded by a common depth N, multiplying the usual Kraft sum by 2^N gives an exact natural-number inequality. This avoids any appeal to real-number rounding while retaining repeated prescribed lengths.

**Theorem 1.1 (The integer-scaled Kraft bound constructs a prefix-free code).**

$$\forall lengths, N, (\forall l \in lengths, l \leq N) \land (\sum_{l \in lengths} 2^{{N - l}} \leq 2^{N}) \Rightarrow \exists code, \operatorname{Nodup}(code) \land \operatorname{lengthMultiset}(code) = lengths \land \operatorname{IsPrefixFree}(code).$$

*Proof.* Machine-checked in Lean as `D5/S0/Computability/Coding/KraftConverse.exists_isPrefixFree_code_of_kraft` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Sort the prescribed lengths and add codewords from shortest to longest. At each depth, a union bound counts the binary vectors already occupied by earlier prefix cylinders. The scaled Kraft budget leaves a vector outside that union, so adjoining it preserves prefix freedom and list nodupness.

The hypothesis sum 2^(N-l) <= 2^N is exactly equivalent, for these bounded lengths, to sum 2^(-l) <= 1. The resulting code has exactly the input length multiset, including multiplicities.

## References

- Truth anchor: `D5/S0/Computability/Coding/KraftConverse.exists_isPrefixFree_code_of_kraft`
- Dependency: [D5/S0/Computability/Coding/PrefixFreeCode](PrefixFreeCode.md)
- Dependency: [D5/S0/Computability/KraftInequality](../KraftInequality.md)
