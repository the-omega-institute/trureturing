# The First Fibonacci Delimiter

## Abstract

Appending one terminal bit to a positive canonical Fibonacci word determines its first delimiter and preserves every following bit.

Fibonacci weights begin with one and two. A positive natural number has canonical occupied indices with no adjacent indices. The dense word lists their bits from least to most significant, ending at the highest occupied bit.

The return blocks are zero and one followed by zero. Expansion with the transient terminal channel adds a final one after these blocks. Thus a word in this form has no consecutive ones internally and ends in one.

The function parseF reads zero as a zero block and one followed by zero as a oneZero block. It stops immediately at two consecutive ones and returns the accumulated blocks with the untouched suffix. Empty input and a lone one fail because they contain no complete delimiter.

**Theorem 1.1 (Every positive canonical word has its exact first-delimiter parse).**

$$\begin{aligned}\forall n \in \mathbb{N},\\0 < n \implies \forall suffix \in \operatorname{List}(\operatorname{Fin}(2)),\\\exists! blocks \in \operatorname{List}(ReturnBlock),\\\operatorname{zeckendorfLSDWord}(\operatorname{wdigits}(n)) = \operatorname{expand}(blocks, transient) \land\\\operatorname{parseF}(\operatorname{append}(\operatorname{append}(\operatorname{zeckendorfLSDWord}(\operatorname{wdigits}(n)), [1]), suffix)) = \operatorname{some}((blocks, suffix)).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Digit/FibonacciFirstDelimiter.positive_word_first_delimiter` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Here append is list concatenation, some denotes a successful optional result, and transient specifies the final one in the expansion. The suffix is any binary list, including a list beginning with two ones.

Canonicality separates occupied indices. Induction on the remaining display length constructs zero or oneZero blocks until the highest occupied bit, which supplies the transient terminal one. A second induction checks that the parser consumes exactly these blocks and the extra terminal one. Injectivity of expansion gives uniqueness.

For the number one there are no return blocks: its data word is a single one and its completed message consists of two ones. Positivity excludes the zero word, whose highest displayed bit is zero.

## References

- Truth anchor: `D5/S1/Digit/FibonacciFirstDelimiter.positive_word_first_delimiter`
- Dependency: [D5/S0/Automata/BinaryZeckendorfBlockSkeletonCore](../../S0/Automata/BinaryZeckendorfBlockSkeletonCore.md)
- Dependency: [D5/S1/Digit/ZeckendorfResidueTransducer](ZeckendorfResidueTransducer.md)
