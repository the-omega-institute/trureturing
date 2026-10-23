# Odd lattice-word construction

## Abstract

Construct distinct actual odd lattice words at the proposed descent level.

**Theorem 1.1 (Injective odd candidates in the actual carrier).**

Lean statement: `D5/S3/Combinatorics/ShankarWords/OddWordConstruction.odd_word_construction`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ShankarWords/OddWordConstruction.odd_word_construction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Umesh Shankar (2026). *Avoiding patterns with three distinct letters in Canon permutations*. DOI: [10.48550/arXiv.2608.30002](https://doi.org/10.48550/arXiv.2608.30002).

*Commentary.*

For every natural t at least one, oddWord(t) is injective on the full disjoint sum of two copies of Fin(2t) and Bool. For every index i in that domain, its word belongs to actualWords(2t+1) and has strict adjacent descent count extremalValue(2t+1), equal to 3t. The definitions are the public original-word definitions in ActualWordExtremal; the construction includes both inserted-one families and both singleton-two words. Every prefix cut, equal letter count, and 321 subsequence exclusion is required, including the empty middle block at t=1. Reverse-complement transfer uses the bounded alphabet 1,2,3 and equal content. The unique 11 marker recovers the first family index, its reverse-complement 33 marker separates the second family, and a distinguishing phase position separates the singleton-two words. All auxiliary facts are proof-local. This construction does not establish a universal upper bound, maximality, complete classification, surjectivity onto the actual top fiber, or Conjecture 9.3.

## References

- Truth anchor: `D5/S3/Combinatorics/ShankarWords/OddWordConstruction.odd_word_construction`
- Dependency: [D5/S3/Combinatorics/ShankarWords/ActualWordExtremal](ActualWordExtremal.md)
