# Equal-height factorial words with common outer thirds

## Abstract

Equal-height factorial words with common outer thirds.

**Definition 1.1 (Balanced substitution).**

Lean statement: `D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedWords.balancedWord`

*Formalization.* `D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedWords.balancedWord` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At level zero the word of type a is the single letter a. Put N=(n+1)!. The next false word is 2N copies of the false child followed by N copies of the true child; the next true word is N false children followed by 2N true children. Both lengths are h(n+1)=3N h(n), with h(0)=1. The number of false letters is strictly greater in the false word, proving type injectivity despite the equal lengths.

**Theorem 1.2 (Shared columns and recurrence).**

Lean statement: `D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedWords.balancedWord_common_prefix`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedWords.balancedWord_common_prefix` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Both next words share their first N false children and their last N true children. Each shared segment has exactly one third of the next height. Every child type occurs in every next word. At levels n at least one, every ordered pair of level-n words occurs in every level-(n+2) word; the pair true-false uses an internal parent seam. These are combinatorial inputs for an equal-height tiling construction, not a claim that its subshift or its Toeplitz points have already been constructed.

**Theorem 1.3 (Exact disagreement fraction).**

Lean statement: `D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedWords.disagreement_fraction`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedWords.disagreement_fraction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Mismatch count compares aligned letters of the two equal-length lists. Splitting the two next words into three regions of N children leaves agreement on the first and third regions and N copies of the previous comparison in the middle. Thus d(n+1)=N d(n), d(0)=1, and 3^n d(n)=h(n). In particular the exact rational proportion of mismatching columns is (1/3)^n. Converting these column counts into periodic-skeleton density requires the separate tiling and phase construction.

**Theorem 1.4 (Finite group holonomy).**

Lean statement: `D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedWords.balancedWord_holonomy_eq_one`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedWords.balancedWord_holonomy_eq_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any finite group G and letter map from Bool to G, both level-(n+1) word holonomies are the identity whenever the cardinality of G is at most n+1. Holonomy places the last letter on the left. The two child holonomies are separately raised to factorial multiples, so each factor is the identity; unrelated group elements are never commuted. This is a finite algebraic statement and does not by itself establish a dynamical conjugacy or resolve Kang--Jaeger Question 1.10.

## References

- Truth anchor: `D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedWords.balancedWord`
- Truth anchor: `D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedWords.balancedWord_common_prefix`
- Truth anchor: `D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedWords.balancedWord_holonomy_eq_one`
- Truth anchor: `D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedWords.disagreement_fraction`
- Dependency: [D5/S1/Dynamics/Symbolic/PermutativeLifts/FactorialWords](FactorialWords.md)
