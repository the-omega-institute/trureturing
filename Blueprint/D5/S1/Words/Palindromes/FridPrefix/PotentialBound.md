# Palindromic factorisations bound integral potentials

## Abstract

Palindromic factorisations bound integral potentials

**Theorem 1.1 (potential_pl_bound).**

$$\forall S \in Arrow\left(\mathbb{N}, \mathbb{Z}\right),\; \forall n \in \mathbb{N},\; \left(apply\left(S, 0\right) = 0 \land \left(\forall i \in \mathbb{N},\; \forall j \in \mathbb{N},\; \left(i < j \land \left(j \le n \land Palindrome\left(goldenFactor\left(j - i, i\right)\right)\right)\right) \Rightarrow apply\left(S, j\right) \le apply\left(S, i\right) + 1\right)\right) \Rightarrow apply\left(S, n\right) \le int\left(PL\left(goldenFactor\left(n, 0\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Palindromes/FridPrefix/PotentialBound.potential_pl_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Only increasing palindrome edges whose destination is at most n are required. Induction over any nonempty palindrome factorisation telescopes the edge inequalities from the zero potential at the empty prefix.

## References

- Truth anchor: `D5/S1/Words/Palindromes/FridPrefix/PotentialBound.potential_pl_bound`
- Dependency: [D5/S1/Words/Palindromes/FridPrefix/PalindromicLength](PalindromicLength.md)
