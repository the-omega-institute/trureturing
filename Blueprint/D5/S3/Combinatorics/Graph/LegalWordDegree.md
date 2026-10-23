# Degrees and the sharp count bound for legal words

## Abstract

Legal binary words have one neighbour per occupied position or flippable zero. The flippable-zero count plus twice the occupation count is at most n+1, with equality exactly for odd alternating words beginning and ending in one.

A legal word is a Boolean function on Fin n satisfying Adm: adjacent positions cannot both be true. Positions are indexed from zero. The graph is the induced subgraph of the Boolean hypercube, so its edges have actual Hamming distance one. The occupation count is the existing sum of the Boolean values converted to naturals.

**Definition 1.1 (The induced legal-word graph).**

$$\forall n \in \mathrm{Nat},\; \forall b \in \{w: \mathrm{Fin}\left(n\right) \to \mathrm{Bool} \mid \mathrm{Adm}\left(n, w\right)\},\; \forall c \in \{w: \mathrm{Fin}\left(n\right) \to \mathrm{Bool} \mid \mathrm{Adm}\left(n, w\right)\},\; \mathrm{Adj}\left(\mathrm{legalWordGraph}\left(n\right), b, c\right) \Leftrightarrow \mathrm{hammingDist}\left(\mathrm{val}\left(b\right), \mathrm{val}\left(c\right)\right) = 1$$

*Formalization.* `D5/S3/Combinatorics/Graph/LegalWordDegree.legalWordGraph` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Vertices are the literal subtype of admissible Boolean words. Adjacency is inherited from the hypercube.

**Definition 1.2 (A flippable zero position).**

$$\forall n \in \mathrm{Nat},\; \forall w \in \mathrm{Fin}\left(n\right) \to \mathrm{Bool},\; \forall i \in \mathrm{Fin}\left(n\right),\; \mathrm{FlippableZero}\left(w, i\right) \Leftrightarrow \left(w\left(i\right) = \mathrm{false} \land \left(\forall j \in \mathrm{Fin}\left(n\right),\; \left(\mathrm{val}\left(j\right) + 1 = \mathrm{val}\left(i\right) \lor \mathrm{val}\left(i\right) + 1 = \mathrm{val}\left(j\right)\right) \Rightarrow w\left(j\right) = \mathrm{false}\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/LegalWordDegree.FlippableZero` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The position itself is false, and every existing immediate neighbour is false. A missing left or right neighbour is taken to be zero. Thus the two endpoint conditions are exactly the same as padding the word with a zero on each side.

**Definition 1.3 (Counting flippable zeros).**

$$\forall n \in \mathrm{Nat},\; \forall w \in \mathrm{Fin}\left(n\right) \to \mathrm{Bool},\; \mathrm{flippableZeroCount}\left(w\right) = \sum_{i: \mathrm{Fin}\left(n\right)} (\mathrm{ite}\left(\mathrm{FlippableZero}\left(w, i\right), 1, 0\right))$$

*Formalization.* `D5/S3/Combinatorics/Graph/LegalWordDegree.flippableZeroCount` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The count sums one for each flippable zero and zero for every other position.

**Theorem 1.4 (Degree equals additions plus removals).**

$$\forall n \in \mathrm{Nat},\; \forall b \in \{w: \mathrm{Fin}\left(n\right) \to \mathrm{Bool} \mid \mathrm{Adm}\left(n, w\right)\},\; \mathrm{degree}\left(\mathrm{legalWordGraph}\left(n\right), b\right) = \mathrm{flippableZeroCount}\left(\mathrm{val}\left(b\right)\right) + \mathrm{occupationCount}\left(\mathrm{val}\left(b\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/LegalWordDegree.degree_eq_flippable_add_occupation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Removing a one always preserves legality. Adding a one preserves legality exactly at a flippable zero. These legal flips give a bijection from the eligible positions to the actual neighbour set. A neighbour differs at exactly one position, so this accounts for every edge without duplication.

**Theorem 1.5 (The sharp bound and its complete equality condition).**

$$\forall n \in \mathrm{Nat},\; \forall b \in \{w: \mathrm{Fin}\left(n\right) \to \mathrm{Bool} \mid \mathrm{Adm}\left(n, w\right)\},\; \mathrm{flippableZeroCount}\left(\mathrm{val}\left(b\right)\right) + 2 \cdot \mathrm{occupationCount}\left(\mathrm{val}\left(b\right)\right) \le n + 1 \land \left(\mathrm{flippableZeroCount}\left(\mathrm{val}\left(b\right)\right) + 2 \cdot \mathrm{occupationCount}\left(\mathrm{val}\left(b\right)\right) = n + 1 \Leftrightarrow \left(\mathrm{Odd}\left(n\right) \land \left(\forall i \in \mathrm{Fin}\left(n\right),\; \mathrm{val}\left(b\right)\left(i\right) = \mathrm{decide}\left(\mathrm{val}\left(i\right) \bmod 2 = 0\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/LegalWordDegree.flippable_bound_and_equality` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every length and every legal word, u+2k is at most n+1. Equality holds exactly when n is odd and position i is true exactly when i is even. The proof separates a leading zero from a leading one followed by zero. Removing a leading zero preserves the tail's flippable positions and removes at most one extra flippable zero; equality is impossible in this branch. Removing a leading 10 preserves u and decreases k by one, reducing both the bound and the equality condition to the shorter word. The length-one word 1 attains equality. The empty word satisfies the strict inequality, and all-zero words, even lengths, and zero endpoints are included.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/LegalWordDegree.FlippableZero`
- Truth anchor: `D5/S3/Combinatorics/Graph/LegalWordDegree.degree_eq_flippable_add_occupation`
- Truth anchor: `D5/S3/Combinatorics/Graph/LegalWordDegree.flippableZeroCount`
- Truth anchor: `D5/S3/Combinatorics/Graph/LegalWordDegree.flippable_bound_and_equality`
- Truth anchor: `D5/S3/Combinatorics/Graph/LegalWordDegree.legalWordGraph`
- Dependency: [D5/S3/Combinatorics/Graph/Hypercube](Hypercube.md)
- Dependency: [D5/S3/Quantum/FockSpace/ForbiddenNeighbourDeterminant](../../Quantum/FockSpace/ForbiddenNeighbourDeterminant.md)
