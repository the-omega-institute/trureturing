# Row Counting and Row Reversal

## Abstract

Row and column counting are interchangeable, and reversing the rows complements the total ascent count.

**Definition 1.1 (Row ascent count).**

$$\forall n \in \mathrm{Nat},\; \forall L \in \operatorname{Fin}\left(n\right) \to \left(\operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(n\right)\right),\; \forall j \in \mathrm{Nat},\; \operatorname{rowAscents}\left(n, L, j\right) = \operatorname{card}\left(\{c \in \operatorname{Fin}\left(n\right)| j + 1 < n \land \operatorname{L}\left(j, c\right) < \operatorname{L}\left(j + 1, c\right)\}\right)$$

*Formalization.* `D5/S3/Combinatorics/LatinEulerianCounting.rowAscents` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Madjid Mirzavaziri, Daniel Yaqubi (2026). *Latin Eulerian Numbers*. DOI: [10.48550/arXiv.2609.25100](https://doi.org/10.48550/arXiv.2609.25100). URL: <https://arxiv.org/abs/2609.25100v1>.

*Commentary.*

For adjacent rows, count the columns whose entries increase from the first row to the second.

**Definition 1.2 (Row reversal).**

$$\forall n \in \mathrm{Nat},\; \forall L \in \operatorname{Fin}\left(n\right) \to \left(\operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(n\right)\right),\; \operatorname{reverseRows}\left(n, L\right) = \operatorname{fun}\left(i, c, \operatorname{L}\left(\operatorname{rev}\left(i\right), c\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/LatinEulerianCounting.reverseRows` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Madjid Mirzavaziri, Daniel Yaqubi (2026). *Latin Eulerian Numbers*. DOI: [10.48550/arXiv.2609.25100](https://doi.org/10.48550/arXiv.2609.25100). URL: <https://arxiv.org/abs/2609.25100v1>.

*Commentary.*

ReverseRows reads the original square at the reversed row index and leaves columns unchanged.

**Theorem 1.3 (Complementary row pair counts).**

$$\forall n \in \mathrm{Nat},\; \forall L \in \operatorname{Fin}\left(n\right) \to \left(\operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(n\right)\right),\; \forall j \in \mathrm{Nat},\; \left(2 \le n \land \left(\operatorname{IsLatin}\left(n, L\right) \land j < n - 1\right)\right) \Rightarrow \operatorname{rowAscents}\left(n, \operatorname{reverseRows}\left(n, L\right), j\right) + \operatorname{rowAscents}\left(n, L, n - 2 - j\right) = n$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/LatinEulerianCounting.rowAscents_reverse_add` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Madjid Mirzavaziri, Daniel Yaqubi (2026). *Latin Eulerian Numbers*. DOI: [10.48550/arXiv.2609.25100](https://doi.org/10.48550/arXiv.2609.25100). URL: <https://arxiv.org/abs/2609.25100v1>.

*Commentary.*

For a Latin square, each reversed adjacent row pair has a complementary ascent count, summing to the order.

**Theorem 1.4 (Reversal identity).**

$$\forall n \in \mathrm{Nat},\; \forall L \in \operatorname{Fin}\left(n\right) \to \left(\operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(n\right)\right),\; \left(2 \le n \land \operatorname{IsLatin}\left(n, L\right)\right) \Rightarrow \operatorname{totalAscents}\left(n, \operatorname{reverseRows}\left(n, L\right)\right) + \operatorname{totalAscents}\left(n, L\right) = n \cdot \left(n - 1\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/LatinEulerianCounting.total_reverse` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Madjid Mirzavaziri, Daniel Yaqubi (2026). *Latin Eulerian Numbers*. DOI: [10.48550/arXiv.2609.25100](https://doi.org/10.48550/arXiv.2609.25100). URL: <https://arxiv.org/abs/2609.25100v1>.

*Commentary.*

Reversing all rows exchanges ascent and descent in every column comparison, so the two totals sum to n times n minus one.

## References

- Truth anchor: `D5/S3/Combinatorics/LatinEulerianCounting.reverseRows`
- Truth anchor: `D5/S3/Combinatorics/LatinEulerianCounting.rowAscents`
- Truth anchor: `D5/S3/Combinatorics/LatinEulerianCounting.rowAscents_reverse_add`
- Truth anchor: `D5/S3/Combinatorics/LatinEulerianCounting.total_reverse`
- Dependency: [D5/S3/Combinatorics/LatinEulerianDefs](LatinEulerianDefs.md)
