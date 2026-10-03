# Margins of alternating signed matrices

## Abstract

Signed row and column margins admit an alternating signed square matrix exactly when their total sums agree.

**Definition 1.1 (Signed integer entries).**

$$\forall x \in \mathrm{Int},\; (\operatorname{Signed}\left(x\right)) \Leftrightarrow ((x = -1) \lor ((x = 0) \lor (x = 1)))$$

*Formalization.* `D5/S3/Combinatorics/Latin/AlternatingSignMargins.Signed` (`✓ std3`).

*Citation.* A. Ernst, S. Lia, C. O'Brien, J. Sheekey, J. Zumbrägel (2026). *Generalising Latin square orthogonality and Frobenius-König with alternating sign matrices*. DOI: [10.48550/arXiv.2606.25884](https://doi.org/10.48550/arXiv.2606.25884). URL: <https://arxiv.org/abs/2606.25884v1>.

*Commentary.*

A signed integer is precisely one of minus one, zero and one.

**Definition 1.2 (Alternation along a line).**

$$\forall n \in \mathrm{Nat},\; \forall v \in \operatorname{Fin}\left(n\right) \to \mathrm{Int},\; (\operatorname{Alternates}\left(v\right)) \Leftrightarrow (\forall a \in \operatorname{Fin}\left(n\right),\; \forall b \in \operatorname{Fin}\left(n\right),\; (a < b) \Rightarrow ((\operatorname{v}\left(a\right) \ne 0) \Rightarrow ((\operatorname{v}\left(b\right) \ne 0) \Rightarrow ((\forall c \in \operatorname{Fin}\left(n\right),\; (a < c) \Rightarrow ((c < b) \Rightarrow (\operatorname{v}\left(c\right) = 0))) \Rightarrow (\operatorname{v}\left(a\right) \ne \operatorname{v}\left(b\right))))))$$

*Formalization.* `D5/S3/Combinatorics/Latin/AlternatingSignMargins.Alternates` (`✓ std3`).

*Citation.* A. Ernst, S. Lia, C. O'Brien, J. Sheekey, J. Zumbrägel (2026). *Generalising Latin square orthogonality and Frobenius-König with alternating sign matrices*. DOI: [10.48550/arXiv.2606.25884](https://doi.org/10.48550/arXiv.2606.25884). URL: <https://arxiv.org/abs/2606.25884v1>.

*Commentary.*

The line is indexed by Fin n in its natural order. Two nonzero entries with only zeros strictly between them must differ. For signed entries this means opposite signs; there is no restriction on the first or last sign.

**Definition 1.3 (The matrix class W).**

$$\forall n \in \mathrm{Nat},\; \operatorname{W}\left(n\right) = \operatorname{setOf}\left(\lambda X: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathrm{Int}\right). ((\forall i \in \operatorname{Fin}\left(n\right),\; \forall j \in \operatorname{Fin}\left(n\right),\; \operatorname{Signed}\left(\operatorname{X}\left(i, j\right)\right)) \land ((\forall i \in \operatorname{Fin}\left(n\right),\; \operatorname{Alternates}\left(\lambda j: \operatorname{Fin}\left(n\right). (\operatorname{X}\left(i, j\right))\right)) \land ((\forall j \in \operatorname{Fin}\left(n\right),\; \operatorname{Alternates}\left(\lambda i: \operatorname{Fin}\left(n\right). (\operatorname{X}\left(i, j\right))\right)) \land ((\forall i \in \operatorname{Fin}\left(n\right),\; \operatorname{Signed}\left(\sum_{j \in \operatorname{Fin}\left(n\right)} (\operatorname{X}\left(i, j\right))\right)) \land (\forall j \in \operatorname{Fin}\left(n\right),\; \operatorname{Signed}\left(\sum_{i \in \operatorname{Fin}\left(n\right)} (\operatorname{X}\left(i, j\right))\right))))))\right)$$

*Formalization.* `D5/S3/Combinatorics/Latin/AlternatingSignMargins.W` (`✓ std3`).

*Citation.* A. Ernst, S. Lia, C. O'Brien, J. Sheekey, J. Zumbrägel (2026). *Generalising Latin square orthogonality and Frobenius-König with alternating sign matrices*. DOI: [10.48550/arXiv.2606.25884](https://doi.org/10.48550/arXiv.2606.25884). URL: <https://arxiv.org/abs/2606.25884v1>.

*Commentary.*

Section 8, p. 27: “Section 4 introduces the set W_n consisting of all (0, ±1)-matrices in which the non-zero entries of each row and column alternate in sign, and the sum of each row/column is in {0, ±1}.” The encoding uses integer matrices with rows and columns indexed by Fin n. The setOf expression includes signed entries, row alternation, column alternation, signed row sums and signed column sums, in that order. A row function is j ↦ X(i,j), and a column function is i ↦ X(i,j). Empty lines satisfy alternation.

**Definition 1.4 (Problem 8.3 and its exact answer).**

$$(claim) \Leftrightarrow (\forall n \in \mathrm{Nat},\; \forall R \in \operatorname{Fin}\left(n\right) \to \mathrm{Int},\; \forall S \in \operatorname{Fin}\left(n\right) \to \mathrm{Int},\; (\forall i \in \operatorname{Fin}\left(n\right),\; \operatorname{Signed}\left(\operatorname{R}\left(i\right)\right)) \Rightarrow ((\forall j \in \operatorname{Fin}\left(n\right),\; \operatorname{Signed}\left(\operatorname{S}\left(j\right)\right)) \Rightarrow ((\exists X \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathrm{Int}\right),\; (X \in \operatorname{W}\left(n\right)) \land ((\forall i \in \operatorname{Fin}\left(n\right),\; \sum_{j \in \operatorname{Fin}\left(n\right)} (\operatorname{X}\left(i, j\right)) = \operatorname{R}\left(i\right)) \land (\forall j \in \operatorname{Fin}\left(n\right),\; \sum_{i \in \operatorname{Fin}\left(n\right)} (\operatorname{X}\left(i, j\right)) = \operatorname{S}\left(j\right)))) \Leftrightarrow (\sum_{i \in \operatorname{Fin}\left(n\right)} (\operatorname{R}\left(i\right)) = \sum_{j \in \operatorname{Fin}\left(n\right)} (\operatorname{S}\left(j\right))))))$$

*Formalization.* `D5/S3/Combinatorics/Latin/AlternatingSignMargins.claim` (`✓ std3`).

*Citation.* A. Ernst, S. Lia, C. O'Brien, J. Sheekey, J. Zumbrägel (2026). *Generalising Latin square orthogonality and Frobenius-König with alternating sign matrices*. DOI: [10.48550/arXiv.2606.25884](https://doi.org/10.48550/arXiv.2606.25884). URL: <https://arxiv.org/abs/2606.25884v1>.

*Commentary.*

Section 8, p. 27: “Problem 8.3. For which (0, ±1)-vectors R and S of order n does there exist X ∈ W_n with row-sums R and column-sums S?” Section 8, p. 27: “Section 4 introduces the set W_n consisting of all (0, ±1)-matrices in which the non-zero entries of each row and column alternate in sign, and the sum of each row/column is in {0, ±1}.” The quantified proposition encodes the complete answer: equality of the two total sums is necessary and sufficient. Both vectors have integer entries in {−1,0,1}; every sum ranges over all of Fin n. All natural orders, including zero, are included.

**Theorem 1.5 (Equal totals are the only obstruction).**

$$\forall n \in \mathrm{Nat},\; \forall R \in \operatorname{Fin}\left(n\right) \to \mathrm{Int},\; \forall S \in \operatorname{Fin}\left(n\right) \to \mathrm{Int},\; (\forall i \in \operatorname{Fin}\left(n\right),\; \operatorname{Signed}\left(\operatorname{R}\left(i\right)\right)) \Rightarrow ((\forall j \in \operatorname{Fin}\left(n\right),\; \operatorname{Signed}\left(\operatorname{S}\left(j\right)\right)) \Rightarrow ((\exists X \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathrm{Int}\right),\; (X \in \operatorname{W}\left(n\right)) \land ((\forall i \in \operatorname{Fin}\left(n\right),\; \sum_{j \in \operatorname{Fin}\left(n\right)} (\operatorname{X}\left(i, j\right)) = \operatorname{R}\left(i\right)) \land (\forall j \in \operatorname{Fin}\left(n\right),\; \sum_{i \in \operatorname{Fin}\left(n\right)} (\operatorname{X}\left(i, j\right)) = \operatorname{S}\left(j\right)))) \Leftrightarrow (\sum_{i \in \operatorname{Fin}\left(n\right)} (\operatorname{R}\left(i\right)) = \sum_{j \in \operatorname{Fin}\left(n\right)} (\operatorname{S}\left(j\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Latin/AlternatingSignMargins.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Summing all entries in either order gives necessity. For sufficiency, orient the margins so that the positive row count is at least the positive column count. Equality of totals makes the positive and negative row surpluses equal. Match the required signed columns to rows of the same sign and place each remaining positive-negative row pair in its own zero-margin column. The zero-column capacity follows from the three sign-class counts. Rows then have at most one nonzero entry, and columns at most one of each sign, so every line alternates. Transposition handles the other orientation.

## References

- Truth anchor: `D5/S3/Combinatorics/Latin/AlternatingSignMargins.Alternates`
- Truth anchor: `D5/S3/Combinatorics/Latin/AlternatingSignMargins.Signed`
- Truth anchor: `D5/S3/Combinatorics/Latin/AlternatingSignMargins.W`
- Truth anchor: `D5/S3/Combinatorics/Latin/AlternatingSignMargins.claim`
- Truth anchor: `D5/S3/Combinatorics/Latin/AlternatingSignMargins.result`
