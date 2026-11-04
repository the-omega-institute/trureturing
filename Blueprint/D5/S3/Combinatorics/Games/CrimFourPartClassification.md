# Losing four-part CRIM positions

## Abstract

An unbounded classification of all losing four-part positions in normal-play CRIM.

**Definition 1.1 (The four-part classification).**

$$claim = (\forall a \in \mathbb{N},\; \forall b \in \mathbb{N},\; \forall c \in \mathbb{N},\; \forall d \in \mathbb{N},\; (1 \le d) \Rightarrow ((d \le c) \Rightarrow ((c \le b) \Rightarrow ((b \le a) \Rightarrow ((\operatorname{grundy}\left([a,b,c,d]\right) = 0) \Leftrightarrow ((\operatorname{Nat}.\operatorname{mod}\left(a, 2\right) = 0) \land (((2 \le d) \land (\neg((\operatorname{Nat}.\operatorname{mod}\left(b, 2\right) = 1) \land (\operatorname{Nat}.\operatorname{mod}\left(c, 2\right) = 1)))) \lor (((d = 1) \land ((c = 1) \land ((\operatorname{Nat}.\operatorname{mod}\left(b, 2\right) = 0) \lor (b = 1)))) \lor (((d = 1) \land ((2 \le c) \land (\operatorname{Nat}.\operatorname{mod}\left(b, 2\right) = 1))) \lor ((d = 1) \land ((c = 2) \land ((3 \le b) \lor (a = 2)))))))))))))$$

*Formalization.* `D5/S3/Combinatorics/Games/CrimFourPartClassification.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ina Bašić; Eric Gottlieb; Matjaž Krnc (2026). *CRIM: A Natural Game on Integer Partitions*. DOI: [10.48550/arXiv.2606.16828](https://doi.org/10.48550/arXiv.2606.16828). URL: <https://arxiv.org/abs/2606.16828v1>.

*Commentary.*

Section 5, Question 1, p. 17: “Which partitions consisting of four parts are losing?” The natural numbers a, b, c, d are the positive row lengths, ordered from largest to smallest. The function grundy is the original CRIM evaluator: a move deletes a row, or conjugates, deletes a row and conjugates back. Losing means Grundy value zero. The displayed equivalence answers the question on its entire four-part domain. Nat.mod is natural-number remainder; each remainder has divisor two. The four alternatives may overlap.

**Theorem 1.2 (Exactly the losing four-part positions).**

$$\forall a \in \mathbb{N},\; \forall b \in \mathbb{N},\; \forall c \in \mathbb{N},\; \forall d \in \mathbb{N},\; (1 \le d) \Rightarrow ((d \le c) \Rightarrow ((c \le b) \Rightarrow ((b \le a) \Rightarrow ((\operatorname{grundy}\left([a,b,c,d]\right) = 0) \Leftrightarrow ((\operatorname{Nat}.\operatorname{mod}\left(a, 2\right) = 0) \land (((2 \le d) \land (\neg((\operatorname{Nat}.\operatorname{mod}\left(b, 2\right) = 1) \land (\operatorname{Nat}.\operatorname{mod}\left(c, 2\right) = 1)))) \lor (((d = 1) \land ((c = 1) \land ((\operatorname{Nat}.\operatorname{mod}\left(b, 2\right) = 0) \lor (b = 1)))) \lor (((d = 1) \land ((2 \le c) \land (\operatorname{Nat}.\operatorname{mod}\left(b, 2\right) = 1))) \lor ((d = 1) \land ((c = 2) \land ((3 \le b) \lor (a = 2))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Games/CrimFourPartClassification.result` (`✓ std3`). ∎

*Resolves.* `Problems/crim-question-one-four-parts` (proved) by `D5/S3/Combinatorics/Games/CrimFourPartClassification.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"crim-question-one-four-parts","declaration_gid":"D5/S3/Combinatorics/Games/CrimFourPartClassification.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Ina Bašić; Eric Gottlieb; Matjaž Krnc (2026). *CRIM: A Natural Game on Integer Partitions*. DOI: [10.48550/arXiv.2606.16828](https://doi.org/10.48550/arXiv.2606.16828). URL: <https://arxiv.org/abs/2606.16828v1>.

*Commentary.*

The four alternatives, together with even a, are necessary and sufficient. The proof treats every sorted nonnegative quadruple after removing zero entries. Each legal column deletion subtracts one from the first one, two, three or four entries, with a strict gap at the cut. Together with the four row deletions these exhaust the moves. A losing candidate has no losing candidate as a follower; every other position has one. Strong induction on the number of cells, using the CRIM mex recursion and strict descent, therefore identifies the candidate predicate with Grundy value zero. For three positive parts the auxiliary predicate excludes the column [1,1,1]. There is no upper bound on a, b, c or d. The theorem determines zero versus nonzero, and does not determine the positive Grundy values or classify all positions with five rows.

## References

- Truth anchor: `D5/S3/Combinatorics/Games/CrimFourPartClassification.claim`
- Truth anchor: `D5/S3/Combinatorics/Games/CrimFourPartClassification.result`
- Dependency: [D5/S0/Certificates/Games/CrimGrundyRefutation](../../../S0/Certificates/Games/CrimGrundyRefutation.md)
