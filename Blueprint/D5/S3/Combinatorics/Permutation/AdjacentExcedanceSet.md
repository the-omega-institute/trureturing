# Adjacent excedance and nonexcedance

## Abstract

An adjacent swap and two deletions split an exact-excedance permutation class.

The bracket recurrence is due to Richard Ehrenborg and Einar Steingrímsson, The excedance set of a permutation, Proposition 2.1, DOI 10.1006/aama.1999.0671. The formalization uses zero-based positions.

**Definition 1.1 (Exact strict excedances).**

$$\forall n \in \mathbb{N}, \forall S: \operatorname{Set}\left(\operatorname{Fin}\left(n\right)\right), \forall p: \operatorname{Perm}\left(\operatorname{Fin}\left(n\right)\right), \operatorname{HasExactExcedances}\left(p, S\right) \iff (\forall j: \operatorname{Fin}\left(n\right), j < \operatorname{p}\left(j\right) \iff j \in S)$$

*Formalization.* `D5/S3/Combinatorics/Permutation/AdjacentExcedanceSet.HasExactExcedances` (`✓ std3`).

*Citation.* Richard Ehrenborg; Einar Steingrímsson (2000). *The Excedance Set of a Permutation*. DOI: [10.1006/aama.1999.0671](https://doi.org/10.1006/aama.1999.0671). URL: <https://doi.org/10.1006/aama.1999.0671>.

*Commentary.*

Every position j has p(j) greater than j exactly when j belongs to S.

**Definition 1.2 (Subtype of actual permutations).**

$$\forall n \in \mathbb{N}, \forall S: \operatorname{Set}\left(\operatorname{Fin}\left(n\right)\right), \operatorname{ExactPermutations}\left(S\right) = \{ p: \operatorname{Perm}\left(\operatorname{Fin}\left(n\right)\right) \mid \operatorname{HasExactExcedances}\left(p, S\right) \}$$

*Formalization.* `D5/S3/Combinatorics/Permutation/AdjacentExcedanceSet.ExactPermutations` (`✓ std3`).

*Citation.* Richard Ehrenborg; Einar Steingrímsson (2000). *The Excedance Set of a Permutation*. DOI: [10.1006/aama.1999.0671](https://doi.org/10.1006/aama.1999.0671). URL: <https://doi.org/10.1006/aama.1999.0671>.

*Commentary.*

The subtype of permutations of Fin(n) whose exact strict excedance set is S.

**Definition 1.3 (Cardinality of the prescribed subtype).**

$$\forall n \in \mathbb{N}, \forall S: \operatorname{Set}\left(\operatorname{Fin}\left(n\right)\right), \operatorname{exactCount}\left(S\right) = \operatorname{card}\left(\operatorname{ExactPermutations}\left(S\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Permutation/AdjacentExcedanceSet.exactCount` (`✓ std3`).

*Citation.* Richard Ehrenborg; Einar Steingrímsson (2000). *The Excedance Set of a Permutation*. DOI: [10.1006/aama.1999.0671](https://doi.org/10.1006/aama.1999.0671). URL: <https://doi.org/10.1006/aama.1999.0671>.

*Commentary.*

Take the natural cardinality of the subtype of permutations with exact set S.

**Definition 1.4 (Swap two input positions).**

$$\forall n \in \mathbb{N}, \forall a, b: \operatorname{Fin}\left(n\right), \forall p: \operatorname{Perm}\left(\operatorname{Fin}\left(n\right)\right), \operatorname{swapPositions}\left(a, b, p\right) = p \circ \operatorname{swap}\left(a, b\right)$$

*Formalization.* `D5/S3/Combinatorics/Permutation/AdjacentExcedanceSet.swapPositions` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Richard Ehrenborg; Einar Steingrímsson (2000). *The Excedance Set of a Permutation*. DOI: [10.1006/aama.1999.0671](https://doi.org/10.1006/aama.1999.0671). URL: <https://doi.org/10.1006/aama.1999.0671>.

*Commentary.*

Precompose the permutation by the transposition of positions a and b. This acts on the type of permutations by an involution.

**Definition 1.5 (Delete a fixed nonexcedance).**

$$\forall n \in \mathbb{N}, \forall b: \operatorname{Fin}\left(n+1\right), \forall S: \operatorname{Set}\left(\operatorname{Fin}\left(n+1\right)\right), \neg (b \in S) \implies \{ p: \operatorname{ExactPermutations}\left(S\right) \mid \operatorname{p}\left(b\right) = b \} \equiv \operatorname{ExactPermutations}\left(\operatorname{preimage}\left(\operatorname{succAbove}\left(b\right), S\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Permutation/AdjacentExcedanceSet.deleteFixedCase` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Richard Ehrenborg; Einar Steingrímsson (2000). *The Excedance Set of a Permutation*. DOI: [10.1006/aama.1999.0671](https://doi.org/10.1006/aama.1999.0671). URL: <https://doi.org/10.1006/aama.1999.0671>.

*Commentary.*

Restrict to the complement of the fixed position b, and reindex positions and values by the order embedding that skips b. The inverse extends the permutation and fixes b.

**Lemma 1.6 (Swap the left hit into a fixed point).**

$$\forall n \in \mathbb{N}, \forall a: \operatorname{Fin}\left(n+1\right), \forall S: \operatorname{Set}\left(\operatorname{Fin}\left(n+2\right)\right), \operatorname{castSucc}\left(a\right) \in S \land \neg (\operatorname{succ}\left(a\right) \in S) \implies \forall p: \operatorname{Perm}\left(\operatorname{Fin}\left(n+2\right)\right), (\operatorname{HasExactExcedances}\left(p, S\right) \land \operatorname{p}\left(\operatorname{castSucc}\left(a\right)\right) = \operatorname{succ}\left(a\right)) \iff (\operatorname{HasExactExcedances}\left(\operatorname{swapPositions}\left(\operatorname{castSucc}\left(a\right), \operatorname{succ}\left(a\right), p\right), S \setminus \{ \operatorname{castSucc}\left(a\right) \}\right) \land \operatorname{apply}\left(\operatorname{swapPositions}\left(\operatorname{castSucc}\left(a\right), \operatorname{succ}\left(a\right), p\right), \operatorname{succ}\left(a\right)\right) = \operatorname{succ}\left(a\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Permutation/AdjacentExcedanceSet.exact_swap_fixed_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Richard Ehrenborg; Einar Steingrímsson (2000). *The Excedance Set of a Permutation*. DOI: [10.1006/aama.1999.0671](https://doi.org/10.1006/aama.1999.0671). URL: <https://doi.org/10.1006/aama.1999.0671>.

*Commentary.*

The left position belongs to S and its right neighbor does not. A permutation with set S that sends the left position to the right one becomes a permutation fixing the right position after swapping their inputs. The swap removes only the left position from S.

**Lemma 1.7 (Reindex the prescribed set after deletion).**

$$\forall n \in \mathbb{N}, \forall a: \operatorname{Fin}\left(n+1\right), \forall S: \operatorname{Set}\left(\operatorname{Fin}\left(n+2\right)\right), \neg (\operatorname{succ}\left(a\right) \in S) \implies \operatorname{preimage}\left(\operatorname{succAbove}\left(\operatorname{succ}\left(a\right)\right), S \setminus \{ \operatorname{castSucc}\left(a\right) \}\right) = \operatorname{preimage}\left(\operatorname{succAbove}\left(\operatorname{castSucc}\left(a\right)\right), S\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Permutation/AdjacentExcedanceSet.delete_swap_set` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Richard Ehrenborg; Einar Steingrímsson (2000). *The Excedance Set of a Permutation*. DOI: [10.1006/aama.1999.0671](https://doi.org/10.1006/aama.1999.0671). URL: <https://doi.org/10.1006/aama.1999.0671>.

*Commentary.*

The right position is outside S. Pulling back S with the left position removed along the embedding skipping the right position gives the same set as pulling back S along the embedding skipping the left.

**Theorem 1.8 (The three-way adjacent bracket recurrence).**

$$\forall n \in \mathbb{N}, \forall a: \operatorname{Fin}\left(n+1\right), \forall S: \operatorname{Set}\left(\operatorname{Fin}\left(n+2\right)\right), \operatorname{castSucc}\left(a\right) \in S \land \neg (\operatorname{succ}\left(a\right) \in S) \implies \operatorname{exactCount}\left(S\right) = \operatorname{exactCount}\left(\operatorname{preimage}\left(\operatorname{swap}\left(\operatorname{castSucc}\left(a\right), \operatorname{succ}\left(a\right)\right), S\right)\right)+\operatorname{exactCount}\left(\operatorname{preimage}\left(\operatorname{succAbove}\left(\operatorname{succ}\left(a\right)\right), S\right)\right)+\operatorname{exactCount}\left(\operatorname{preimage}\left(\operatorname{succAbove}\left(\operatorname{castSucc}\left(a\right)\right), S\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Permutation/AdjacentExcedanceSet.adjacentBA` (`✓ std3`). ∎

*Citation.* Richard Ehrenborg; Einar Steingrímsson (2000). *The Excedance Set of a Permutation*. DOI: [10.1006/aama.1999.0671](https://doi.org/10.1006/aama.1999.0671). URL: <https://doi.org/10.1006/aama.1999.0671>.

*Commentary.*

At an adjacent excedance and nonexcedance, split by whether the right position is fixed, the left position hits the right value, or neither does. The first two alternatives give the order-preserving deletions. In the third, swapping the two inputs swaps their prescribed membership and preserves the rest.

## References

- Truth anchor: `D5/S3/Combinatorics/Permutation/AdjacentExcedanceSet.ExactPermutations`
- Truth anchor: `D5/S3/Combinatorics/Permutation/AdjacentExcedanceSet.HasExactExcedances`
- Truth anchor: `D5/S3/Combinatorics/Permutation/AdjacentExcedanceSet.adjacentBA`
- Truth anchor: `D5/S3/Combinatorics/Permutation/AdjacentExcedanceSet.deleteFixedCase`
- Truth anchor: `D5/S3/Combinatorics/Permutation/AdjacentExcedanceSet.delete_swap_set`
- Truth anchor: `D5/S3/Combinatorics/Permutation/AdjacentExcedanceSet.exactCount`
- Truth anchor: `D5/S3/Combinatorics/Permutation/AdjacentExcedanceSet.exact_swap_fixed_iff`
- Truth anchor: `D5/S3/Combinatorics/Permutation/AdjacentExcedanceSet.swapPositions`
