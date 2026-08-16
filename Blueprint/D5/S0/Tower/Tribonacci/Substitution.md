# Tribonacci Substitution

## Abstract

One-level refinement of Tribonacci names realizes a three-letter gap substitution.

Appending a final zero embeds every old admissible name at the same real value. Deleting the final digit controls all fine names between two embedded endpoints and forces any inserted value to one exact position.

**Definition 1.1 (Level embedding of Tribonacci names).**

$$\forall Q \in N,\; \forall i \in \operatorname{coarseIndex}\left(Q\right),\; \operatorname{levelEmbedding}\left(Q, i\right) = \operatorname{indexOf}\left(Q + 1, \operatorname{appendZero}\left(\operatorname{nameAt}\left(Q, i\right)\right)\right)$$

*Formalization.* `D5/S0/Tower/Tribonacci/Substitution.levelEmbedding` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The embedding is the fine-level index of the old word with one final false digit. Admissibility is preserved because no new terminal run of three true digits can be created.

**Theorem 1.2 (Level embedding preserves value).**

$$\forall Q \in N,\; \forall i \in \operatorname{coarseIndex}\left(Q\right),\; \operatorname{indexedValue}\left(Q + 1, \operatorname{levelEmbedding}\left(Q, i\right)\right) = \operatorname{indexedValue}\left(Q, i\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/Tribonacci/Substitution.levelEmbedding_value` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The final false digit contributes zero, while every prior digit keeps the same exponent. Strict increase of indexed values then makes the embedding strictly monotone.

**Definition 1.3 (Inserted Tribonacci name indices).**

$$\forall Q \in N,\; \operatorname{insertedNameIndices}\left(Q, i\right) = \operatorname{openIndexInterval}\left(\operatorname{levelEmbedding}\left(Q, \operatorname{gapLeft}\left(Q, i\right)\right), \operatorname{levelEmbedding}\left(Q, \operatorname{gapRight}\left(Q, i\right)\right)\right)$$

*Formalization.* `D5/S0/Tower/Tribonacci/Substitution.insertedNameIndices` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a coarse adjacent interval, the inserted set is exactly the open finite-index interval between its two embedded endpoints.

**Theorem 1.4 (Inserted indices are exactly the intermediate values).**

$$\forall Q \in N,\; \forall j \in \operatorname{fineIndex}\left(Q\right),\; \operatorname{member}\left(j, \operatorname{insertedNameIndices}\left(Q, i\right)\right) = \operatorname{strictlyBetweenEndpointValues}\left(Q, i, j\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/Tribonacci/Substitution.mem_insertedNameIndices_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Strict monotonicity converts membership in the open index interval to strict inequalities between the corresponding real values.

**Theorem 1.5 (Exact Tribonacci gap insertion count).**

$$\forall Q \in N,\; \operatorname{insertedCount}\left(Q, i\right) = \operatorname{tribonacciInsertionCount}\left(\operatorname{gapType}\left(Q, i\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/Tribonacci/Substitution.tribonacci_gap_insertion_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A small coarse gap inserts no name. Large and combined coarse gaps each insert exactly one. Truncating a fine name proves uniqueness; the next-level three-gap spectrum proves existence in both non-small cases.

**Theorem 1.6 (Tribonacci three-letter gap substitution).**

$$\operatorname{substitute}\left(\mathit{small}\right) = \operatorname{gapWord}\left(\mathit{large}\right) \land \left(\operatorname{substitute}\left(\mathit{large}\right) = \operatorname{gapWord}\left(\mathit{large}, \mathit{combined}\right) \land \operatorname{substitute}\left(\mathit{combined}\right) = \operatorname{gapWord}\left(\mathit{large}, \mathit{small}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/Tribonacci/Substitution.tribonacci_gap_substitution` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At level Q plus one the new large length is t^-(Q+1), the new small length is t^-(Q+2), and the new combined length is the sum of t^-(Q+2) and t^-(Q+3). The unique inserted point, when present, always lies one new-large length from the left endpoint.

Pinned mathlib was searched first. Fin.snoc, Fin.init, Fin.sum_univ_castSucc, and Fin.card_Ioo provide the tuple, value, and interval infrastructure; the Tribonacci-specific dynamics are proved in this repository.

## References

- Truth anchor: `D5/S0/Tower/Tribonacci/Substitution.insertedNameIndices`
- Truth anchor: `D5/S0/Tower/Tribonacci/Substitution.levelEmbedding`
- Truth anchor: `D5/S0/Tower/Tribonacci/Substitution.levelEmbedding_value`
- Truth anchor: `D5/S0/Tower/Tribonacci/Substitution.mem_insertedNameIndices_iff`
- Truth anchor: `D5/S0/Tower/Tribonacci/Substitution.tribonacci_gap_insertion_count`
- Truth anchor: `D5/S0/Tower/Tribonacci/Substitution.tribonacci_gap_substitution`
- Dependency: [D5/S0/Tower/Tribonacci/Gaps](Gaps.md)
