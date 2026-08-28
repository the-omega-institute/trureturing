# Power Traces Do Not Determine Similarity

## Abstract

Two explicit matrices have identical positive-power traces and characteristic polynomial but belong to different similarity classes.

**Theorem 1.1 (All power traces can miss the similarity class).**

$$\forall K: Type, \operatorname{Field}\left(K\right) \Rightarrow\ A = \operatorname{zeroMatrix}\left(2, K\right), N = \operatorname{single}\left(2, 0, 1, 1, K\right),\ (\forall k \in \mathbb{N}, 1 \le k \Rightarrow (\operatorname{tr}\left(A^{k}\right) = 0 \land \operatorname{tr}\left(N^{k}\right) = 0)) \land\ \operatorname{charpoly}\left(A\right) = X^{2} \land\ \operatorname{charpoly}\left(N\right) = X^{2} \land\ \operatorname{rank}\left(A\right) = 0 \land\ \operatorname{rank}\left(N\right) = 1 \land\ \neg (\exists P \in \operatorname{GL}\left(2, K\right): PAP^{-1} = N) \land\ \neg (\forall M, C \in \operatorname{Matrix}\left(2, 2, K\right), (\forall k \in \mathbb{N}, 1 \le k \Rightarrow \operatorname{tr}\left(M^{k}\right) = \operatorname{tr}\left(C^{k}\right)) \Rightarrow \exists P \in \operatorname{GL}\left(2, K\right): PMP^{-1} = C).$$

*Proof.* Machine-checked in Lean as `D5/S0/Observation/PowerTraceSimilarityCountermodel.power_traces_do_not_determine_similarity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Over an arbitrary field, take A to be the two-by-two zero matrix and N to have its only nonzero entry, one, in row zero and column one. The matrix N is nonzero and square-zero.

Every positive power of A and N has trace zero, and both characteristic polynomials are X squared. Their ranks are zero and one, so no invertible change of basis conjugates A to N. The same pair directly refutes the universal claim that all positive-power traces determine matrix similarity.

The result is stronger than the source's characteristic-zero context: the countermodel works over every field. Pinned Mathlib supplies the two-dimensional characteristic-polynomial formula and rank bounds, but no theorem packages this full countermodel.

## References

- Truth anchor: `D5/S0/Observation/PowerTraceSimilarityCountermodel.power_traces_do_not_determine_similarity`
