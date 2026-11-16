# Quantitative Finite Subset Merging

## Abstract

A uniform pairwise length bound controls synchronization of finite uncertainty sets.

**Theorem 1.1 (A merging word of length at most one pair budget per additional state).**

$$\begin{gathered}\forall X: \operatorname{Type}(u), A: \operatorname{Type}(v),\\{}\forall t: X \to A \to X, L: \mathbb{N}, S: \operatorname{Finset}(X),\\{}(\forall x, y: X, \exists p: \operatorname{List}(A), \operatorname{length}(p) \leq L \land \operatorname{run}(t, p, x) = \operatorname{run}(t, p, y))\\{}\Rightarrow \exists w: \operatorname{List}(A), \operatorname{length}(w) \leq (\operatorname{card}(S) - 1) * L \land\\{}\forall x \in S, \forall y \in S, \operatorname{run}(t, w, x) = \operatorname{run}(t, w, y).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/FiniteSubsetMergingBound.exists_merging_word_length_le` (`✓ std3`). ∎

*Citation.* Ján Černý (1964). *Poznámka k homogénnym experimentom s konečnými automatmi*. URL: <https://dml.cz/bitstream/handle/10338.dmlcz/126647/MathSlov_14-1964-3_2.pdf>.

*Commentary.*

The state type X and letter type A range independently over arbitrary universes. The function t is any deterministic transition, L is a natural number, and S is a finite set of states. The notation run(t,w,x) means the native list left fold w.foldl t x, and length(w) is the list length. Natural subtraction is truncated at zero.

Assume every pair of ambient states can be merged by some word of length at most L. Then a single word of length at most (card(S) minus one) times L merges every pair in S. There are no finiteness, nonemptiness or decidable equality assumptions on either ambient type. Empty state or letter types, empty and singleton uncertainty sets, L equal to zero, and infinite ambient types are included.

Induct on the finite set. The empty set uses the empty word. For an inserted state a and a nonempty old set, first apply the old merging word u and choose an old representative b. Apply the pairwise hypothesis to the two states run(t,u,a) and run(t,u,b), obtaining v. The concatenation of u and v merges the inserted state with every old state; equality of old images is preserved by folding v. Its length is at most (card(S) minus one) times L plus L, hence card(S) times L. If the old set is empty, the inserted singleton again uses the empty word.

Černý's Theorem 2 gives the successive pair-merging mechanism for finite automata. The statement here exposes its uniform length estimate for a finite uncertainty set in an arbitrary ambient transition system.

## References

- Truth anchor: `D5/S1/Words/FiniteSubsetMergingBound.exists_merging_word_length_le`
