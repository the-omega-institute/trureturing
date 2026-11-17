# Rank-Dependent Finite Subset Compression

## Abstract

Local reductions of finite uncertainty sets give a cumulative bound with arbitrary costs at each rank.

**Theorem 1.1 (Summing local rank budgets produces one compressing word).**

$$\begin{gathered}\forall X: \operatorname{Type}(u), A: \operatorname{Type}(v), [\operatorname{DecidableEq}(X)],\\{}\forall t: X \to A \to X, C: \mathbb{N} \to \mathbb{N}, S: \operatorname{Finset}(X),\\{}(\forall T: \operatorname{Finset}(X), 2 \leq \operatorname{card}(T) \Rightarrow \exists p: \operatorname{List}(A),\\{}\operatorname{length}(p) \leq \operatorname{C}(\operatorname{card}(T)) \land \operatorname{card}(\operatorname{image}(t, p, T)) < \operatorname{card}(T))\\{}\Rightarrow \exists w: \operatorname{List}(A), \operatorname{length}(w) \leq \sum_{k \in \operatorname{range}(\operatorname{card}(S) - 1)} \operatorname{C}(k + 2) \land\\{}\operatorname{card}(\operatorname{image}(t, w, S)) \leq 1.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/FiniteSubsetCompressionBound.exists_compressing_word_length_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The state type X and letter type A range independently over arbitrary universes. The original decidable equality on X is retained. The map t is a deterministic transition and C is any natural-valued cost function. Write image(t,w,S) for the finite image of S under x mapped to the native list left fold w.foldl t x, and length(w) for list length. All subtraction is natural subtraction truncated at zero.

Assume every finite uncertainty set T of at least two states admits a word of length at most C(card(T)) whose image has strictly smaller cardinality. Then every finite S admits a word reducing its image to at most one state, of length at most the sum of C(2), C(3), through C(card(S)). No monotonicity of C is required. The ambient state and letter types need not be finite or nonempty. Empty and singleton S use the empty word and have zero total budget.

Strongly induct on the current cardinality. Above one state, choose a reducing word u and let U be its actual image. Apply the induction hypothesis to U, obtaining v, and concatenate u followed by v. The fold of the concatenation has exactly the same image as applying v to U. Since card(U) is strictly smaller than card(T), its prefix sum is bounded by the prefix ending at card(T) minus one. Adding the cost C(card(T)) gives the required total. Ranks skipped by one reduction contribute nonnegative unused terms, which is why the argument does not need a monotone cost profile.

The uniform pairwise result FiniteSubsetMergingBound.exists_merging_word_length_le supplies a different input interface and the product estimate (card(S) minus one) times L. Here the local hypothesis directly concerns a strict reduction of the entire current image and can provide different budgets at different ranks. This permits applying rank-specific compression estimates in finite automata, and also applies to finite uncertainty sets in infinite deterministic transition systems. The conclusion gives a word length bound; it does not provide a cost for finding the local words, a shortest-word theorem, a noisy recovery guarantee, or an original-state reconstruction.

## References

- Truth anchor: `D5/S1/Words/FiniteSubsetCompressionBound.exists_compressing_word_length_le`
