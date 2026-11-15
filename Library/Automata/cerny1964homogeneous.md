---
bibkey: cerny1964homogeneous
authors: Ján Černý
year: 1964
title: "Poznámka k homogénnym experimentom s konečnými automatmi"
doi: null
url: https://dml.cz/bitstream/handle/10338.dmlcz/126647/MathSlov_14-1964-3_2.pdf
claim: "Theorem 2, printed page 211, proves that a finite automaton is synchronizing exactly when every pair of states can be merged, by successive concatenation of pair-merging words."
strata_touched:
  - D5/S1/Words/FiniteSubsetMergingBound
license: "Mathematical citation only; no copied prose or figures. The digitized article is provided for personal use under the terms printed in its cover sheet."
triage: anchor
---

# Pairwise merging and synchronization

## Verified locator

https://dml.cz/bitstream/handle/10338.dmlcz/126647/MathSlov_14-1964-3_2.pdf

Ján Černý, *Poznámka k homogénnym experimentom s konečnými automatmi*,
Matematicko-fyzikálny časopis 14 (1964), no. 3, 208–216.
Theorem 2, printed page 211, characterizes synchronizing finite automata
by the existence of a merging word for every pair of states. Its proof
concatenates successive pair-merging words and needs at most one fewer
stage than the number of states.

`FiniteSubsetMergingBound.exists_merging_word_length_le` uses this
concatenation mechanism for a finite uncertainty set inside an arbitrary
ambient transition system. It assumes a uniform pairwise length bound L
and makes the resulting bound `(S.card - 1) * L` explicit. Neither the
state type nor the letter type is assumed finite or nonempty. This
quantified extension and its empty-set conventions are not a claim that
the article states the exact Lean telescope. No mathematical novelty is
claimed for the concatenation argument or the resulting estimate.
