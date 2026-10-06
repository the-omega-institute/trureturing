# Integral ranks accumulated on finite chunk runs

## Abstract

Integral ranks accumulated on finite chunk runs

**Definition 1.1 (ChunkRank).**

$$ChunkRank:Type$$

*Formalization.* `D5/S1/Words/Palindromes/FridPrefix/RankAutomata.ChunkRank` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

ChunkRank is the record with width : Nat, initial : Nat, transitions : Array (Array Nat), and weights : Array (Array Int). Transitions outside the stored arrays use destination 0 and weight 0 in the evaluator.

**Definition 1.2 (chunkScore).**

$$\forall r \in ChunkRank,\; \forall xs \in List\left(\mathbb{N}\right),\; chunkScore\left(r, xs\right) = snd\left(foldl\left(\lambda (s:tuple\left(\mathbb{N}, \mathbb{Z}\right)) \mapsto \lambda (x:\mathbb{N}) \mapsto tuple\left(getD\left(getD\left(transitions\left(r\right), fst\left(s\right), emptyArray\right), x, 0\right), snd\left(s\right) + getD\left(getD\left(weights\left(r\right), fst\left(s\right), emptyArray\right), x, 0\right)\right), tuple\left(initial\left(r\right), 0\right), xs\right)\right)$$

*Formalization.* `D5/S1/Words/Palindromes/FridPrefix/RankAutomata.chunkScore` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The state and accumulated integer weight are updated together. No terminal weight is added; the second coordinate of the final pair is the score.

## References

- Truth anchor: `D5/S1/Words/Palindromes/FridPrefix/RankAutomata.ChunkRank`
- Truth anchor: `D5/S1/Words/Palindromes/FridPrefix/RankAutomata.chunkScore`
