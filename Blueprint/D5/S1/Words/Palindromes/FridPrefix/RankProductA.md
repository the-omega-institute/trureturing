# A product potential bounds every accepted paired chunk word

## Abstract

A product potential bounds every accepted paired chunk word

**Theorem 1.1 (a_endpoint_score_bound).**

$$\forall xs \in List\left(tuple\left(\mathbb{N}, \mathbb{N}\right)\right),\; mem\left(xs, accepts\left(chunkEndpoint\left(6\right)\right)\right) \Rightarrow chunkScore\left(rankA, map\left(snd, xs\right)\right) \le chunkScore\left(rankA, map\left(fst, xs\right)\right) + 1$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Palindromes/FridPrefix/RankProductA.a_endpoint_score_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A forward induction retains the grouped reachable product states. A backward induction from the accepting endpoint retains the co-accessible masks. The integer potential inequalities telescope the score difference to at most one. The finite checks are reduced by the Lean kernel in seventeen separate endpoint-state blocks.

## References

- Truth anchor: `D5/S1/Words/Palindromes/FridPrefix/RankProductA.a_endpoint_score_bound`
- Dependency: [D5/S1/Words/Palindromes/FridPrefix/ProductChecker](ProductChecker.md)
- Dependency: [D5/S1/Words/Palindromes/FridPrefix/ProductDataA](ProductDataA.md)
- Dependency: [D5/S1/Words/Palindromes/FridPrefix/ProductMovesA](ProductMovesA.md)
- Dependency: [D5/S1/Words/Palindromes/FridPrefix/ProductPotentialsA](ProductPotentialsA.md)
- Dependency: [D5/S1/Words/Palindromes/FridPrefix/RankA](RankA.md)
