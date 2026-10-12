# The odd-dimensional improvement

## Abstract

In every odd dimension at least eleven, one more member than the chain guarantee is unavoidable. A balanced binary rank word of even length at least twelve has either three equally spaced consecutive occurrences of one colour or a balanced interval of length twelve. Balanced colourings of twelve ranks admit a seven-member monochromatic sublattice.

**Definition 1.1 (Equally spaced consecutive occurrences).**

$$\forall g \in \mathrm{Nat} \to \mathrm{Bool},\; \forall n \in \mathrm{Nat},\; \operatorname{ConsecutiveAP}\left(g, n\right) \Leftrightarrow \left(\exists a \in \mathrm{Nat},\; \exists b \in \mathrm{Nat},\; \exists c \in \mathrm{Nat},\; a < b \land \left(b < c \land \left(c \le n \land \left(a + c = \operatorname{mul}\left(2, b\right) \land \left(\operatorname{g}\left(a\right) = \operatorname{g}\left(b\right) \land \left(\operatorname{g}\left(b\right) = \operatorname{g}\left(c\right) \land \left(\left(\forall r \in \mathrm{Nat},\; \left(a < r \land r < b\right) \Rightarrow \left(\neg \operatorname{g}\left(r\right) = \operatorname{g}\left(b\right)\right)\right) \land \left(\forall r \in \mathrm{Nat},\; \left(b < r \land r < c\right) \Rightarrow \left(\neg \operatorname{g}\left(r\right) = \operatorname{g}\left(b\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/ErdosUlam/SublatticeChainBound.ConsecutiveAP` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The ranks a, b, c have one colour and equal positive gaps. Every rank strictly between a and b or between b and c has the other colour.

**Definition 1.2 (Balanced interval of length twelve).**

$$\forall g \in \mathrm{Nat} \to \mathrm{Bool},\; \forall b \in \mathrm{Nat},\; \operatorname{BalancedWindow}\left(g, b\right) \Leftrightarrow \operatorname{card}\left(\operatorname{filter}\left(\operatorname{range}\left(12\right), \operatorname{trueAtOffset}\left(g, b\right)\right)\right) = 6$$

*Formalization.* `D5/S3/Combinatorics/ErdosUlam/SublatticeChainBound.BalancedWindow` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The interval beginning at b contains six true ranks and six false ranks.

**Theorem 1.3 (The balanced rank-word alternative).**

$$\forall g \in \mathrm{Nat} \to \mathrm{Bool},\; \forall n \in \mathrm{Nat},\; \left(11 \le n \land \left(\operatorname{Odd}\left(n\right) \land \operatorname{card}\left(\operatorname{filter}\left(\operatorname{range}\left(n + 1\right), \operatorname{trueAtOffset}\left(g, 0\right)\right)\right) = \operatorname{div}\left(n + 1, 2\right)\right)\right) \Rightarrow \left(\operatorname{ConsecutiveAP}\left(g, n\right) \lor \left(\exists b \in \mathrm{Nat},\; b + 11 \le n \land \operatorname{BalancedWindow}\left(g, b\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ErdosUlam/SublatticeChainBound.rank_word_lemma` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An equally spaced consecutive triple is present in each of the local words 000, 111, 01010, 10101, 0110110 and 1001001. Extend a word one letter at a time, excluding those suffixes and balanced suffixes of length twelve. The resulting collection is empty at length fifteen. At length fourteen none of its words has seven letters of each colour. A balanced word of length twelve is already the required interval. These three cases cover every even length at least twelve.

**Theorem 1.4 (Balanced rank colourings).**

$$\forall g \in \mathrm{Nat} \to \mathrm{Bool},\; \operatorname{card}\left(\operatorname{filter}\left(\operatorname{trueRanks}\left(g\right), \operatorname{range}\left(12\right)\right)\right) = 6 \Rightarrow \left(\exists L \in \operatorname{Finset}\left(\operatorname{Finset}\left(\operatorname{Fin}\left(11\right)\right)\right),\; \operatorname{IsSublattice}\left(L\right) \land \left(\operatorname{Monochromatic}\left(\operatorname{rankColouring}\left(g\right), L\right) \land 7 \le \operatorname{card}\left(L\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ErdosUlam/SublatticeChainBound.balanced_rank_base` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Of the 924 balanced rank patterns, 874 contain three consecutive occurrences of one colour in arithmetic progression. The corresponding diamond augments the six same-colour prefixes. Each of the remaining fifty patterns is covered by one of ten bitmask families closed under union and intersection, with seven or eight distinct members.

**Definition 1.5 (Guaranteed size).**

$$\forall n \in \mathrm{Nat},\; \operatorname{f}\left(n\right) = \min_{chi: \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right) \to \mathrm{Bool}} \max_{L: \operatorname{Finset}\left(\operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right)\right), \operatorname{IsSublattice}\left(L\right) \land \operatorname{Monochromatic}\left(chi, L\right)} \operatorname{card}\left(L\right)$$

*Formalization.* `D5/S3/Combinatorics/ErdosUlam/SublatticeChainBound.f` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Minimize over all colourings the largest cardinality of a monochromatic sublattice.

**Definition 1.6 (Proposed formula).**

$$claim \Leftrightarrow \left(\forall n \in \mathrm{Nat},\; \operatorname{f}\left(n\right) = \left\lfloor\frac{n + 2}{2}\right\rfloor\right)$$

*Formalization.* `D5/S3/Combinatorics/ErdosUlam/SublatticeChainBound.claim` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The proposed equality is asserted in every natural dimension.

**Theorem 1.7 (The odd-dimensional lower bound).**

$$\forall n \in \mathrm{Nat},\; 11 \le n \Rightarrow \left(\operatorname{Odd}\left(n\right) \Rightarrow \left\lfloor\frac{n + 3}{2}\right\rfloor \le \operatorname{f}\left(n\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ErdosUlam/SublatticeChainBound.odd_lower_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If every monochromatic sublattice had at most half the number of ranks, equal-size subsets would have equal colour and both rank colours would be balanced. A consecutive arithmetic progression adds a diamond member. Otherwise a balanced twelve-rank interval admits a seven-member sublattice; embedding it and adjoining the same-colour prefixes outside the interval again adds one member.

**Theorem 1.8 (The formula is false).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ErdosUlam/SublatticeChainBound.result` (`✓ std3`). ∎

*Resolves.* `Problems/bhattacharjee-mandal-bhattacharya-2026-sublattice-chain-bound-refutation` (refuted) by `D5/S3/Combinatorics/ErdosUlam/SublatticeChainBound.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"bhattacharjee-mandal-bhattacharya-2026-sublattice-chain-bound-refutation","declaration_gid":"D5/S3/Combinatorics/ErdosUlam/SublatticeChainBound.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Commentary.*

At dimension eleven the lower bound is seven, whereas the proposed formula gives six. The separate linear-growth question remains open.

## References

- Truth anchor: `D5/S3/Combinatorics/ErdosUlam/SublatticeChainBound.BalancedWindow`
- Truth anchor: `D5/S3/Combinatorics/ErdosUlam/SublatticeChainBound.ConsecutiveAP`
- Truth anchor: `D5/S3/Combinatorics/ErdosUlam/SublatticeChainBound.balanced_rank_base`
- Truth anchor: `D5/S3/Combinatorics/ErdosUlam/SublatticeChainBound.claim`
- Truth anchor: `D5/S3/Combinatorics/ErdosUlam/SublatticeChainBound.f`
- Truth anchor: `D5/S3/Combinatorics/ErdosUlam/SublatticeChainBound.odd_lower_bound`
- Truth anchor: `D5/S3/Combinatorics/ErdosUlam/SublatticeChainBound.rank_word_lemma`
- Truth anchor: `D5/S3/Combinatorics/ErdosUlam/SublatticeChainBound.result`
- Dependency: [D5/S3/Combinatorics/ErdosUlam/SublatticeConstructions](SublatticeConstructions.md)
- Dependency: [D5/S3/Combinatorics/ErdosUlam/SublatticeRankRigidity](SublatticeRankRigidity.md)
