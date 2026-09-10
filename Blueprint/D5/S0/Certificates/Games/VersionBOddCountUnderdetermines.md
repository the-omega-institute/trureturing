# Odd-pile count does not determine losing status

## Abstract

Two in-scope twelve-pile positions have six odd piles and opposite normal-play Version B outcomes.

**Definition 1.1 (Seven pile sizes).**

Lean statement: `D5/S0/Certificates/Games/VersionBOddCountUnderdetermines.Position`

*Formalization.* `D5/S0/Certificates/Games/VersionBOddCountUnderdetermines.Position` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A position records the multiplicities of sizes one through seven. There is no bound on the number of piles.

**Definition 1.2 (Pile count).**

Lean statement: `D5/S0/Certificates/Games/VersionBOddCountUnderdetermines.pileCount`

*Formalization.* `D5/S0/Certificates/Games/VersionBOddCountUnderdetermines.pileCount` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The sum of the seven multiplicities is the number of nonempty piles.

**Definition 1.3 (Token count).**

Lean statement: `D5/S0/Certificates/Games/VersionBOddCountUnderdetermines.tokens`

*Formalization.* `D5/S0/Certificates/Games/VersionBOddCountUnderdetermines.tokens` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each multiplicity is weighted by its pile size. The resulting total is the termination measure for Losing.

**Definition 1.4 (Single-pile successors).**

Lean statement: `D5/S0/Certificates/Games/VersionBOddCountUnderdetermines.singleSuccessors`

*Formalization.* `D5/S0/Certificates/Games/VersionBOddCountUnderdetermines.singleSuccessors` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For each present size, one pile loses one token. A size-one pile disappears; any larger pile becomes one size smaller.

**Definition 1.5 (Simultaneous successor).**

Lean statement: `D5/S0/Certificates/Games/VersionBOddCountUnderdetermines.allSuccessor`

*Formalization.* `D5/S0/Certificates/Games/VersionBOddCountUnderdetermines.allSuccessor` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

All piles lose one token. Size-one piles disappear and the size-seven multiplicity of the successor is zero.

**Definition 1.6 (Single-pile move).**

Lean statement: `D5/S0/Certificates/Games/VersionBOddCountUnderdetermines.SingleMove`

*Formalization.* `D5/S0/Certificates/Games/VersionBOddCountUnderdetermines.SingleMove` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A single-pile move means membership in singleSuccessors.

**Definition 1.7 (All-pile move).**

Lean statement: `D5/S0/Certificates/Games/VersionBOddCountUnderdetermines.AllMove`

*Formalization.* `D5/S0/Certificates/Games/VersionBOddCountUnderdetermines.AllMove` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The simultaneous move requires a nonzero pile count and reaches allSuccessor.

**Definition 1.8 (Legal move).**

Lean statement: `D5/S0/Certificates/Games/VersionBOddCountUnderdetermines.Move`

*Formalization.* `D5/S0/Certificates/Games/VersionBOddCountUnderdetermines.Move` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A legal move is either SingleMove or AllMove.

**Definition 1.9 (Normal-play losing status).**

Lean statement: `D5/S0/Certificates/Games/VersionBOddCountUnderdetermines.Losing`

*Formalization.* `D5/S0/Certificates/Games/VersionBOddCountUnderdetermines.Losing` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Losing is defined by recursion on token count: every legal successor is not losing. This includes the empty position as a loss.

**Definition 1.10 (Odd-pile count).**

Lean statement: `D5/S0/Certificates/Games/VersionBOddCountUnderdetermines.oddPiles`

*Formalization.* `D5/S0/Certificates/Games/VersionBOddCountUnderdetermines.oddPiles` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The multiplicities of sizes one, three, five and seven sum to the number of odd piles.

**Definition 1.11 (Strict threshold).**

Lean statement: `D5/S0/Certificates/Games/VersionBOddCountUnderdetermines.EveryPileExceedsThreshold`

*Formalization.* `D5/S0/Certificates/Games/VersionBOddCountUnderdetermines.EveryPileExceedsThreshold` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every present pile strictly exceeds the integer ceiling of one third of the pile count. Absent sizes impose no condition.

**Definition 1.12 (The claim under refutation).**

$$\mathit{OddCountDetermines} \Leftrightarrow \forall s t:\mathit{Position}, 3\le \operatorname{pileCount}\left(s\right) \Rightarrow 3\le \operatorname{pileCount}\left(t\right) \Rightarrow \operatorname{EveryPileExceedsThreshold}\left(s\right) \Rightarrow \operatorname{EveryPileExceedsThreshold}\left(t\right) \Rightarrow \operatorname{pileCount}\left(s\right)= \operatorname{pileCount}\left(t\right) \Rightarrow \operatorname{oddPiles}\left(s\right)= \operatorname{oddPiles}\left(t\right) \Rightarrow (\operatorname{Losing}\left(s\right) \Leftrightarrow \operatorname{Losing}\left(t\right))$$

*Formalization.* `D5/S0/Certificates/Games/VersionBOddCountUnderdetermines.OddCountDetermines` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The closed proposition quantifies over all pairs in the seven-size game. Each position has at least three piles and satisfies the strict threshold. Equal pile counts and equal odd-pile counts are asserted to imply equivalent losing status.

**Definition 1.13 (Six fives and six sixes).**

Lean statement: `D5/S0/Certificates/Games/VersionBOddCountUnderdetermines.sixFives_sixSixes`

*Formalization.* `D5/S0/Certificates/Games/VersionBOddCountUnderdetermines.sixFives_sixSixes` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Write s56 for sixFives_sixSixes. This position has six piles of size five, six of size six, and no other piles.

**Definition 1.14 (Six sixes and six sevens).**

Lean statement: `D5/S0/Certificates/Games/VersionBOddCountUnderdetermines.sixSixes_sixSevens`

*Formalization.* `D5/S0/Certificates/Games/VersionBOddCountUnderdetermines.sixSixes_sixSevens` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Write s67 for sixSixes_sixSevens. This position has six piles of size six, six of size seven, and no other piles.

**Theorem 1.15 (The losing witness).**

$$\operatorname{pileCount}\left(\mathit{s56}\right)= 12\land 3\le \operatorname{pileCount}\left(\mathit{s56}\right)\land \operatorname{EveryPileExceedsThreshold}\left(\mathit{s56}\right)\land \operatorname{oddPiles}\left(\mathit{s56}\right)= 6\land \operatorname{Losing}\left(\mathit{s56}\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/Games/VersionBOddCountUnderdetermines.sixFives_sixSixes_witness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Six fives and six sixes satisfy the scope hypotheses, have twelve piles and six odd piles, and are losing. The wider game has its own kernel-checked certificate recurrence on the closed domain of at most twelve piles with no sevens; induction on token count identifies that certificate with Losing.

**Theorem 1.16 (The winning all-move).**

$$\operatorname{AllMove}\left(\mathit{s67}, \mathit{s56}\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/Games/VersionBOddCountUnderdetermines.sixSixes_sixSevens_all_move` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Removing one token from every pile of six sixes and six sevens reaches six fives and six sixes. The starting position is nonempty, so this all-move is legal.

**Theorem 1.17 (The non-losing witness).**

$$\operatorname{pileCount}\left(\mathit{s67}\right)= 12\land 3\le \operatorname{pileCount}\left(\mathit{s67}\right)\land \operatorname{EveryPileExceedsThreshold}\left(\mathit{s67}\right)\land \operatorname{oddPiles}\left(\mathit{s67}\right)= 6\land \neg \operatorname{Losing}\left(\mathit{s67}\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/Games/VersionBOddCountUnderdetermines.sixSixes_sixSevens_witness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Six sixes and six sevens satisfy the same scope hypotheses and have the same two counts. Their legal all-move reaches the losing witness, so this position is not losing.

**Theorem 1.18 (Odd-pile count underdetermines the outcome).**

$$\neg \mathit{OddCountDetermines}$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/Games/VersionBOddCountUnderdetermines.odd_count_does_not_determine` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Applying OddCountDetermines to the two witnesses would make their losing statuses equivalent. The losing first witness and non-losing second witness contradict that equivalence.

## References

- Truth anchor: `D5/S0/Certificates/Games/VersionBOddCountUnderdetermines.AllMove`
- Truth anchor: `D5/S0/Certificates/Games/VersionBOddCountUnderdetermines.EveryPileExceedsThreshold`
- Truth anchor: `D5/S0/Certificates/Games/VersionBOddCountUnderdetermines.Losing`
- Truth anchor: `D5/S0/Certificates/Games/VersionBOddCountUnderdetermines.Move`
- Truth anchor: `D5/S0/Certificates/Games/VersionBOddCountUnderdetermines.OddCountDetermines`
- Truth anchor: `D5/S0/Certificates/Games/VersionBOddCountUnderdetermines.Position`
- Truth anchor: `D5/S0/Certificates/Games/VersionBOddCountUnderdetermines.SingleMove`
- Truth anchor: `D5/S0/Certificates/Games/VersionBOddCountUnderdetermines.allSuccessor`
- Truth anchor: `D5/S0/Certificates/Games/VersionBOddCountUnderdetermines.oddPiles`
- Truth anchor: `D5/S0/Certificates/Games/VersionBOddCountUnderdetermines.odd_count_does_not_determine`
- Truth anchor: `D5/S0/Certificates/Games/VersionBOddCountUnderdetermines.pileCount`
- Truth anchor: `D5/S0/Certificates/Games/VersionBOddCountUnderdetermines.singleSuccessors`
- Truth anchor: `D5/S0/Certificates/Games/VersionBOddCountUnderdetermines.sixFives_sixSixes`
- Truth anchor: `D5/S0/Certificates/Games/VersionBOddCountUnderdetermines.sixFives_sixSixes_witness`
- Truth anchor: `D5/S0/Certificates/Games/VersionBOddCountUnderdetermines.sixSixes_sixSevens`
- Truth anchor: `D5/S0/Certificates/Games/VersionBOddCountUnderdetermines.sixSixes_sixSevens_all_move`
- Truth anchor: `D5/S0/Certificates/Games/VersionBOddCountUnderdetermines.sixSixes_sixSevens_witness`
- Truth anchor: `D5/S0/Certificates/Games/VersionBOddCountUnderdetermines.tokens`
