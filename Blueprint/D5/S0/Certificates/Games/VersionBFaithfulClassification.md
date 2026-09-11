# Version B faithful classification refuted

## Abstract

The threshold classification with three parity cases fails in both directions at twelve piles in normal-play Version B.

**Definition 1.1 (Odd piles).**

Lean statement: `D5/S0/Certificates/Games/VersionBFaithfulClassification.oddPiles`

*Formalization.* `D5/S0/Certificates/Games/VersionBFaithfulClassification.oddPiles` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The multiplicities of sizes one, three and five sum to the number of odd piles in the imported closed subgame with sizes one through six.

**Definition 1.2 (Allowed odd counts).**

Lean statement: `D5/S0/Certificates/Games/VersionBFaithfulClassification.allowedOddCount`

*Formalization.* `D5/S0/Certificates/Games/VersionBFaithfulClassification.allowedOddCount` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The count is at most the pile count. For odd pile count, even counts are allowed. For pile count divisible by four, the lower even range ends two below half the pile count and the upper odd range starts one above half. For pile count congruent to two modulo four, these endpoints are one below half and two above half. Each upper range ends strictly below the pile count.

The lower bounds use addition on the count, preserving empty ranges without truncated subtraction.

**Definition 1.3 (Strict threshold).**

Lean statement: `D5/S0/Certificates/Games/VersionBFaithfulClassification.EveryPileExceedsThreshold`

*Formalization.* `D5/S0/Certificates/Games/VersionBFaithfulClassification.EveryPileExceedsThreshold` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every present pile strictly exceeds the integer ceiling of one third of the pile count. Absent sizes impose no condition.

**Definition 1.4 (Classification).**

$$\mathit{FaithfulClassification} \Leftrightarrow \forall s:\mathit{Position}, 3\le \operatorname{pileCount}\left(s\right) \Rightarrow \operatorname{EveryPileExceedsThreshold}\left(s\right) \Rightarrow (\operatorname{Losing}\left(s\right) \Leftrightarrow \operatorname{allowedOddCount}\left(\operatorname{pileCount}\left(s\right), \operatorname{oddPiles}\left(s\right)\right))$$

*Formalization.* `D5/S0/Certificates/Games/VersionBFaithfulClassification.FaithfulClassification` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The closed proposition quantifies over all positions in the imported closed subgame, with no pile-count bound. Both the lower bound of three piles and the strict threshold precede the biconditional.

**Theorem 1.5 (Exactly six allowed counts at twelve piles).**

$$\forall n\in \mathbb{N}, \operatorname{allowedOddCount}\left(12, n\right) \Leftrightarrow n= 0\lor n= 2\lor n= 4\lor n= 7\lor n= 9\lor n= 11$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/Games/VersionBFaithfulClassification.allowedOddCount_twelve_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The general predicate specializes exactly to zero, two, four, seven, nine and eleven.

**Definition 1.6 (Seven fives and five sixes).**

Lean statement: `D5/S0/Certificates/Games/VersionBFaithfulClassification.sevenFives_fiveSixes`

*Formalization.* `D5/S0/Certificates/Games/VersionBFaithfulClassification.sevenFives_fiveSixes` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Write $\mathit{s7}$ for this position: seven piles of size five and five of size six.

**Definition 1.7 (Seven fours and five fives).**

Lean statement: `D5/S0/Certificates/Games/VersionBFaithfulClassification.sevenFours_fiveFives`

*Formalization.* `D5/S0/Certificates/Games/VersionBFaithfulClassification.sevenFours_fiveFives` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Write $\mathit{s4}$ for this position: seven piles of size four and five of size five.

**Theorem 1.8 (The successor is losing).**

$$\operatorname{Losing}\left(\mathit{s4}\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/Games/VersionBFaithfulClassification.sevenFours_fiveFives_losing` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The imported certificate equivalence and a kernel-checked certificate bit establish that the player to move loses.

**Theorem 1.9 (The winning all-move).**

$$\operatorname{AllMove}\left(\mathit{s7}, \mathit{s4}\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/Games/VersionBFaithfulClassification.sevenFives_fiveSixes_all_move` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The starting position is nonempty and simultaneous removal reaches the certified losing successor, so this all-move is legal.

**Theorem 1.10 (Necessity fails).**

$$\operatorname{pileCount}\left(\mathit{target}\right)= 12\land 3\le \operatorname{pileCount}\left(\mathit{target}\right)\land \operatorname{EveryPileExceedsThreshold}\left(\mathit{target}\right)\land \operatorname{oddPiles}\left(\mathit{target}\right)= 6\land \operatorname{Losing}\left(\mathit{target}\right)\land \neg \operatorname{allowedOddCount}\left(\operatorname{pileCount}\left(\mathit{target}\right), \operatorname{oddPiles}\left(\mathit{target}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/Games/VersionBFaithfulClassification.sixFives_sixSixes_is_losing_but_predicted_winning` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The imported target consists of six fives and six sixes. It satisfies both classification hypotheses and is losing, but its six odd piles are excluded by the prediction.

**Theorem 1.11 (Sufficiency fails).**

$$\operatorname{pileCount}\left(\mathit{s7}\right)= 12\land 3\le \operatorname{pileCount}\left(\mathit{s7}\right)\land \operatorname{EveryPileExceedsThreshold}\left(\mathit{s7}\right)\land \operatorname{oddPiles}\left(\mathit{s7}\right)= 7\land \neg \operatorname{Losing}\left(\mathit{s7}\right)\land \operatorname{allowedOddCount}\left(\operatorname{pileCount}\left(\mathit{s7}\right), \operatorname{oddPiles}\left(\mathit{s7}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/Games/VersionBFaithfulClassification.sevenFives_fiveSixes_is_winning_but_predicted_losing` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Seven fives and five sixes satisfy both classification hypotheses and the allowed-count prediction. A legal all-move to a losing position proves that this starting position is not losing.

**Theorem 1.12 (Classification refuted).**

$$\neg \mathit{FaithfulClassification}$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/Games/VersionBFaithfulClassification.faithful_classification_refuted` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Applying the asserted biconditional to seven fives and five sixes would make that position losing, contradicting its certified winning move.

## References

- Truth anchor: `D5/S0/Certificates/Games/VersionBFaithfulClassification.EveryPileExceedsThreshold`
- Truth anchor: `D5/S0/Certificates/Games/VersionBFaithfulClassification.FaithfulClassification`
- Truth anchor: `D5/S0/Certificates/Games/VersionBFaithfulClassification.allowedOddCount`
- Truth anchor: `D5/S0/Certificates/Games/VersionBFaithfulClassification.allowedOddCount_twelve_iff`
- Truth anchor: `D5/S0/Certificates/Games/VersionBFaithfulClassification.faithful_classification_refuted`
- Truth anchor: `D5/S0/Certificates/Games/VersionBFaithfulClassification.oddPiles`
- Truth anchor: `D5/S0/Certificates/Games/VersionBFaithfulClassification.sevenFives_fiveSixes`
- Truth anchor: `D5/S0/Certificates/Games/VersionBFaithfulClassification.sevenFives_fiveSixes_all_move`
- Truth anchor: `D5/S0/Certificates/Games/VersionBFaithfulClassification.sevenFives_fiveSixes_is_winning_but_predicted_losing`
- Truth anchor: `D5/S0/Certificates/Games/VersionBFaithfulClassification.sevenFours_fiveFives`
- Truth anchor: `D5/S0/Certificates/Games/VersionBFaithfulClassification.sevenFours_fiveFives_losing`
- Truth anchor: `D5/S0/Certificates/Games/VersionBFaithfulClassification.sixFives_sixSixes_is_losing_but_predicted_winning`
- Dependency: [D5/S0/Certificates/Games/VersionBTwelvePileRefutation](VersionBTwelvePileRefutation.md)
