# Transfer powers

## Abstract

The finite transfer-power table.

**Definition 1.1 (Power table).**

$$\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233259PairTransferPowers}.\operatorname{W} = (![![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], ![16, 8, 4, 8, 4, 4, 2, 2, 4, 8, 4, 2, 2, 4], ![108, 54, 36, 54, 18, 36, 24, 12, 30, 54, 24, 6, 12, 18], ![792, 360, 246, 360, 96, 252, 162, 72, 210, 396, 150, 24, 84, 108], ![5556, 2478, 1758, 2496, 588, 1758, 1152, 456, 1476, 2778, 1002, 132, 606, 738], ![38904, 17112, 12288, 17412, 3954, 12288, 8034, 3084, 10248, 19452, 6864, 870, 4254, 5124], ![271476, 119070, 85716, 121410, 27360, 85716, 56016, 21366, 71388, 135738, 47682, 5994, 29700, 35694], ![1893060, 829818, 597672, 846486, 190458, 597672, 390546, 148770, 497628, 946530, 332190, 41688, 207126, 248814], ![13198824, 5784984, 4167036, 5901696, 1327446, 4167036, 2722878, 1036944, 3469320, 6599412, 2315664, 290502, 1444158, 1734660]]: \operatorname{Fin}\left(9\right) \to \left(\operatorname{Fin}\left(14\right) \to \operatorname{Int}\right))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233259PairTransferPowers.W` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233259: complementary-pair exclusion on a four-row strip*. URL: <https://oeis.org/A233259>.

*Commentary.*

Power table.

**Definition 1.2 (Recurrence coefficients).**

$$\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233259PairTransferPowers}.\operatorname{coefficients} = (![-6, 21, -24, 10]: \operatorname{Fin}\left(4\right) \to \operatorname{Int})$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233259PairTransferPowers.coefficients` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233259: complementary-pair exclusion on a four-row strip*. URL: <https://oeis.org/A233259>.

*Commentary.*

Recurrence coefficients.

**Theorem 1.3 (Power table base).**

$$\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233259PairTransferPowers}.\operatorname{W}\left(0\right) = (![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]: \operatorname{Fin}\left(14\right) \to \operatorname{Int})$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233259PairTransferPowers.table_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233259: complementary-pair exclusion on a four-row strip*. URL: <https://oeis.org/A233259>.

*Commentary.*

Power table base.

**Theorem 1.4 (Power table steps).**

$$\forall k \in \operatorname{Fin}\left(8\right),\; \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233259PairTransferPowers}.\operatorname{W}\left(\operatorname{Fin}.\operatorname{succ}\left(k\right)\right) = \operatorname{Matrix}.\operatorname{mulVec}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233259PairTransferCore}.\operatorname{Q}, \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233259PairTransferPowers}.\operatorname{W}\left(\operatorname{Fin}.\operatorname{castSucc}\left(k\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233259PairTransferPowers.table_steps` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233259: complementary-pair exclusion on a four-row strip*. URL: <https://oeis.org/A233259>.

*Commentary.*

Power table steps.

**Theorem 1.5 (Power table).**

$$\forall k \in \operatorname{Fin}\left(9\right),\; \operatorname{Matrix}.\operatorname{mulVec}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233259PairTransferCore}.\operatorname{Q}^{\operatorname{Fin}.\operatorname{val}\left(k\right)}, (![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]: \operatorname{Fin}\left(14\right) \to \operatorname{Int})\right) = \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233259PairTransferPowers}.\operatorname{W}\left(k\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233259PairTransferPowers.powers_table` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233259: complementary-pair exclusion on a four-row strip*. URL: <https://oeis.org/A233259>.

*Commentary.*

Power table.

**Theorem 1.6 (Power polynomial).**

$$\operatorname{Matrix}.\operatorname{mulVec}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233259PairTransferCore}.\operatorname{Q}^{(4) + (4)}, (![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]: \operatorname{Fin}\left(14\right) \to \operatorname{Int})\right) = \sum_{j \in \operatorname{Fin}\left(4\right)} (\operatorname{HSMul}.\operatorname{hSMul}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233259PairTransferPowers}.\operatorname{coefficients}\left(j\right), \operatorname{Matrix}.\operatorname{mulVec}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233259PairTransferCore}.\operatorname{Q}^{(4) + (\operatorname{Fin}.\operatorname{val}\left(j\right))}, (![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]: \operatorname{Fin}\left(14\right) \to \operatorname{Int})\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233259PairTransferPowers.power_polynomial` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233259: complementary-pair exclusion on a four-row strip*. URL: <https://oeis.org/A233259>.

*Commentary.*

Power polynomial.

## References

- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233259PairTransferPowers.W`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233259PairTransferPowers.coefficients`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233259PairTransferPowers.power_polynomial`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233259PairTransferPowers.powers_table`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233259PairTransferPowers.table_steps`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233259PairTransferPowers.table_zero`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233259PairTransferCore](HardinA233259PairTransferCore.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/TransferMatrix](TransferMatrix.md)
