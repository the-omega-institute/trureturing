# Transfer powers

## Abstract

The finite transfer-power table.

**Definition 1.1 (Power table).**

$$\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233259PairTransferPowers}.\operatorname{W}\left(\right) = (![![2, 2, 2, 2, 0, 2, 2, 0, 2, 2, 0, 0, 0, 0], ![1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0], ![1, 1, 1, 1, 0, 0, 0, 0, 0, 1, 1, 0, 1, 1], ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1], ![1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0], ![0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 1]]: \operatorname{Fin}\left(9\right) \to \left(\operatorname{Fin}\left(14\right) \to \operatorname{Int}\right))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233259PairTransferPowers.W` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233259: complementary-pair exclusion on a four-row strip*. URL: <https://oeis.org/A233259>.

*Commentary.*

Power table.

**Definition 1.2 (Recurrence coefficients).**

$$\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233259PairTransferPowers}.\operatorname{coefficients}\left(\right) = (![\neg 6, 21, \neg 24, 10]: \operatorname{Fin}\left(4\right) \to \operatorname{Int})$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233259PairTransferPowers.coefficients` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233259: complementary-pair exclusion on a four-row strip*. URL: <https://oeis.org/A233259>.

*Commentary.*

Recurrence coefficients.

**Theorem 1.3 (Power table base).**

$$\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233259PairTransferPowers}.\operatorname{W}\left(\right)\left(0\right) = (![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]: \operatorname{Fin}\left(14\right) \to \operatorname{Int})$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233259PairTransferPowers.table_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233259: complementary-pair exclusion on a four-row strip*. URL: <https://oeis.org/A233259>.

*Commentary.*

Power table base.

**Theorem 1.4 (Power table steps).**

$$\forall k \in \operatorname{Fin}\left(8\right),\; \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233259PairTransferPowers}.\operatorname{W}\left(\right)\left(\operatorname{Fin}.\operatorname{succ}\left(k\right)\right) = \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233259PairTransferCore}.\operatorname{Q}.\operatorname{mulVec}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233259PairTransferPowers}.\operatorname{W}\left(\right)\left(\operatorname{Fin}.\operatorname{castSucc}\left(k\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233259PairTransferPowers.table_steps` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233259: complementary-pair exclusion on a four-row strip*. URL: <https://oeis.org/A233259>.

*Commentary.*

Power table steps.

**Theorem 1.5 (Power table).**

$$\forall k \in \operatorname{Fin}\left(9\right),\; \operatorname{Matrix}.\operatorname{mulVec}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233259PairTransferPowers}.\operatorname{Q}\left(\right)^{\operatorname{Fin}.\operatorname{val}\left(k\right)}, (![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]: \operatorname{Fin}\left(14\right) \to \operatorname{Int})\right) = \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233259PairTransferPowers}.\operatorname{W}\left(\right)\left(k\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233259PairTransferPowers.powers_table` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233259: complementary-pair exclusion on a four-row strip*. URL: <https://oeis.org/A233259>.

*Commentary.*

Power table.

**Theorem 1.6 (Power polynomial).**

$$\operatorname{Matrix}.\operatorname{mulVec}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233259PairTransferPowers}.\operatorname{Q}\left(\right)^{(4) + (4)}, (![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]: \operatorname{Fin}\left(14\right) \to \operatorname{Int})\right) = \sum_{j \in \operatorname{Fin}\left(4\right)} ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233259PairTransferPowers}.\operatorname{coefficients}\left(\right)\left(j\right)) \cdot (\operatorname{Matrix}.\operatorname{mulVec}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233259PairTransferPowers}.\operatorname{Q}\left(\right)^{(4) + (\operatorname{Fin}.\operatorname{val}\left(j\right))}, (![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]: \operatorname{Fin}\left(14\right) \to \operatorname{Int})\right)))$$

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
