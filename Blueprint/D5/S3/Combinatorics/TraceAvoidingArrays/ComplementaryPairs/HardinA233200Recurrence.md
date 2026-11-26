# The recurrence at every height from 24

## Abstract

Hardin's signed recurrence for the literal eight-colour width-six array count.

**Definition 1.1 (Signed lag coefficients).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/ComplementaryPairs/HardinA233200Recurrence.lagCoefficient`

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/ComplementaryPairs/HardinA233200Recurrence.lagCoefficient` (`✓ std3`).

*Citation.* R. H. Hardin and OEIS Foundation Inc. (2013). *OEIS A233200: complementary exclusion on a width-six eight-colour strip*. URL: <https://oeis.org/A233200>.

*Commentary.*

In the following tuple, entry zero multiplies the height-one lag, and entry twenty-one multiplies the height-twenty-two lag.

2624, -2916352, 2023751680, -1022873305088, 396210733056000, -117075448369774592, 24978582014512857088, -3235719238675389743104, 32228191279027496943616, 79127659192314522138312704, -14330945495506960134011092992, 573127552562903399144703918080, 175763191005253023447780744495104, -41436012082310191504073111849926656, 7185129802334419767282615543889133568, -1237277610717122610430160500786185895936, 170446905899499762382455179339748584980480, -17499361001276181422067502561786112042336256, 1430383734999503249937564429831586312219525120, -95447189449711067045772874206934987245596180480, 4407340875076004112707987073660040981149921574912, -93536104789177786765035829293842113257979682750464.

**Theorem 1.2 (Exact width-six recurrence).**

$$\forall n: \operatorname{PNat}, 24 \le \operatorname{val}\left(n\right) \implies (\operatorname{a}\left(n\right): \operatorname{Int}) = \sum_{j: \operatorname{Fin}\left(22\right)} \operatorname{lagCoefficient}\left(j\right) \cdot (\operatorname{a}\left(\operatorname{val}\left(n\right) - \left(\operatorname{val}\left(j\right) + 1\right)\right): \operatorname{Int})$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/ComplementaryPairs/HardinA233200Recurrence.result` (`✓ std3`). ∎

*Resolves.* `Problems/hardin233200` (proved) by `D5/S3/Combinatorics/TraceAvoidingArrays/ComplementaryPairs/HardinA233200Recurrence.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"hardin233200","declaration_gid":"D5/S3/Combinatorics/TraceAvoidingArrays/ComplementaryPairs/HardinA233200Recurrence.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin and OEIS Foundation Inc. (2013). *OEIS A233200: complementary exclusion on a width-six eight-colour strip*. URL: <https://oeis.org/A233200>.

*Commentary.*

Here a is the literal cardinality from HardinA233200PairTransfer. The count uses the zero upper-left entry, the three contained bond directions, the exclusion of equal or complementary endpoints and all strict row-major first-use constraints.

For each of the 58 source states the proof accumulates exact next-row weights by destination and checks the resulting row against the transition table. It verifies the constant-one vector and every next continuation vector through power 23.

The power-23 vector equals the signed sum of powers 22 down to 1 in lag order. TransferMatrix.scalarRelationShift propagates the relation to every later power. The all-height counting bridge applies the anchored initial vector and shifts from additional rows to total height. At height 24 the lagged counts run from height 23 down to 2.

## References

- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/ComplementaryPairs/HardinA233200Recurrence.lagCoefficient`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/ComplementaryPairs/HardinA233200Recurrence.result`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/ComplementaryPairs/HardinA233200PairTransfer](HardinA233200PairTransfer.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/TransferMatrix](../TransferMatrix.md)
