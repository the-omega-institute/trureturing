# Exact defective strip colourings

## Abstract

Exact bond-defect transfer and integer recurrence.

Exactly 2 monochromatic bonds are allowed. These are unsatisfied bonds of the three-state Potts antiferromagnet; the theorem concerns finite combinatorial counts.

**Definition 1.1 (Residual budgets).**

$$\forall p: \operatorname{\mathit{HardinA229583StripData}}.\operatorname{\mathit{Boundary}}, (\forall d: \mathit{Nat}, ((\operatorname{\mathit{HardinA229691StripData}}.\operatorname{\mathit{Valid}}\left(p, d\right)) \iff ((d \le 2) \land (\operatorname{\mathit{Finset}}.\operatorname{\mathit{card}}\left(\operatorname{\mathit{Finset}}.\operatorname{\mathit{filter}}\left(\lambda j: \operatorname{\mathit{Fin}}\left(3\right) \mapsto (p\left(\operatorname{\mathit{Fin}}.\operatorname{\mathit{castSucc}}\left(j\right)\right) = p\left(\operatorname{\mathit{Fin}}.\operatorname{\mathit{succ}}\left(j\right)\right)), \operatorname{\mathit{Finset}}.\operatorname{\mathit{univ}}\right)\right) \le 2 - d))))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229691StripData.Valid` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229691: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229691>.

*Commentary.*

The remaining budget is at most the registered exact budget.

**Definition 1.2 (Equality and budget classes).**

$$\forall p: \operatorname{\mathit{HardinA229583StripData}}.\operatorname{\mathit{Boundary}}, (\forall d: \mathit{Nat}, (\operatorname{\mathit{HardinA229691StripData}}.\operatorname{\mathit{cl}}\left(p, d\right) = (\operatorname{\mathit{if}} (d = 0) \operatorname{\mathit{then}} ![26, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]\left(\operatorname{\mathit{HardinA233177PairTransfer}}.\operatorname{\mathit{cls}}\left((p\left(0\right), p\left(1\right), p\left(2\right), p\left(3\right))\right)\right) \operatorname{\mathit{else}} (\operatorname{\mathit{if}} (d = 1) \operatorname{\mathit{then}} ![26, 26, 4, 26, 5, 6, 7, 8, 9, 26, 10, 11, 12, 13]\left(\operatorname{\mathit{HardinA233177PairTransfer}}.\operatorname{\mathit{cls}}\left((p\left(0\right), p\left(1\right), p\left(2\right), p\left(3\right))\right)\right) \operatorname{\mathit{else}} (\operatorname{\mathit{if}} (d = 2) \operatorname{\mathit{then}} ![26, 26, 26, 26, 26, 26, 0, 1, 26, 26, 26, 2, 3, 26]\left(\operatorname{\mathit{HardinA233177PairTransfer}}.\operatorname{\mathit{cls}}\left((p\left(0\right), p\left(1\right), p\left(2\right), p\left(3\right))\right)\right) \operatorname{\mathit{else}} 26)))))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229691StripData.cl` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229691: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229691>.

*Commentary.*

Global colour permutations preserve the equality pattern of the retained column.

**Definition 1.3 (T).**

$$\operatorname{\mathit{HardinA229691StripData}}.\operatorname{T} = ![![5, 5, 3, 3, 1, 1, 5, 3, 3, 2, 2, 5, 5, 3, 2, 7, 1, 7, 3, 5, 5, 5, 2, 5, 5, 5, 5], ![4, 4, 3, 3, 2, 2, 4, 2, 2, 3, 3, 6, 6, 3, 0, 7, 2, 7, 2, 8, 8, 5, 3, 5, 5, 5, 6], ![2, 2, 3, 3, 4, 4, 2, 7, 7, 3, 3, 6, 6, 3, 0, 2, 4, 2, 7, 5, 5, 5, 3, 5, 5, 5, 6], ![4, 4, 3, 3, 2, 2, 4, 6, 6, 1, 1, 4, 4, 3, 4, 5, 2, 5, 6, 2, 2, 8, 1, 8, 8, 8, 4], ![0, 0, 0, 0, 0, 0, 0, 3, 3, 0, 0, 2, 2, 0, 0, 1, 0, 1, 3, 7, 7, 1, 0, 1, 7, 7, 2], ![0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 2, 2, 0, 0, 2, 0, 2, 2, 7, 7, 2, 0, 2, 8, 8, 2], ![0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 4, 4, 0, 0, 1, 0, 1, 1, 8, 8, 5, 0, 5, 2, 2, 4], ![0, 0, 0, 0, 0, 0, 0, 5, 5, 0, 0, 3, 3, 0, 0, 1, 0, 1, 5, 3, 3, 2, 0, 2, 5, 5, 3], ![0, 0, 0, 0, 0, 0, 0, 4, 4, 0, 0, 3, 3, 0, 0, 2, 0, 2, 4, 2, 2, 3, 0, 3, 6, 6, 3], ![0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 3, 3, 0, 0, 5, 0, 5, 1, 7, 7, 2, 0, 2, 5, 5, 3], ![0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 3, 3, 0, 0, 4, 0, 4, 2, 5, 5, 1, 0, 1, 4, 4, 3], ![0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 3, 3, 0, 0, 4, 0, 4, 2, 7, 7, 3, 0, 3, 6, 6, 3], ![0, 0, 0, 0, 0, 0, 0, 4, 4, 0, 0, 3, 3, 0, 0, 2, 0, 2, 4, 6, 6, 1, 0, 1, 4, 4, 3], ![0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 2, 2, 0, 0, 2, 0, 2, 2, 5, 5, 4, 0, 4, 8, 8, 2], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 2, 2, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 3, 0, 0, 0, 2, 2, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 2, 2, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 0, 2, 2, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 4, 4, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 5, 0, 0, 0, 3, 3, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 4, 0, 0, 0, 3, 3, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 3, 3, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 3, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 0, 3, 3, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 0, 3, 3, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 4, 0, 0, 0, 3, 3, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 0, 2, 2, 0]]$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229691StripData.T` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229691: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229691>.

*Commentary.*

The leading 14-state block and the ten-state zero-budget submatrix call HardinA229583StripData.T. In the lower sector, shared positions are 1,3,4,5,6,7,9,10,11,12; added positions are 0,2,8. Matrix.fromBlocks and submatrix restore this order. Only added-state interactions remain literal. The other tables give initial weights, terminal acceptance and successive forward weights.

**Definition 1.4 (initial).**

$$\operatorname{\mathit{HardinA229691StripData}}.\operatorname{\mathit{initial}} = ![12, 12, 12, 12, 12, 12, 12, 6, 6, 12, 12, 6, 6, 12, 12, 6, 12, 6, 6, 0, 0, 6, 12, 6, 0, 0, 6]$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229691StripData.initial` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229691: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229691>.

*Commentary.*

The leading 14-state block and the ten-state zero-budget submatrix call HardinA229583StripData.T. In the lower sector, shared positions are 1,3,4,5,6,7,9,10,11,12; added positions are 0,2,8. Matrix.fromBlocks and submatrix restore this order. Only added-state interactions remain literal. The other tables give initial weights, terminal acceptance and successive forward weights.

**Definition 1.5 (terminal).**

$$\operatorname{\mathit{HardinA229691StripData}}.\operatorname{\mathit{terminal}} = ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229691StripData.terminal` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229691: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229691>.

*Commentary.*

The leading 14-state block and the ten-state zero-budget submatrix call HardinA229583StripData.T. In the lower sector, shared positions are 1,3,4,5,6,7,9,10,11,12; added positions are 0,2,8. Matrix.fromBlocks and submatrix restore this order. Only added-state interactions remain literal. The other tables give initial weights, terminal acceptance and successive forward weights.

**Definition 1.6 (W).**

$$\operatorname{\mathit{HardinA229691StripData}}.\operatorname{W} = ![![12, 12, 12, 12, 12, 12, 12, 6, 6, 12, 12, 6, 6, 12, 12, 6, 12, 6, 6, 0, 0, 6, 12, 6, 0, 0, 6], ![180, 180, 144, 144, 108, 108, 180, 438, 438, 108, 108, 516, 516, 144, 72, 486, 108, 486, 438, 942, 942, 510, 108, 510, 954, 954, 516], ![2484, 2484, 1944, 1944, 1404, 1404, 2484, 11142, 11142, 1476, 1476, 11232, 11232, 1944, 936, 9702, 1404, 9702, 11142, 37350, 37350, 10050, 1476, 10050, 37278, 37278, 11232], ![34020, 34020, 26568, 26568, 19116, 19116, 34020, 223182, 223182, 20196, 20196, 209304, 209304, 26568, 12744, 173070, 19116, 173070, 223182, 993438, 993438, 179586, 20196, 179586, 958446, 958446, 209304], ![465588, 465588, 363528, 363528, 261468, 261468, 465588, 4023270, 4023270, 276372, 276372, 3621672, 3621672, 363528, 174312, 2913894, 261468, 2913894, 4023270, 22210038, 22210038, 3033018, 276372, 3033018, 20838870, 20838870, 3621672], ![6371460, 6371460, 4974696, 4974696, 3577932, 3577932, 6371460, 68322366, 68322366, 3782052, 3782052, 59919912, 59919912, 4974696, 2385288, 47327166, 3577932, 47327166, 68322366, 449438382, 449438382, 49380354, 3782052, 49380354, 412458318, 412458318, 59919912], ![87191316, 87191316, 68076936, 68076936, 48962556, 48962556, 87191316, 1116505782, 1116505782, 51756084, 51756084, 961725960, 961725960, 68076936, 32641704, 749602998, 48962556, 749602998, 1116505782, 8519487174, 8519487174, 783513162, 51756084, 783513162, 7681405446, 7681405446, 961725960], ![1193183460, 1193183460, 931609512, 931609512, 670035564, 670035564, 1193183460, 17763290766, 17763290766, 708264324, 708264324, 15100570152, 15100570152, 931609512, 446690376, 11653127694, 670035564, 11653127694, 17763290766, 154178657982, 154178657982, 12196766322, 708264324, 12196766322, 137032507998, 137032507998, 15100570152]]$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229691StripData.W` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229691: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229691>.

*Commentary.*

The leading 14-state block and the ten-state zero-budget submatrix call HardinA229583StripData.T. In the lower sector, shared positions are 1,3,4,5,6,7,9,10,11,12; added positions are 0,2,8. Matrix.fromBlocks and submatrix restore this order. Only added-state interactions remain literal. The other tables give initial weights, terminal acceptance and successive forward weights.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229691StripData.T`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229691StripData.Valid`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229691StripData.W`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229691StripData.cl`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229691StripData.initial`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229691StripData.terminal`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177PairTransfer](../../../Combinatorics/TraceAvoidingArrays/HardinA233177PairTransfer.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229583StripData](HardinA229583StripData.md)
