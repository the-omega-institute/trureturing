# Finite vector relation for one-defect HDA strips

## Abstract

Finite vector relation for one-defect HDA strips

Continuation counts are resolved by the number of remaining monochromatic bonds. Zero-defect continuations follow the five-row proper-colouring transfer.

**Definition 1.1 (countCut).**

$$\forall (p: \operatorname{HardinA233178Chromatic}.\operatorname{Column}), (\forall (q: \operatorname{HardinA233178Chromatic}.\operatorname{Column}), ((\operatorname{HardinA229538StripCertificate}.\operatorname{countCut}\left(p, q\right): \operatorname{Nat}) = (((((((((((((\operatorname{if} (\operatorname{HardinA233178Chromatic}.\operatorname{colour}\left(p, 0\right) = \operatorname{HardinA233178Chromatic}.\operatorname{colour}\left(q, 0\right)) \operatorname{then} 1 \operatorname{else} 0)) + ((\operatorname{if} (\operatorname{HardinA233178Chromatic}.\operatorname{colour}\left(p, 0\right) = \operatorname{HardinA233178Chromatic}.\operatorname{colour}\left(q, 1\right)) \operatorname{then} 1 \operatorname{else} 0))) + ((\operatorname{if} (\operatorname{HardinA233178Chromatic}.\operatorname{colour}\left(p, 1\right) = \operatorname{HardinA233178Chromatic}.\operatorname{colour}\left(q, 0\right)) \operatorname{then} 1 \operatorname{else} 0))) + ((\operatorname{if} (\operatorname{HardinA233178Chromatic}.\operatorname{colour}\left(p, 1\right) = \operatorname{HardinA233178Chromatic}.\operatorname{colour}\left(q, 1\right)) \operatorname{then} 1 \operatorname{else} 0))) + ((\operatorname{if} (\operatorname{HardinA233178Chromatic}.\operatorname{colour}\left(p, 1\right) = \operatorname{HardinA233178Chromatic}.\operatorname{colour}\left(q, 2\right)) \operatorname{then} 1 \operatorname{else} 0))) + ((\operatorname{if} (\operatorname{HardinA233178Chromatic}.\operatorname{colour}\left(p, 2\right) = \operatorname{HardinA233178Chromatic}.\operatorname{colour}\left(q, 1\right)) \operatorname{then} 1 \operatorname{else} 0))) + ((\operatorname{if} (\operatorname{HardinA233178Chromatic}.\operatorname{colour}\left(p, 2\right) = \operatorname{HardinA233178Chromatic}.\operatorname{colour}\left(q, 2\right)) \operatorname{then} 1 \operatorname{else} 0))) + ((\operatorname{if} (\operatorname{HardinA233178Chromatic}.\operatorname{colour}\left(p, 2\right) = \operatorname{HardinA233178Chromatic}.\operatorname{colour}\left(q, 3\right)) \operatorname{then} 1 \operatorname{else} 0))) + ((\operatorname{if} (\operatorname{HardinA233178Chromatic}.\operatorname{colour}\left(p, 3\right) = \operatorname{HardinA233178Chromatic}.\operatorname{colour}\left(q, 2\right)) \operatorname{then} 1 \operatorname{else} 0))) + ((\operatorname{if} (\operatorname{HardinA233178Chromatic}.\operatorname{colour}\left(p, 3\right) = \operatorname{HardinA233178Chromatic}.\operatorname{colour}\left(q, 3\right)) \operatorname{then} 1 \operatorname{else} 0))) + ((\operatorname{if} (\operatorname{HardinA233178Chromatic}.\operatorname{colour}\left(p, 3\right) = \operatorname{HardinA233178Chromatic}.\operatorname{colour}\left(q, 4\right)) \operatorname{then} 1 \operatorname{else} 0))) + ((\operatorname{if} (\operatorname{HardinA233178Chromatic}.\operatorname{colour}\left(p, 4\right) = \operatorname{HardinA233178Chromatic}.\operatorname{colour}\left(q, 3\right)) \operatorname{then} 1 \operatorname{else} 0))) + ((\operatorname{if} (\operatorname{HardinA233178Chromatic}.\operatorname{colour}\left(p, 4\right) = \operatorname{HardinA233178Chromatic}.\operatorname{colour}\left(q, 4\right)) \operatorname{then} 1 \operatorname{else} 0))))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538StripCertificate.countCut` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229538: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229538>.

*Commentary.*

The cost counts the colour coincidences at the thirteen oriented pairs of row positions.

**Theorem 1.2 (cost_countCut).**

$$\forall (p: \operatorname{HardinA233178Chromatic}.\operatorname{Column}), (\forall (q: \operatorname{HardinA233178Chromatic}.\operatorname{Column}), (\operatorname{HardinA229538StripData}.\operatorname{cost}\left(p, q\right) = \operatorname{HardinA229538StripCertificate}.\operatorname{countCut}\left(p, q\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538StripCertificate.cost_countCut` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229538: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229538>.

*Commentary.*

The sum of the thirteen indicators equals the number of monochromatic bonds on the cut.

**Definition 1.3 (movesOne).**

$$(\operatorname{HardinA229538StripCertificate}.\operatorname{movesOne}: \operatorname{HardinA233178Chromatic}.\operatorname{Column} \to \operatorname{List}\left(\operatorname{HardinA233178Chromatic}.\operatorname{Column}\right))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538StripCertificate.movesOne` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229538: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229538>.

*Commentary.*

The entries are the successor columns that exhaust one unit of the remaining defect budget.

**Theorem 1.4 (step_one).**

$$\forall (w: \operatorname{HardinA233178Chromatic}.\operatorname{Column} \to \operatorname{Int}), (\forall (p: \operatorname{HardinA233178Chromatic}.\operatorname{Column}), (\operatorname{Matrix}.\operatorname{mulVec}\left(\operatorname{HardinA229538StripData}.\operatorname{oneDefect}, w\right)\left(p\right) = \operatorname{List}.\operatorname{sum}\left(\operatorname{List}.\operatorname{map}\left(w, \operatorname{HardinA229538StripCertificate}.\operatorname{movesOne}\left(p\right)\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538StripCertificate.step_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229538: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229538>.

*Commentary.*

The action of the exact-one-cut matrix is a sum over its successors.

**Definition 1.5 (weights).**

$$(\operatorname{HardinA229538StripCertificate}.\operatorname{weights}: \operatorname{Fin}\left(23\right) \to \left(\operatorname{Fin}\left(12\right) \to \operatorname{Int}\right))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538StripCertificate.weights` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229538: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229538>.

*Commentary.*

These coefficients express zero-defect continuations in terms of the first twelve continuation vectors.

**Definition 1.6 (classIndex).**

$$(\operatorname{HardinA229538StripCertificate}.\operatorname{classIndex}: \operatorname{HardinA233178Chromatic}.\operatorname{Column} \to \operatorname{Fin}\left(25\right))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538StripCertificate.classIndex` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229538: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229538>.

*Commentary.*

The lookup classifies five-entry boundary columns under colour permutation and row reversal.

**Definition 1.7 (tableOne).**

$$(\operatorname{HardinA229538StripCertificate}.\operatorname{tableOne}: \operatorname{Fin}\left(23\right) \to \left(\operatorname{HardinA233178Chromatic}.\operatorname{Column} \to \operatorname{Int}\right))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538StripCertificate.tableOne` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229538: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229538>.

*Commentary.*

Each row gives one-defect continuations at one exponent, indexed by the class of the boundary column.

**Definition 1.8 (zeroValues).**

$$\forall (n: \operatorname{Fin}\left(23\right)), (\forall (p: \operatorname{HardinA233178Chromatic}.\operatorname{Column}), ((\operatorname{HardinA229538StripCertificate}.\operatorname{zeroValues}\left(n, p\right): \operatorname{Int}) = (\operatorname{if} ((h: \operatorname{Fin}.\operatorname{val}\left(n\right) < 12)) \operatorname{then} \operatorname{HardinA233178Chromatic}.\operatorname{table}\left(\operatorname{Fin}.\operatorname{castLT}\left(n, h\right), p\right) \operatorname{else} \sum_{(j: \operatorname{Fin}\left(12\right))} ((\operatorname{HardinA229538StripCertificate}.\operatorname{weights}\left(n, j\right)) \cdot (\operatorname{HardinA233178Chromatic}.\operatorname{table}\left(j, p\right))))))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538StripCertificate.zeroValues` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229538: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229538>.

*Commentary.*

For larger exponents the zero-defect values are linear combinations of the twelve proper-colouring vectors.

**Theorem 1.9 (weight_eq).**

$$\forall (n: \operatorname{Fin}\left(23\right)), (\operatorname{HardinA229538StripCertificate}.\operatorname{zeroValues}\left(n\right) = \sum_{(j: \operatorname{Fin}\left(12\right))} (\operatorname{SMul}.\operatorname{smul}\left(\operatorname{HardinA229538StripCertificate}.\operatorname{weights}\left(n, j\right), \operatorname{HardinA233178Chromatic}.\operatorname{table}\left(j\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538StripCertificate.weight_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229538: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229538>.

*Commentary.*

The same coefficient formula also holds at the tabulated exponents.

**Theorem 1.10 (zero_values).**

$$\forall (n: \operatorname{Fin}\left(23\right)), (\operatorname{HardinA229538StripCertificate}.\operatorname{zeroValues}\left(n\right) = \operatorname{Matrix}.\operatorname{mulVec}\left((\operatorname{HardinA233178Chromatic}.\operatorname{T})^{\operatorname{Fin}.\operatorname{val}\left(n\right)}, (1: \operatorname{HardinA233178Chromatic}.\operatorname{Column} \to \operatorname{Int})\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538StripCertificate.zero_values` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229538: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229538>.

*Commentary.*

The reconstructed value is the proper-colouring continuation vector at each exponent.

**Theorem 1.11 (table_powers).**

$$\forall (n: \operatorname{Fin}\left(23\right)), (\operatorname{Matrix}.\operatorname{mulVec}\left((\operatorname{HardinA229538StripData}.\operatorname{transfer})^{\operatorname{Fin}.\operatorname{val}\left(n\right)}, \operatorname{HardinA229538StripData}.\operatorname{terminal}\right) = \operatorname{Sum}.\operatorname{elim}\left(\operatorname{HardinA229538StripCertificate}.\operatorname{tableOne}\left(n\right), \operatorname{Matrix}.\operatorname{mulVec}\left((\operatorname{HardinA233178Chromatic}.\operatorname{T})^{\operatorname{Fin}.\operatorname{val}\left(n\right)}, (1: \operatorname{HardinA233178Chromatic}.\operatorname{Column} \to \operatorname{Int})\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538StripCertificate.table_powers` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229538: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229538>.

*Commentary.*

The first coordinate gives the one-defect continuations and the second gives the inherited proper-colouring continuations.

**Definition 1.12 (coefficients538).**

$$(\operatorname{HardinA229538StripCertificate}.\operatorname{coefficients538}: \operatorname{Fin}\left(20\right) \to \operatorname{Int}) = \operatorname{Matrix}.\operatorname{vecCons}\left((-1296), \operatorname{Matrix}.\operatorname{vecCons}\left(5184, \operatorname{Matrix}.\operatorname{vecCons}\left(8640, \operatorname{Matrix}.\operatorname{vecCons}\left((-64656), \operatorname{Matrix}.\operatorname{vecCons}\left(43848, \operatorname{Matrix}.\operatorname{vecCons}\left(214008, \operatorname{Matrix}.\operatorname{vecCons}\left((-371692), \operatorname{Matrix}.\operatorname{vecCons}\left((-48036), \operatorname{Matrix}.\operatorname{vecCons}\left(498819, \operatorname{Matrix}.\operatorname{vecCons}\left((-211910), \operatorname{Matrix}.\operatorname{vecCons}\left((-256127), \operatorname{Matrix}.\operatorname{vecCons}\left(183692, \operatorname{Matrix}.\operatorname{vecCons}\left(55115, \operatorname{Matrix}.\operatorname{vecCons}\left((-59620), \operatorname{Matrix}.\operatorname{vecCons}\left((-4121), \operatorname{Matrix}.\operatorname{vecCons}\left(8804, \operatorname{Matrix}.\operatorname{vecCons}\left((-123), \operatorname{Matrix}.\operatorname{vecCons}\left((-566), \operatorname{Matrix}.\operatorname{vecCons}\left(26, \operatorname{Matrix}.\operatorname{vecCons}\left(12, \operatorname{Matrix}.\operatorname{vecEmpty}\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538StripCertificate.coefficients538` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229538: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229538>.

*Commentary.*

The entries are ordered from the smallest shift of the recurrence to the largest.

**Theorem 1.13 (vector_polynomial).**

$$\operatorname{Matrix}.\operatorname{mulVec}\left((\operatorname{HardinA229538StripData}.\operatorname{transfer})^{22}, \operatorname{HardinA229538StripData}.\operatorname{terminal}\right) = \sum_{(k: \operatorname{Fin}\left(20\right))} (\operatorname{SMul}.\operatorname{smul}\left(\operatorname{HardinA229538StripCertificate}.\operatorname{coefficients538}\left(k\right), \operatorname{Matrix}.\operatorname{mulVec}\left((\operatorname{HardinA229538StripData}.\operatorname{transfer})^{(2) + (\operatorname{Fin}.\operatorname{val}\left(k\right))}, \operatorname{HardinA229538StripData}.\operatorname{terminal}\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538StripCertificate.vector_polynomial` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229538: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229538>.

*Commentary.*

The relation holds simultaneously for all boundary columns and both residual budgets.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538StripCertificate.classIndex`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538StripCertificate.coefficients538`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538StripCertificate.cost_countCut`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538StripCertificate.countCut`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538StripCertificate.movesOne`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538StripCertificate.step_one`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538StripCertificate.tableOne`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538StripCertificate.table_powers`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538StripCertificate.vector_polynomial`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538StripCertificate.weight_eq`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538StripCertificate.weights`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538StripCertificate.zeroValues`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538StripCertificate.zero_values`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/FiveRow/HardinA233178Chromatic](../../../../Combinatorics/TraceAvoidingArrays/FiveRow/HardinA233178Chromatic.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/FiveRow/HardinA233178Recurrence](../../../../Combinatorics/TraceAvoidingArrays/FiveRow/HardinA233178Recurrence.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233260Literal](../../../../Combinatorics/TraceAvoidingArrays/HardinA233260Literal.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538StripData](HardinA229538StripData.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/DefectTransfer](../../StripDefects/DefectTransfer.md)
