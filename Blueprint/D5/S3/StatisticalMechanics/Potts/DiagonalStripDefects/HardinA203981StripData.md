# Six-column boundary classes

## Abstract

Six-column boundary classes

**Theorem 1.1 (Diagonal and antidiagonal bonds).**

$$\operatorname{\mathit{HardinA229637RowColumn}}.\operatorname{\mathit{betw}}\left(6\right) = \{(0, 1), (1, 0), (1, 2), (2, 1), (2, 3), (3, 2), (3, 4), (4, 3), (4, 5), (5, 4)\}$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203981StripData.between_six` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2012). *OEIS A203981: canonical diagonal and antidiagonal strip colourings*. URL: <https://oeis.org/A203981>.

*Commentary.*

Each pair lists the upper and lower column indices of a bond. HardinA229635Literal.same_between identifies the width-six bond set with the union whose pairs are listed here.

**Definition 1.2 (Column as a three-position row).**

$$(\forall c: \operatorname{\mathit{HardinA233258PairTransfer}}.\operatorname{\mathit{Col}}, (\forall i: \operatorname{\mathit{Fin}}\left(3\right), (\operatorname{\mathit{HardinA203981StripData}}.\operatorname{\mathit{columnRows}}\left(c, i\right) = \operatorname{\mathit{HardinA233258PairTransfer}}.\operatorname{\mathit{column}}\left(c, i\right)))) \land (\forall r: (\operatorname{\mathit{Fin}}\left(3\right)) \to (\operatorname{\mathit{Fin}}\left(3\right)), (\operatorname{\mathit{Equiv}}.\operatorname{\mathit{symm}}\left(\operatorname{\mathit{HardinA203981StripData}}.\operatorname{\mathit{columnRows}}\right)\left(r\right) = (r\left(0\right), (r\left(1\right), r\left(2\right)))))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203981StripData.columnRows` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2012). *OEIS A203981: canonical diagonal and antidiagonal strip colourings*. URL: <https://oeis.org/A203981>.

*Commentary.*

The inverse reads a triple of entries from the three positions.

**Definition 1.3 (Parity triples).**

$$(\forall p: (\operatorname{\mathit{Fin}}\left(6\right)) \to (\operatorname{\mathit{Fin}}\left(3\right)), (\operatorname{\mathit{HardinA203981StripData}}.\operatorname{\mathit{parityRows}}\left(p\right) = ((p\left(0\right), (p\left(2\right), p\left(4\right))), (p\left(5\right), (p\left(3\right), p\left(1\right)))))) \land (\forall t: (\operatorname{\mathit{HardinA233258PairTransfer}}.\operatorname{\mathit{Col}}) \times (\operatorname{\mathit{HardinA233258PairTransfer}}.\operatorname{\mathit{Col}}), (\operatorname{\mathit{Equiv}}.\operatorname{\mathit{symm}}\left(\operatorname{\mathit{HardinA203981StripData}}.\operatorname{\mathit{parityRows}}\right)\left(t\right) = [\operatorname{\mathit{Prod}}.\operatorname{\mathit{fst}}\left(\operatorname{\mathit{Prod}}.\operatorname{\mathit{fst}}\left(t\right)\right), \operatorname{\mathit{Prod}}.\operatorname{\mathit{snd}}\left(\operatorname{\mathit{Prod}}.\operatorname{\mathit{snd}}\left(\operatorname{\mathit{Prod}}.\operatorname{\mathit{snd}}\left(t\right)\right)\right), \operatorname{\mathit{Prod}}.\operatorname{\mathit{fst}}\left(\operatorname{\mathit{Prod}}.\operatorname{\mathit{snd}}\left(\operatorname{\mathit{Prod}}.\operatorname{\mathit{fst}}\left(t\right)\right)\right), \operatorname{\mathit{Prod}}.\operatorname{\mathit{fst}}\left(\operatorname{\mathit{Prod}}.\operatorname{\mathit{snd}}\left(\operatorname{\mathit{Prod}}.\operatorname{\mathit{snd}}\left(t\right)\right)\right), \operatorname{\mathit{Prod}}.\operatorname{\mathit{snd}}\left(\operatorname{\mathit{Prod}}.\operatorname{\mathit{snd}}\left(\operatorname{\mathit{Prod}}.\operatorname{\mathit{fst}}\left(t\right)\right)\right), \operatorname{\mathit{Prod}}.\operatorname{\mathit{fst}}\left(\operatorname{\mathit{Prod}}.\operatorname{\mathit{snd}}\left(t\right)\right)]))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203981StripData.parityRows` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2012). *OEIS A203981: canonical diagonal and antidiagonal strip colourings*. URL: <https://oeis.org/A203981>.

*Commentary.*

The two triples read the even columns from the left and the odd columns from the right. The inverse interleaves the triples in column order.

**Definition 1.4 (Pair of triple patterns).**

$$(\operatorname{\mathit{HardinA203981StripData}}.\operatorname{\mathit{pairClass}}: (\operatorname{\mathit{Fin}}\left(5\right)) \to ((\operatorname{\mathit{Fin}}\left(5\right)) \to (\operatorname{\mathit{Fin}}\left(15\right)))) = [[0, 1, 2, 3, 4], [1, 5, 6, 7, 8], [2, 6, 9, 10, 11], [3, 7, 10, 12, 13], [4, 8, 11, 13, 14]]$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203981StripData.pairClass` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2012). *OEIS A203981: canonical diagonal and antidiagonal strip colourings*. URL: <https://oeis.org/A203981>.

*Commentary.*

The table stores the positions computed by the indexed lookup in the next statement.

**Theorem 1.5 (Position of the sorted pair).**

$$\forall x: \operatorname{\mathit{Fin}}\left(5\right), (\forall y: \operatorname{\mathit{Fin}}\left(5\right), (\operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(\operatorname{\mathit{HardinA203981StripData}}.\operatorname{\mathit{pairClass}}\left(x, y\right)\right) = \operatorname{\mathit{List}}.\operatorname{\mathit{idxOf}}\left(\operatorname{\mathit{List}}.\operatorname{\mathit{ofFn}}\left(\operatorname{\mathit{HardinA203981StripData}}.\operatorname{\mathit{classPair}}\right), (\operatorname{\mathit{min}}\left(x, y\right), \operatorname{\mathit{max}}\left(x, y\right))\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203981StripData.pairClass_eq_lookup` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2012). *OEIS A203981: canonical diagonal and antidiagonal strip colourings*. URL: <https://oeis.org/A203981>.

*Commentary.*

The label is the zero-based position of the sorted pair in the representative list.

**Definition 1.6 (Boundary class).**

$$\forall p: (\operatorname{\mathit{Fin}}\left(6\right)) \to (\operatorname{\mathit{Fin}}\left(3\right)), (\operatorname{\mathit{HardinA203981StripData}}.\operatorname{\mathit{boundary}}\left(p\right) = \operatorname{\mathit{HardinA203981StripData}}.\operatorname{\mathit{pairClass}}\left(\operatorname{\mathit{HardinA233258PairTransfer}}.\operatorname{\mathit{cls}}\left(\operatorname{\mathit{Prod}}.\operatorname{\mathit{fst}}\left(\operatorname{\mathit{HardinA203981StripData}}.\operatorname{\mathit{parityRows}}\left(p\right)\right)\right), \operatorname{\mathit{HardinA233258PairTransfer}}.\operatorname{\mathit{cls}}\left(\operatorname{\mathit{Prod}}.\operatorname{\mathit{snd}}\left(\operatorname{\mathit{HardinA203981StripData}}.\operatorname{\mathit{parityRows}}\left(p\right)\right)\right)\right))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203981StripData.boundary` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2012). *OEIS A203981: canonical diagonal and antidiagonal strip colourings*. URL: <https://oeis.org/A203981>.

*Commentary.*

The boundary index combines the equality classes of the two parity triples.

**Definition 1.7 (Sorted triple-class pairs).**

$$(\operatorname{\mathit{HardinA203981StripData}}.\operatorname{\mathit{classPair}}: (\operatorname{\mathit{Fin}}\left(15\right)) \to ((\operatorname{\mathit{Fin}}\left(5\right)) \times (\operatorname{\mathit{Fin}}\left(5\right)))) = [(0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, 1), (1, 2), (1, 3), (1, 4), (2, 2), (2, 3), (2, 4), (3, 3), (3, 4), (4, 4)]$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203981StripData.classPair` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2012). *OEIS A203981: canonical diagonal and antidiagonal strip colourings*. URL: <https://oeis.org/A203981>.

*Commentary.*

The two entries are in increasing order with equality allowed.

**Definition 1.8 (Representative rows).**

$$\forall i: \operatorname{\mathit{Fin}}\left(15\right), (\operatorname{\mathit{HardinA203981StripData}}.\operatorname{\mathit{representatives}}\left(i\right) = \operatorname{\mathit{Equiv}}.\operatorname{\mathit{symm}}\left(\operatorname{\mathit{HardinA203981StripData}}.\operatorname{\mathit{parityRows}}\right)\left((\operatorname{\mathit{HardinA233258PairTransfer}}.\operatorname{\mathit{representatives}}\left(\operatorname{\mathit{Prod}}.\operatorname{\mathit{fst}}\left(\operatorname{\mathit{HardinA203981StripData}}.\operatorname{\mathit{classPair}}\left(i\right)\right)\right), \operatorname{\mathit{HardinA233258PairTransfer}}.\operatorname{\mathit{representatives}}\left(\operatorname{\mathit{Prod}}.\operatorname{\mathit{snd}}\left(\operatorname{\mathit{HardinA203981StripData}}.\operatorname{\mathit{classPair}}\left(i\right)\right)\right))\right))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203981StripData.representatives` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2012). *OEIS A203981: canonical diagonal and antidiagonal strip colourings*. URL: <https://oeis.org/A203981>.

*Commentary.*

Each row interleaves two representatives of the three-position equality classes.

**Definition 1.9 (Unordered pair weights).**

$$\forall (\mathit{alpha}: \mathit{Type}) [\operatorname{\mathit{Mul}}\left(\mathit{alpha}\right)] [\operatorname{\mathit{Add}}\left(\mathit{alpha}\right)] [\operatorname{\mathit{Zero}}\left(\mathit{alpha}\right)], (\forall u: (\operatorname{\mathit{Fin}}\left(5\right)) \to (\mathit{alpha}), (\forall v: (\operatorname{\mathit{Fin}}\left(5\right)) \to (\mathit{alpha}), (\forall j: \operatorname{\mathit{Fin}}\left(15\right), (\operatorname{\mathit{HardinA203981StripData}}.\operatorname{\mathit{unordered}}\left(u, v, j\right) = u\left(\operatorname{\mathit{Prod}}.\operatorname{\mathit{fst}}\left(\operatorname{\mathit{HardinA203981StripData}}.\operatorname{\mathit{classPair}}\left(j\right)\right)\right) \cdot v\left(\operatorname{\mathit{Prod}}.\operatorname{\mathit{snd}}\left(\operatorname{\mathit{HardinA203981StripData}}.\operatorname{\mathit{classPair}}\left(j\right)\right)\right) + (\operatorname{\mathit{if}} (\operatorname{\mathit{Prod}}.\operatorname{\mathit{fst}}\left(\operatorname{\mathit{HardinA203981StripData}}.\operatorname{\mathit{classPair}}\left(j\right)\right) = \operatorname{\mathit{Prod}}.\operatorname{\mathit{snd}}\left(\operatorname{\mathit{HardinA203981StripData}}.\operatorname{\mathit{classPair}}\left(j\right)\right)) \operatorname{\mathit{then}} 0 \operatorname{\mathit{else}} u\left(\operatorname{\mathit{Prod}}.\operatorname{\mathit{snd}}\left(\operatorname{\mathit{HardinA203981StripData}}.\operatorname{\mathit{classPair}}\left(j\right)\right)\right) \cdot v\left(\operatorname{\mathit{Prod}}.\operatorname{\mathit{fst}}\left(\operatorname{\mathit{HardinA203981StripData}}.\operatorname{\mathit{classPair}}\left(j\right)\right)\right))))))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203981StripData.unordered` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2012). *OEIS A203981: canonical diagonal and antidiagonal strip colourings*. URL: <https://oeis.org/A203981>.

*Commentary.*

Equal classes contribute once. Distinct classes contribute in both orders.

**Definition 1.10 (Zero-cost half-strip block).**

$$\forall i: \operatorname{\mathit{Fin}}\left(5\right), (\forall j: \operatorname{\mathit{Fin}}\left(5\right), (\operatorname{\mathit{HardinA203981StripData}}.\operatorname{\mathit{halfZero}}\left(i, j\right) = \operatorname{\mathit{HardinA233258PairTransfer}}.\operatorname{Q}\left(i, \operatorname{\mathit{Equiv}}.\operatorname{\mathit{swap}}\left(1, 3, j\right)\right)))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203981StripData.halfZero` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2012). *OEIS A203981: canonical diagonal and antidiagonal strip colourings*. URL: <https://oeis.org/A203981>.

*Commentary.*

The half-strip reads the target triple backwards, which exchanges classes 1 and 3.

**Definition 1.11 (Product of two class transitions).**

$$\forall (\mathit{alpha}: \mathit{Type}) [\operatorname{\mathit{Mul}}\left(\mathit{alpha}\right)] [\operatorname{\mathit{Add}}\left(\mathit{alpha}\right)] [\operatorname{\mathit{Zero}}\left(\mathit{alpha}\right)], (\forall A: \operatorname{\mathit{Matrix}}\left(\operatorname{\mathit{Fin}}\left(5\right), \operatorname{\mathit{Fin}}\left(5\right), \mathit{alpha}\right), (\forall B: \operatorname{\mathit{Matrix}}\left(\operatorname{\mathit{Fin}}\left(5\right), \operatorname{\mathit{Fin}}\left(5\right), \mathit{alpha}\right), (\forall i: \operatorname{\mathit{Fin}}\left(15\right), (\forall j: \operatorname{\mathit{Fin}}\left(15\right), (\operatorname{\mathit{HardinA203981StripData}}.\operatorname{\mathit{classProduct}}\left(A, B, i, j\right) = \operatorname{\mathit{HardinA203981StripData}}.\operatorname{\mathit{unordered}}\left(A\left(\operatorname{\mathit{Prod}}.\operatorname{\mathit{fst}}\left(\operatorname{\mathit{HardinA203981StripData}}.\operatorname{\mathit{classPair}}\left(i\right)\right)\right), B\left(\operatorname{\mathit{Prod}}.\operatorname{\mathit{snd}}\left(\operatorname{\mathit{HardinA203981StripData}}.\operatorname{\mathit{classPair}}\left(i\right)\right)\right), j\right))))))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203981StripData.classProduct` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2012). *OEIS A203981: canonical diagonal and antidiagonal strip colourings*. URL: <https://oeis.org/A203981>.

*Commentary.*

The first and second source classes select the two rows whose target weights are combined.

**Definition 1.12 (Zero-cost transfer).**

$$\operatorname{\mathit{HardinA203981StripData}}.\operatorname{T} = \operatorname{\mathit{HardinA203981StripData}}.\operatorname{\mathit{classProduct}}\left(\operatorname{\mathit{HardinA203981StripData}}.\operatorname{\mathit{halfZero}}, \operatorname{\mathit{HardinA203981StripData}}.\operatorname{\mathit{halfZero}}\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203981StripData.T` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2012). *OEIS A203981: canonical diagonal and antidiagonal strip colourings*. URL: <https://oeis.org/A203981>.

*Commentary.*

Each parity class contributes its zero-cost transition.

**Definition 1.13 (Initial half-strip populations).**

$$\forall i: \operatorname{\mathit{Fin}}\left(5\right), (\operatorname{\mathit{HardinA203981StripData}}.\operatorname{\mathit{halfInitial}}\left(i\right) = \operatorname{\mathit{HardinA229588Strip}}.\operatorname{\mathit{initial}}\left(\operatorname{\mathit{Fin}}.\operatorname{\mathit{castAdd}}\left(5, i\right)\right))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203981StripData.halfInitial` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2012). *OEIS A203981: canonical diagonal and antidiagonal strip colourings*. URL: <https://oeis.org/A203981>.

*Commentary.*

The first five entries of the half-strip initial vector are its class populations.

**Definition 1.14 (Labelled first-row distribution).**

$$\operatorname{\mathit{HardinA203981StripData}}.\operatorname{\mathit{initial}} = \operatorname{\mathit{HardinA203981StripData}}.\operatorname{\mathit{unordered}}\left(\operatorname{\mathit{HardinA203981StripData}}.\operatorname{\mathit{halfInitial}}, \operatorname{\mathit{HardinA203981StripData}}.\operatorname{\mathit{halfInitial}}\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203981StripData.initial` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2012). *OEIS A203981: canonical diagonal and antidiagonal strip colourings*. URL: <https://oeis.org/A203981>.

*Commentary.*

The two independent labelled triples contribute the product of their populations.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203981StripData.T`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203981StripData.between_six`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203981StripData.boundary`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203981StripData.classPair`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203981StripData.classProduct`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203981StripData.columnRows`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203981StripData.halfInitial`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203981StripData.halfZero`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203981StripData.initial`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203981StripData.pairClass`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203981StripData.pairClass_eq_lookup`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203981StripData.parityRows`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203981StripData.representatives`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203981StripData.unordered`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233258PairTransfer](../../../Combinatorics/TraceAvoidingArrays/HardinA233258PairTransfer.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635Literal](../CrossedStripDefectsWide/P5b/HardinA229635Literal.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/WidthSix/HardinA229532StripData](../CrossedStripDefectsWide/WidthSix/HardinA229532StripData.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/DefectTransfer](../StripDefects/DefectTransfer.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229588Strip](../StripDefects/HardinA229588Strip.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229637RowColumn](../StripDefects/HardinA229637RowColumn.md)
