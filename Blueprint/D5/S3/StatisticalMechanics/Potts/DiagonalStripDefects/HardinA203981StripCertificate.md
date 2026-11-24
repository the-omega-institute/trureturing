# Finite checks for the zero-defect recurrence

## Abstract

Finite checks for the zero-defect recurrence

**Definition 1.1 (Exact cost on one parity class).**

$$\forall a: \operatorname{\mathit{HardinA233258PairTransfer}}.\operatorname{\mathit{Col}}, (\forall b: \operatorname{\mathit{HardinA233258PairTransfer}}.\operatorname{\mathit{Col}}, (\operatorname{\mathit{HardinA203981StripCertificate}}.\operatorname{\mathit{halfCost}}\left(a, b\right) = \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229588Strip}}.\operatorname{\mathit{between}}, \operatorname{\mathit{HardinA203981StripData}}.\operatorname{\mathit{columnRows}}\left(a\right), [\operatorname{\mathit{Prod}}.\operatorname{\mathit{snd}}\left(\operatorname{\mathit{Prod}}.\operatorname{\mathit{snd}}\left(b\right)\right), \operatorname{\mathit{Prod}}.\operatorname{\mathit{fst}}\left(\operatorname{\mathit{Prod}}.\operatorname{\mathit{snd}}\left(b\right)\right), \operatorname{\mathit{Prod}}.\operatorname{\mathit{fst}}\left(b\right)]\right)))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203981StripCertificate.halfCost` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2012). *OEIS A203981: canonical diagonal and antidiagonal strip colourings*. URL: <https://oeis.org/A203981>.

*Commentary.*

The five half-strip bonds read the target triple in reverse order.

**Theorem 1.2 (Allocate exact cost between the parity classes).**

$$\forall d: \mathit{Nat}, (\forall m: (\operatorname{\mathit{Fin}}\left(d + 1\right)) \to (\operatorname{\mathit{Matrix}}\left(\operatorname{\mathit{Fin}}\left(5\right), \operatorname{\mathit{Fin}}\left(5\right), \mathit{Int}\right)), (\forall p: (\operatorname{\mathit{Fin}}\left(6\right)) \to (\operatorname{\mathit{Fin}}\left(3\right)), (\forall j: \operatorname{\mathit{Fin}}\left(15\right), ((\forall k: \operatorname{\mathit{Fin}}\left(d + 1\right), (\forall a: \operatorname{\mathit{HardinA233258PairTransfer}}.\operatorname{\mathit{Col}}, (\forall c: \operatorname{\mathit{Fin}}\left(5\right), (((a = \operatorname{\mathit{Prod}}.\operatorname{\mathit{fst}}\left(\operatorname{\mathit{HardinA203981StripData}}.\operatorname{\mathit{parityRows}}\left(p\right)\right)) \lor (a = \operatorname{\mathit{Prod}}.\operatorname{\mathit{snd}}\left(\operatorname{\mathit{HardinA203981StripData}}.\operatorname{\mathit{parityRows}}\left(p\right)\right))) \to ((c = \operatorname{\mathit{Prod}}.\operatorname{\mathit{fst}}\left(\operatorname{\mathit{HardinA203981StripData}}.\operatorname{\mathit{classPair}}\left(j\right)\right)) \lor (c = \operatorname{\mathit{Prod}}.\operatorname{\mathit{snd}}\left(\operatorname{\mathit{HardinA203981StripData}}.\operatorname{\mathit{classPair}}\left(j\right)\right))) \to (\sum_{b: \operatorname{\mathit{HardinA233258PairTransfer}}.\operatorname{\mathit{Col}}} ((\operatorname{\mathit{if}} ((\operatorname{\mathit{HardinA203981StripCertificate}}.\operatorname{\mathit{halfCost}}\left(a, b\right) = \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(k\right)) \land (\operatorname{\mathit{HardinA233258PairTransfer}}.\operatorname{\mathit{cls}}\left(b\right) = c)) \operatorname{\mathit{then}} (1: \mathit{Int}) \operatorname{\mathit{else}} (0: \mathit{Int}))) = m\left(k, \operatorname{\mathit{HardinA233258PairTransfer}}.\operatorname{\mathit{cls}}\left(a\right), c\right)))))) \to (\sum_{r: (\operatorname{\mathit{Fin}}\left(6\right)) \to (\operatorname{\mathit{Fin}}\left(3\right))} ((\operatorname{\mathit{if}} ((\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229637RowColumn}}.\operatorname{\mathit{betw}}\left(6\right), p, r\right) = d) \land (\operatorname{\mathit{HardinA203981StripData}}.\operatorname{\mathit{boundary}}\left(r\right) = j)) \operatorname{\mathit{then}} (1: \mathit{Int}) \operatorname{\mathit{else}} (0: \mathit{Int}))) = \sum_{k: \operatorname{\mathit{Fin}}\left(d + 1\right)} (\operatorname{\mathit{HardinA203981StripData}}.\operatorname{\mathit{unordered}}\left(m\left(k, \operatorname{\mathit{HardinA233258PairTransfer}}.\operatorname{\mathit{cls}}\left(\operatorname{\mathit{Prod}}.\operatorname{\mathit{fst}}\left(\operatorname{\mathit{HardinA203981StripData}}.\operatorname{\mathit{parityRows}}\left(p\right)\right)\right)\right), m\left(\operatorname{\mathit{Fin}}.\operatorname{\mathit{rev}}\left(k\right), \operatorname{\mathit{HardinA233258PairTransfer}}.\operatorname{\mathit{cls}}\left(\operatorname{\mathit{Prod}}.\operatorname{\mathit{snd}}\left(\operatorname{\mathit{HardinA203981StripData}}.\operatorname{\mathit{parityRows}}\left(p\right)\right)\right)\right), j\right)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203981StripCertificate.allocated_counts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2012). *OEIS A203981: canonical diagonal and antidiagonal strip colourings*. URL: <https://oeis.org/A203981>.

*Commentary.*

For any source row p in Row 3 6, the count uses the two actual triples parityRows(p) and the two classes in the chosen target pair. Each summand reads the unordered target class. For k in Fin(d+1), Fin.rev(k) has natural value d minus Fin.val(k).

The half-strip count law constrains the supplied matrices. At budget zero and target class zero, the all-zero source row has four exact-cost targets. A family of zero matrices gives a right-hand sum of zero.

**Theorem 1.3 (Reindex the target triple under reversal).**

$$\forall n: \mathit{Nat}, (\forall a: \operatorname{\mathit{HardinA233258PairTransfer}}.\operatorname{\mathit{Col}}, (\forall j: \operatorname{\mathit{Fin}}\left(5\right), (\sum_{b: \operatorname{\mathit{HardinA233258PairTransfer}}.\operatorname{\mathit{Col}}} ((\operatorname{\mathit{if}} ((\operatorname{\mathit{HardinA203981StripCertificate}}.\operatorname{\mathit{halfCost}}\left(a, b\right) = n) \land (\operatorname{\mathit{HardinA233258PairTransfer}}.\operatorname{\mathit{cls}}\left(b\right) = j)) \operatorname{\mathit{then}} (1: \mathit{Int}) \operatorname{\mathit{else}} (0: \mathit{Int}))) = \sum_{b: \operatorname{\mathit{HardinA233258PairTransfer}}.\operatorname{\mathit{Col}}} ((\operatorname{\mathit{if}} ((\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229588Strip}}.\operatorname{\mathit{between}}, \operatorname{\mathit{HardinA203981StripData}}.\operatorname{\mathit{columnRows}}\left(a\right), \operatorname{\mathit{HardinA203981StripData}}.\operatorname{\mathit{columnRows}}\left(b\right)\right) = n) \land (\operatorname{\mathit{HardinA233258PairTransfer}}.\operatorname{\mathit{cls}}\left(b\right) = \operatorname{\mathit{Equiv}}.\operatorname{\mathit{swap}}\left(1, 3, j\right))) \operatorname{\mathit{then}} (1: \mathit{Int}) \operatorname{\mathit{else}} (0: \mathit{Int}))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203981StripCertificate.reversed_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2012). *OEIS A203981: canonical diagonal and antidiagonal strip colourings*. URL: <https://oeis.org/A203981>.

*Commentary.*

Reversing a triple exchanges classes 1 and 3 and preserves the other three classes.

**Theorem 1.4 (Exact zero-cost half-strip counts).**

$$\forall a: \operatorname{\mathit{HardinA233258PairTransfer}}.\operatorname{\mathit{Col}}, (\forall j: \operatorname{\mathit{Fin}}\left(5\right), (\sum_{b: \operatorname{\mathit{HardinA233258PairTransfer}}.\operatorname{\mathit{Col}}} ((\operatorname{\mathit{if}} ((\operatorname{\mathit{HardinA203981StripCertificate}}.\operatorname{\mathit{halfCost}}\left(a, b\right) = 0) \land (\operatorname{\mathit{HardinA233258PairTransfer}}.\operatorname{\mathit{cls}}\left(b\right) = j)) \operatorname{\mathit{then}} (1: \mathit{Int}) \operatorname{\mathit{else}} (0: \mathit{Int}))) = \operatorname{\mathit{HardinA203981StripData}}.\operatorname{\mathit{halfZero}}\left(\operatorname{\mathit{HardinA233258PairTransfer}}.\operatorname{\mathit{cls}}\left(a\right), j\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203981StripCertificate.zero_exact` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2012). *OEIS A203981: canonical diagonal and antidiagonal strip colourings*. URL: <https://oeis.org/A203981>.

*Commentary.*

The zero-budget transition clause of HardinA229588Strip.finite_certificate gives the count.

**Theorem 1.5 (Exact zero-cost class counts).**

$$\forall p: (\operatorname{\mathit{Fin}}\left(6\right)) \to (\operatorname{\mathit{Fin}}\left(3\right)), (\forall j: \operatorname{\mathit{Fin}}\left(15\right), (\sum_{r: (\operatorname{\mathit{Fin}}\left(6\right)) \to (\operatorname{\mathit{Fin}}\left(3\right))} ((\operatorname{\mathit{if}} ((\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229637RowColumn}}.\operatorname{\mathit{betw}}\left(6\right), p, r\right) = 0) \land (\operatorname{\mathit{HardinA203981StripData}}.\operatorname{\mathit{boundary}}\left(r\right) = j)) \operatorname{\mathit{then}} (1: \mathit{Int}) \operatorname{\mathit{else}} (0: \mathit{Int}))) = \operatorname{\mathit{HardinA203981StripData}}.\operatorname{T}\left(\operatorname{\mathit{HardinA203981StripData}}.\operatorname{\mathit{boundary}}\left(p\right), j\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203981StripCertificate.counts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2012). *OEIS A203981: canonical diagonal and antidiagonal strip colourings*. URL: <https://oeis.org/A203981>.

*Commentary.*

The ten bonds split into two copies of the three-position compatibility relation. Each half count uses the zero-budget clause of HardinA229588Strip.finite_certificate with the reversed target classes. Their products count the possible orders of the two target classes, and parity recolouring and reflection extend the result to every source row.

**Theorem 1.6 (Labelled row populations).**

$$\forall j: \operatorname{\mathit{Fin}}\left(15\right), (\sum_{r: (\operatorname{\mathit{Fin}}\left(6\right)) \to (\operatorname{\mathit{Fin}}\left(3\right))} ((\operatorname{\mathit{if}} (\operatorname{\mathit{HardinA203981StripData}}.\operatorname{\mathit{boundary}}\left(r\right) = j) \operatorname{\mathit{then}} (1: \mathit{Int}) \operatorname{\mathit{else}} (0: \mathit{Int}))) = \operatorname{\mathit{HardinA203981StripData}}.\operatorname{\mathit{initial}}\left(j\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203981StripCertificate.initial_counts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2012). *OEIS A203981: canonical diagonal and antidiagonal strip colourings*. URL: <https://oeis.org/A203981>.

*Commentary.*

The initial clause of HardinA229588Strip.finite_certificate gives the labelled populations on each parity. Equal classes contribute once and distinct classes contribute in both orders.

**Definition 1.7 (The half-strip forward vectors in degree 0).**

$$(\operatorname{\mathit{HardinA203981StripCertificate}}.\operatorname{\mathit{halfForwardZero}}: (\operatorname{\mathit{Fin}}\left(21\right)) \to ((\operatorname{\mathit{Fin}}\left(5\right)) \to (\mathit{Int})))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203981StripCertificate.halfForwardZero` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2012). *OEIS A203981: canonical diagonal and antidiagonal strip colourings*. URL: <https://oeis.org/A203981>.

*Commentary.*

The 21 by 5 integer table begins with HardinA203981StripData.halfInitial and HardinA233258PairTransfer.weights. Exponents two and three use the first five coordinates of HardinA229588Strip.W, with classes 1 and 3 exchanged at exponent three. The later rows are tabulated half-strip samples. The unordered products are checked against the full-strip update in HardinA203981StripCertificate.forward_table.

**Definition 1.8 (Forward vectors in total cost degree 0).**

$$\forall i: \operatorname{\mathit{Fin}}\left(21\right), (\forall j: \operatorname{\mathit{Fin}}\left(15\right), (\operatorname{\mathit{HardinA203981StripCertificate}}.\operatorname{W}\left(i, j\right) = \operatorname{\mathit{HardinA203981StripData}}.\operatorname{\mathit{unordered}}\left(\operatorname{\mathit{HardinA203981StripCertificate}}.\operatorname{\mathit{halfForwardZero}}\left(i\right), \operatorname{\mathit{HardinA203981StripCertificate}}.\operatorname{\mathit{halfForwardZero}}\left(i\right), j\right)))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203981StripCertificate.W` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2012). *OEIS A203981: canonical diagonal and antidiagonal strip colourings*. URL: <https://oeis.org/A203981>.

*Commentary.*

The two half-strip vectors of degree zero are combined at each exponent through twenty.

**Definition 1.9 (Recurrence coefficients).**

$$(\operatorname{\mathit{HardinA203981StripCertificate}}.\operatorname{\mathit{coeff}}: (\operatorname{\mathit{Fin}}\left(6\right)) \to (\mathit{Int})) = [-6561, 3645, 2025, -963, -45, 25]$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203981StripCertificate.coeff` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2012). *OEIS A203981: canonical diagonal and antidiagonal strip colourings*. URL: <https://oeis.org/A203981>.

*Commentary.*

The entries are in increasing order of the input index.

**Definition 1.10 (Monic polynomial coefficients).**

$$\forall n: \mathit{Nat}, (\operatorname{\mathit{HardinA203981StripCertificate}}.\operatorname{\mathit{monicCoeff}}\left(n\right) = (\operatorname{\mathit{if}} (h: n < 6) \operatorname{\mathit{then}} -\operatorname{\mathit{HardinA203981StripCertificate}}.\operatorname{\mathit{coeff}}\left((\langle n, h\rangle: \operatorname{\mathit{Fin}}\left(6\right))\right) \operatorname{\mathit{else}} (\operatorname{\mathit{if}} (n = 6) \operatorname{\mathit{then}} (1: \mathit{Int}) \operatorname{\mathit{else}} (0: \mathit{Int}))))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203981StripCertificate.monicCoeff` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2012). *OEIS A203981: canonical diagonal and antidiagonal strip colourings*. URL: <https://oeis.org/A203981>.

*Commentary.*

Below degree six, the polynomial coefficients are the negatives of the recurrence weights. The leading coefficient is one and all higher coefficients vanish.

**Theorem 1.11 (Forward vectors from adjacent updates).**

$$\forall X: \mathit{Type}, (\forall n: \mathit{Nat}, (\forall f: (X) \to (X), (\forall v: X, (\forall \mathit{table}: (\operatorname{\mathit{Fin}}\left(n + 1\right)) \to (X), (((\mathit{table}\left((0: \operatorname{\mathit{Fin}}\left(n + 1\right))\right) = v) \land ((\forall k: \operatorname{\mathit{Fin}}\left(n\right), (f\left(\mathit{table}\left(\operatorname{\mathit{Fin}}.\operatorname{\mathit{castSucc}}\left(k\right)\right)\right) = \mathit{table}\left(\operatorname{\mathit{Fin}}.\operatorname{\mathit{succ}}\left(k\right)\right))))) \implies (\forall i: \operatorname{\mathit{Fin}}\left(n + 1\right), (\operatorname{\mathit{Nat}}.\operatorname{\mathit{iterate}}\left(f, \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(i\right), v\right) = \mathit{table}\left(i\right))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203981StripCertificate.forward_table_of_steps` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2012). *OEIS A203981: canonical diagonal and antidiagonal strip colourings*. URL: <https://oeis.org/A203981>.

*Commentary.*

The list of table rows starts at the initial vector. Its adjacent update equations determine the forward vector at each index.

**Theorem 1.12 (Zero-degree table update).**

$$\forall k: \operatorname{\mathit{Fin}}\left(20\right), (\operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecMul}}\left(\operatorname{\mathit{HardinA203981StripCertificate}}.\operatorname{W}\left(\operatorname{\mathit{Fin}}.\operatorname{\mathit{castSucc}}\left(k\right)\right), \operatorname{\mathit{HardinA203981StripData}}.\operatorname{T}\right) = \operatorname{\mathit{HardinA203981StripCertificate}}.\operatorname{W}\left(\operatorname{\mathit{Fin}}.\operatorname{\mathit{succ}}\left(k\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203981StripCertificate.forward_step` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2012). *OEIS A203981: canonical diagonal and antidiagonal strip colourings*. URL: <https://oeis.org/A203981>.

*Commentary.*

The finite calculation checks the transfer on each adjacent pair of rows.

**Theorem 1.13 (Forward iteration agrees with the table).**

$$\forall i: \operatorname{\mathit{Fin}}\left(21\right), (\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{forward}}\left(\operatorname{\mathit{HardinA203981StripData}}.\operatorname{T}, \operatorname{\mathit{HardinA203981StripData}}.\operatorname{\mathit{initial}}, \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(i\right)\right) = \operatorname{\mathit{HardinA203981StripCertificate}}.\operatorname{W}\left(i\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203981StripCertificate.forward_table` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2012). *OEIS A203981: canonical diagonal and antidiagonal strip colourings*. URL: <https://oeis.org/A203981>.

*Commentary.*

The integer vectors are obtained from the initial vector by repeated right multiplication.

**Theorem 1.14 (The forward relation at exponent seven).**

$$\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{forward}}\left(\operatorname{\mathit{HardinA203981StripData}}.\operatorname{T}, \operatorname{\mathit{HardinA203981StripData}}.\operatorname{\mathit{initial}}, 1 + 6\right) = \sum_{j: \operatorname{\mathit{Fin}}\left(6\right)} (\operatorname{\mathit{SMul}}.\operatorname{\mathit{smul}}\left(\operatorname{\mathit{HardinA203981StripCertificate}}.\operatorname{\mathit{coeff}}\left(j\right), \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{forward}}\left(\operatorname{\mathit{HardinA203981StripData}}.\operatorname{T}, \operatorname{\mathit{HardinA203981StripData}}.\operatorname{\mathit{initial}}, 1 + \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(j\right)\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203981StripCertificate.finite_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2012). *OEIS A203981: canonical diagonal and antidiagonal strip colourings*. URL: <https://oeis.org/A203981>.

*Commentary.*

The entrywise relation follows from the tabulated forward vectors.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203981StripCertificate.W`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203981StripCertificate.allocated_counts`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203981StripCertificate.coeff`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203981StripCertificate.counts`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203981StripCertificate.finite_certificate`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203981StripCertificate.forward_step`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203981StripCertificate.forward_table`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203981StripCertificate.forward_table_of_steps`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203981StripCertificate.halfCost`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203981StripCertificate.halfForwardZero`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203981StripCertificate.initial_counts`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203981StripCertificate.monicCoeff`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203981StripCertificate.reversed_count`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203981StripCertificate.zero_exact`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233258PairTransfer](../../../Combinatorics/TraceAvoidingArrays/HardinA233258PairTransfer.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203981StripData](HardinA203981StripData.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203981StripSymmetry](HardinA203981StripSymmetry.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/DefectTransfer](../StripDefects/DefectTransfer.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229588Strip](../StripDefects/HardinA229588Strip.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229637RowColumn](../StripDefects/HardinA229637RowColumn.md)
