# Finite checks for the order-twelve recurrence

## Abstract

Finite checks for the order-twelve recurrence

**Theorem 1.1 (Exact one-cost half-strip counts).**

$$\forall a: \operatorname{\mathit{HardinA233258PairTransfer}}.\operatorname{\mathit{Col}}, (\forall j: \operatorname{\mathit{Fin}}\left(5\right), (\sum_{b: \operatorname{\mathit{HardinA233258PairTransfer}}.\operatorname{\mathit{Col}}} ((\operatorname{\mathit{if}} ((\operatorname{\mathit{HardinA203981StripCertificate}}.\operatorname{\mathit{halfCost}}\left(a, b\right) = 1) \land (\operatorname{\mathit{HardinA233258PairTransfer}}.\operatorname{\mathit{cls}}\left(b\right) = j)) \operatorname{\mathit{then}} (1: \mathit{Int}) \operatorname{\mathit{else}} (0: \mathit{Int}))) = \operatorname{\mathit{HardinA229508StripData}}.\operatorname{\mathit{halfOne}}\left(\operatorname{\mathit{HardinA233258PairTransfer}}.\operatorname{\mathit{cls}}\left(a\right), j\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229508StripCertificate.one_exact` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229508: canonical diagonal and antidiagonal strip colourings*. URL: <https://oeis.org/A229508>.

*Commentary.*

The transition clause of HardinA229588Strip.finite_certificate at budget one gives the count into its terminal sector.

**Theorem 1.2 (Exact-one-cost class counts).**

$$\forall p: (\operatorname{\mathit{Fin}}\left(6\right)) \to (\operatorname{\mathit{Fin}}\left(3\right)), (\forall j: \operatorname{\mathit{Fin}}\left(15\right), (\sum_{r: (\operatorname{\mathit{Fin}}\left(6\right)) \to (\operatorname{\mathit{Fin}}\left(3\right))} ((\operatorname{\mathit{if}} ((\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229637RowColumn}}.\operatorname{\mathit{betw}}\left(6\right), p, r\right) = 1) \land (\operatorname{\mathit{HardinA203981StripData}}.\operatorname{\mathit{boundary}}\left(r\right) = j)) \operatorname{\mathit{then}} (1: \mathit{Int}) \operatorname{\mathit{else}} (0: \mathit{Int}))) = \operatorname{\mathit{HardinA229508StripData}}.\operatorname{\mathit{costOne}}\left(\operatorname{\mathit{HardinA203981StripData}}.\operatorname{\mathit{boundary}}\left(p\right), j\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229508StripCertificate.one_counts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229508: canonical diagonal and antidiagonal strip colourings*. URL: <https://oeis.org/A229508>.

*Commentary.*

The exact cost splits as zero plus one or one plus zero. Parity recolouring and reflection extend the representative counts to every source row.

**Theorem 1.3 (Exact remaining-budget transitions).**

$$\forall p: (\operatorname{\mathit{Fin}}\left(6\right)) \to (\operatorname{\mathit{Fin}}\left(3\right)), (\forall d: \operatorname{\mathit{Fin}}\left(2\right), (\forall s: \operatorname{\mathit{Sum}}\left(\operatorname{\mathit{Fin}}\left(15\right), \operatorname{\mathit{Fin}}\left(15\right)\right), (\sum_{r: (\operatorname{\mathit{Fin}}\left(6\right)) \to (\operatorname{\mathit{Fin}}\left(3\right))} ((\operatorname{\mathit{if}} ((\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229637RowColumn}}.\operatorname{\mathit{betw}}\left(6\right), p, r\right) \le \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right)) \land (\operatorname{\mathit{HardinA229508StripData}}.\operatorname{\mathit{cl}}\left(r, \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right) - \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229637RowColumn}}.\operatorname{\mathit{betw}}\left(6\right), p, r\right)\right) = s)) \operatorname{\mathit{then}} (1: \mathit{Int}) \operatorname{\mathit{else}} (0: \mathit{Int}))) = \operatorname{\mathit{HardinA229508StripData}}.\operatorname{T}\left(\operatorname{\mathit{HardinA229508StripData}}.\operatorname{\mathit{cl}}\left(p, \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right)\right), s\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229508StripCertificate.transition_counts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229508: canonical diagonal and antidiagonal strip colourings*. URL: <https://oeis.org/A229508>.

*Commentary.*

A step stays in its sector when it has no defects, or enters the second sector by spending one defect. Spending a defect beyond the budget contributes zero.

**Theorem 1.4 (Forward projection of an upper-block transfer).**

$$\forall (l: \mathit{Type}) (r: \mathit{Type}) (\mathit{alpha}: \mathit{Type}) [\operatorname{\mathit{Fintype}}\left(l\right)] [\operatorname{\mathit{Fintype}}\left(r\right)] [\operatorname{\mathit{NonUnitalNonAssocSemiring}}\left(\mathit{alpha}\right)], (\forall a: \operatorname{\mathit{Matrix}}\left(l, l, \mathit{alpha}\right), (\forall b: \operatorname{\mathit{Matrix}}\left(l, r, \mathit{alpha}\right), (\forall c: \operatorname{\mathit{Matrix}}\left(r, r, \mathit{alpha}\right), (\forall v: (\operatorname{\mathit{Sum}}\left(l, r\right)) \to (\mathit{alpha}), (\forall n: \mathit{Nat}, (\operatorname{\mathit{Function}}.\operatorname{\mathit{comp}}\left(\operatorname{\mathit{Nat}}.\operatorname{\mathit{iterate}}\left((\lambda w: (\operatorname{\mathit{Sum}}\left(l, r\right)) \to (\mathit{alpha}) \mapsto (\operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecMul}}\left(w, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{fromBlocks}}\left(a, b, (0: \operatorname{\mathit{Matrix}}\left(r, l, \mathit{alpha}\right)), c\right)\right))), n, v\right), (\operatorname{\mathit{Sum}}.\operatorname{\mathit{inl}}: (l) \to (\operatorname{\mathit{Sum}}\left(l, r\right)))\right) = \operatorname{\mathit{Nat}}.\operatorname{\mathit{iterate}}\left((\lambda w: (l) \to (\mathit{alpha}) \mapsto (\operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecMul}}\left(w, a\right))), n, \operatorname{\mathit{Function}}.\operatorname{\mathit{comp}}\left(v, (\operatorname{\mathit{Sum}}.\operatorname{\mathit{inl}}: (l) \to (\operatorname{\mathit{Sum}}\left(l, r\right)))\right)\right)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229508StripCertificate.block_projection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229508: canonical diagonal and antidiagonal strip colourings*. URL: <https://oeis.org/A229508>.

*Commentary.*

The finite enumerations and semiring operations define the matrix-vector sums. The zero lower-left block makes left projection commute with one step, and iteration preserves that identity.

**Theorem 1.5 (Reuse of the zero-cost iteration).**

$$\forall n: \mathit{Nat}, (\operatorname{\mathit{Function}}.\operatorname{\mathit{comp}}\left(\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{forward}}\left(\operatorname{\mathit{HardinA229508StripData}}.\operatorname{T}, \operatorname{\mathit{HardinA229508StripData}}.\operatorname{\mathit{initial}}, n\right), \operatorname{\mathit{Sum}}.\operatorname{\mathit{inl}}\right) = \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{forward}}\left(\operatorname{\mathit{HardinA203981StripData}}.\operatorname{T}, \operatorname{\mathit{HardinA203981StripData}}.\operatorname{\mathit{initial}}, n\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229508StripCertificate.forward_zeroth` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229508: canonical diagonal and antidiagonal strip colourings*. URL: <https://oeis.org/A229508>.

*Commentary.*

The upper-block projection specializes to the first sector, whose transition matrix is the zero-cost matrix.

**Definition 1.6 (The half-strip forward vectors in degree 1).**

$$(\operatorname{\mathit{HardinA229508StripCertificate}}.\operatorname{\mathit{halfForwardOne}}: (\operatorname{\mathit{Fin}}\left(21\right)) \to ((\operatorname{\mathit{Fin}}\left(5\right)) \to (\mathit{Int})))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229508StripCertificate.halfForwardOne` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229508: canonical diagonal and antidiagonal strip colourings*. URL: <https://oeis.org/A229508>.

*Commentary.*

The 21 by 5 integer table begins with the zero vector and the final five coordinates of HardinA229588Strip.W at exponent one. Exponent two uses the final five coordinates of the same frozen row at exponent two, with classes 1 and 3 exchanged. The later rows are tabulated half-strip samples. The unordered products are checked against the full-strip update in HardinA229508StripCertificate.forward_one.

**Definition 1.7 (Forward vectors in total cost degree 1).**

$$\forall i: \operatorname{\mathit{Fin}}\left(21\right), (\forall j: \operatorname{\mathit{Fin}}\left(15\right), (\operatorname{\mathit{HardinA229508StripCertificate}}.\operatorname{W}\left(i, j\right) = \operatorname{\mathit{HardinA203981StripData}}.\operatorname{\mathit{unordered}}\left(\operatorname{\mathit{HardinA203981StripCertificate}}.\operatorname{\mathit{halfForwardZero}}\left(i\right), \operatorname{\mathit{HardinA229508StripCertificate}}.\operatorname{\mathit{halfForwardOne}}\left(i\right), j\right) + \operatorname{\mathit{HardinA203981StripData}}.\operatorname{\mathit{unordered}}\left(\operatorname{\mathit{HardinA229508StripCertificate}}.\operatorname{\mathit{halfForwardOne}}\left(i\right), \operatorname{\mathit{HardinA203981StripCertificate}}.\operatorname{\mathit{halfForwardZero}}\left(i\right), j\right)))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229508StripCertificate.W` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229508: canonical diagonal and antidiagonal strip colourings*. URL: <https://oeis.org/A229508>.

*Commentary.*

The degree-zero and degree-one half-strip vectors contribute in both orders at each exponent through twenty.

**Definition 1.8 (Squared monic polynomial coefficients).**

$$\forall n: \mathit{Nat}, (\operatorname{\mathit{HardinA229508StripCertificate}}.\operatorname{\mathit{squareMonicCoeff}}\left(n\right) = \sum_{p \in \operatorname{\mathit{Finset}}.\operatorname{\mathit{HasAntidiagonal}}.\operatorname{\mathit{antidiagonal}}\left(n\right)} (\operatorname{\mathit{HardinA203981StripCertificate}}.\operatorname{\mathit{monicCoeff}}\left(\operatorname{\mathit{Prod}}.\operatorname{\mathit{fst}}\left(p\right)\right) \cdot \operatorname{\mathit{HardinA203981StripCertificate}}.\operatorname{\mathit{monicCoeff}}\left(\operatorname{\mathit{Prod}}.\operatorname{\mathit{snd}}\left(p\right)\right)))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229508StripCertificate.squareMonicCoeff` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229508: canonical diagonal and antidiagonal strip colourings*. URL: <https://oeis.org/A229508>.

*Commentary.*

The antidiagonal lists pairs of nonnegative exponents whose sum is the output exponent.

**Definition 1.9 (Order-twelve coefficients).**

$$\forall k: \operatorname{\mathit{Fin}}\left(12\right), (\operatorname{\mathit{HardinA229508StripCertificate}}.\operatorname{\mathit{coeff}}\left(k\right) = -\operatorname{\mathit{HardinA229508StripCertificate}}.\operatorname{\mathit{squareMonicCoeff}}\left(\operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(k\right)\right))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229508StripCertificate.coeff` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229508: canonical diagonal and antidiagonal strip colourings*. URL: <https://oeis.org/A229508>.

*Commentary.*

The recurrence weights are the negatives of the coefficients below degree 12 in the square of the order-six monic polynomial.

**Theorem 1.10 (Numerical expansion).**

$$(\operatorname{\mathit{HardinA229508StripCertificate}}.\operatorname{\mathit{coeff}}: (\operatorname{\mathit{Fin}}\left(12\right)) \to (\mathit{Int})) = [-43046721, 47829690, 13286025, -27398736, 2329155, 4556250, -940491, -180630, 50175, 324, -715, 50]$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229508StripCertificate.coeff_values` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229508: canonical diagonal and antidiagonal strip colourings*. URL: <https://oeis.org/A229508>.

*Commentary.*

The coefficients are listed in increasing order of input index.

**Theorem 1.11 (Update on both sectors).**

$$\forall k: \operatorname{\mathit{Fin}}\left(20\right), (\operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecMul}}\left(\operatorname{\mathit{Sum}}.\operatorname{\mathit{elim}}\left(\operatorname{\mathit{HardinA203981StripCertificate}}.\operatorname{W}\left(\operatorname{\mathit{Fin}}.\operatorname{\mathit{castSucc}}\left(k\right)\right), \operatorname{\mathit{HardinA229508StripCertificate}}.\operatorname{W}\left(\operatorname{\mathit{Fin}}.\operatorname{\mathit{castSucc}}\left(k\right)\right)\right), \operatorname{\mathit{HardinA229508StripData}}.\operatorname{T}\right) = \operatorname{\mathit{Sum}}.\operatorname{\mathit{elim}}\left(\operatorname{\mathit{HardinA203981StripCertificate}}.\operatorname{W}\left(\operatorname{\mathit{Fin}}.\operatorname{\mathit{succ}}\left(k\right)\right), \operatorname{\mathit{HardinA229508StripCertificate}}.\operatorname{W}\left(\operatorname{\mathit{Fin}}.\operatorname{\mathit{succ}}\left(k\right)\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229508StripCertificate.forward_step` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229508: canonical diagonal and antidiagonal strip colourings*. URL: <https://oeis.org/A229508>.

*Commentary.*

The left component uses the zero-degree update. The right component adds the incoming degree-one transitions to the degree-zero transfers within that sector.

**Theorem 1.12 (Second-sector forward vectors).**

$$\forall i: \operatorname{\mathit{Fin}}\left(21\right), (\operatorname{\mathit{Function}}.\operatorname{\mathit{comp}}\left(\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{forward}}\left(\operatorname{\mathit{HardinA229508StripData}}.\operatorname{T}, \operatorname{\mathit{HardinA229508StripData}}.\operatorname{\mathit{initial}}, \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(i\right)\right), \operatorname{\mathit{Sum}}.\operatorname{\mathit{inr}}\right) = \operatorname{\mathit{HardinA229508StripCertificate}}.\operatorname{W}\left(i\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229508StripCertificate.forward_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229508: canonical diagonal and antidiagonal strip colourings*. URL: <https://oeis.org/A229508>.

*Commentary.*

Each update combines transitions with one new defect from the first sector and zero new defects from the second.

**Theorem 1.13 (A shifted forward relation in one coordinate).**

$$\forall (s: \mathit{Type}) [\operatorname{\mathit{Fintype}}\left(s\right)], (\forall t: \operatorname{\mathit{Matrix}}\left(s, s, \mathit{Int}\right), (\forall v: (s) \to (\mathit{Int}), (\forall d: \mathit{Nat}, (\forall b: \mathit{Nat}, (\forall c: (\operatorname{\mathit{Fin}}\left(d\right)) \to (\mathit{Int}), ((\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{forward}}\left(t, v, b + d\right) = \sum_{k: \operatorname{\mathit{Fin}}\left(d\right)} (\operatorname{\mathit{SMul}}.\operatorname{\mathit{smul}}\left(c\left(k\right), \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{forward}}\left(t, v, b + \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(k\right)\right)\right))) \to (\forall n: \mathit{Nat}, (\forall j: s, (\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{forward}}\left(t, v, n + b + d\right)\left(j\right) = \sum_{k: \operatorname{\mathit{Fin}}\left(d\right)} (c\left(k\right) \cdot \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{forward}}\left(t, v, n + b + \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(k\right)\right)\left(j\right)))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229508StripCertificate.shifted_coordinate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229508: canonical diagonal and antidiagonal strip colourings*. URL: <https://oeis.org/A229508>.

*Commentary.*

The finite enumeration defines the matrix-vector sums. Taking the terminal vector equal to one at the selected coordinate and zero elsewhere reads that coordinate from the shifted relation.

**Theorem 1.14 (Forward relation at exponent thirteen).**

$$\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{forward}}\left(\operatorname{\mathit{HardinA229508StripData}}.\operatorname{T}, \operatorname{\mathit{HardinA229508StripData}}.\operatorname{\mathit{initial}}, 1 + 12\right) = \sum_{k: \operatorname{\mathit{Fin}}\left(12\right)} (\operatorname{\mathit{SMul}}.\operatorname{\mathit{smul}}\left(\operatorname{\mathit{HardinA229508StripCertificate}}.\operatorname{\mathit{coeff}}\left(k\right), \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{forward}}\left(\operatorname{\mathit{HardinA229508StripData}}.\operatorname{T}, \operatorname{\mathit{HardinA229508StripData}}.\operatorname{\mathit{initial}}, 1 + \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(k\right)\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229508StripCertificate.finite_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229508: canonical diagonal and antidiagonal strip colourings*. URL: <https://oeis.org/A229508>.

*Commentary.*

Seven applications of the coordinate shift to the order-six relation give the inherited sector relation. The other sector follows from the tabulated update.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229508StripCertificate.W`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229508StripCertificate.block_projection`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229508StripCertificate.coeff`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229508StripCertificate.coeff_values`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229508StripCertificate.finite_certificate`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229508StripCertificate.forward_one`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229508StripCertificate.forward_step`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229508StripCertificate.forward_zeroth`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229508StripCertificate.halfForwardOne`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229508StripCertificate.one_counts`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229508StripCertificate.one_exact`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229508StripCertificate.shifted_coordinate`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229508StripCertificate.squareMonicCoeff`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229508StripCertificate.transition_counts`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233258PairTransfer](../../../Combinatorics/TraceAvoidingArrays/HardinA233258PairTransfer.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203981StripCertificate](HardinA203981StripCertificate.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203981StripData](HardinA203981StripData.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203981StripSymmetry](HardinA203981StripSymmetry.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229508StripData](HardinA229508StripData.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/DefectTransfer](../StripDefects/DefectTransfer.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229588Strip](../StripDefects/HardinA229588Strip.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229637RowColumn](../StripDefects/HardinA229637RowColumn.md)
