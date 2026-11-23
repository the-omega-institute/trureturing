# Finite checks for the order-eighteen recurrence

## Abstract

Finite checks for the order-eighteen recurrence

**Theorem 1.1 (Exact-two-cost class counts).**

$$\forall p: (\operatorname{\mathit{Fin}}\left(6\right)) \to (\operatorname{\mathit{Fin}}\left(3\right)), (\forall j: \operatorname{\mathit{Fin}}\left(15\right), (\sum_{r: (\operatorname{\mathit{Fin}}\left(6\right)) \to (\operatorname{\mathit{Fin}}\left(3\right))} ((\operatorname{\mathit{if}} ((\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229637RowColumn}}.\operatorname{\mathit{betw}}\left(6\right), p, r\right) = 2) \land (\operatorname{\mathit{HardinA203981StripData}}.\operatorname{\mathit{boundary}}\left(r\right) = j)) \operatorname{\mathit{then}} (1: \mathit{Int}) \operatorname{\mathit{else}} (0: \mathit{Int}))) = \operatorname{\mathit{HardinA229683StripData}}.\operatorname{\mathit{costTwo}}\left(\operatorname{\mathit{HardinA203981StripData}}.\operatorname{\mathit{boundary}}\left(p\right), j\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229683StripCertificate.two_counts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229683: canonical diagonal and antidiagonal strip colourings*. URL: <https://oeis.org/A229683>.

*Commentary.*

The exact cost splits as zero plus two, one plus one, or two plus zero. The half-strip counts use HardinA229696Strip.finite_certificate at budget two and the lower-budget laws. Parity symmetries extend the representative counts to every source row.

**Theorem 1.2 (Exact remaining-budget transitions).**

$$\forall p: (\operatorname{\mathit{Fin}}\left(6\right)) \to (\operatorname{\mathit{Fin}}\left(3\right)), (\forall d: \operatorname{\mathit{Fin}}\left(3\right), (\forall s: \operatorname{\mathit{Sum}}\left(\operatorname{\mathit{Sum}}\left(\operatorname{\mathit{Fin}}\left(15\right), \operatorname{\mathit{Fin}}\left(15\right)\right), \operatorname{\mathit{Fin}}\left(15\right)\right), (\sum_{r: (\operatorname{\mathit{Fin}}\left(6\right)) \to (\operatorname{\mathit{Fin}}\left(3\right))} ((\operatorname{\mathit{if}} ((\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229637RowColumn}}.\operatorname{\mathit{betw}}\left(6\right), p, r\right) \le \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right)) \land (\operatorname{\mathit{HardinA229683StripData}}.\operatorname{\mathit{cl}}\left(r, \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right) - \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229637RowColumn}}.\operatorname{\mathit{betw}}\left(6\right), p, r\right)\right) = s)) \operatorname{\mathit{then}} (1: \mathit{Int}) \operatorname{\mathit{else}} (0: \mathit{Int}))) = \operatorname{\mathit{HardinA229683StripData}}.\operatorname{T}\left(\operatorname{\mathit{HardinA229683StripData}}.\operatorname{\mathit{cl}}\left(p, \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right)\right), s\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229683StripCertificate.transition_counts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229683: canonical diagonal and antidiagonal strip colourings*. URL: <https://oeis.org/A229683>.

*Commentary.*

A transition within the inherited block uses its earlier count. A step to the last sector spends the full remaining budget.

**Theorem 1.3 (Forward vectors in the first two sectors).**

$$\forall n: \mathit{Nat}, (\operatorname{\mathit{Function}}.\operatorname{\mathit{comp}}\left(\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{forward}}\left(\operatorname{\mathit{HardinA229683StripData}}.\operatorname{T}, \operatorname{\mathit{HardinA229683StripData}}.\operatorname{\mathit{initial}}, n\right), \operatorname{\mathit{Sum}}.\operatorname{\mathit{inl}}\right) = \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{forward}}\left(\operatorname{\mathit{HardinA229508StripData}}.\operatorname{T}, \operatorname{\mathit{HardinA229508StripData}}.\operatorname{\mathit{initial}}, n\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229683StripCertificate.forward_inherited` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229683: canonical diagonal and antidiagonal strip colourings*. URL: <https://oeis.org/A229683>.

*Commentary.*

The upper-block projection gives the one-budget transfer on the first two sectors.

**Definition 1.4 (Forward vectors in total cost degree 2).**

$$\forall i: \operatorname{\mathit{Fin}}\left(21\right), (\forall j: \operatorname{\mathit{Fin}}\left(15\right), (\operatorname{\mathit{HardinA229683StripCertificate}}.\operatorname{W}\left(i, j\right) = \operatorname{\mathit{Function}}.\operatorname{\mathit{comp}}\left(\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{forward}}\left(\operatorname{\mathit{HardinA229683StripData}}.\operatorname{T}, \operatorname{\mathit{HardinA229683StripData}}.\operatorname{\mathit{initial}}, \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(i\right)\right), \operatorname{\mathit{Sum}}.\operatorname{\mathit{inr}}\right)\left(j\right)))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229683StripCertificate.W` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229683: canonical diagonal and antidiagonal strip colourings*. URL: <https://oeis.org/A229683>.

*Commentary.*

The degree-two vector is the sum of the unordered products for half-strip degrees zero and two, one and one, and two and zero. Each unordered product reads a single target coordinate, counting both orders when its classes differ. The degree-two half-strip table starts at zero and uses the last five coordinates of HardinA229696StripData.W for exponents one and two, with classes 1 and 3 exchanged at exponent two. The theorem forward_two pins the entries against the three-sector update.

**Definition 1.5 (Order-eighteen coefficients).**

$$\forall k: \operatorname{\mathit{Fin}}\left(18\right), (\operatorname{\mathit{HardinA229683StripCertificate}}.\operatorname{\mathit{coeff}}\left(k\right) = -(\sum_{p \in \operatorname{\mathit{Finset}}.\operatorname{\mathit{HasAntidiagonal}}.\operatorname{\mathit{antidiagonal}}\left(\operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(k\right)\right)} (\operatorname{\mathit{HardinA229508StripCertificate}}.\operatorname{\mathit{squareMonicCoeff}}\left(\operatorname{\mathit{Prod}}.\operatorname{\mathit{fst}}\left(p\right)\right) \cdot \operatorname{\mathit{HardinA203981StripCertificate}}.\operatorname{\mathit{monicCoeff}}\left(\operatorname{\mathit{Prod}}.\operatorname{\mathit{snd}}\left(p\right)\right))))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229683StripCertificate.coeff` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229683: canonical diagonal and antidiagonal strip colourings*. URL: <https://oeis.org/A229683>.

*Commentary.*

The recurrence weights are the negatives of the coefficients below degree 18 in the cube of the order-six monic polynomial.

**Theorem 1.6 (Numerical expansion).**

$$(\operatorname{\mathit{HardinA229683StripCertificate}}.\operatorname{\mathit{coeff}}: (\operatorname{\mathit{Fin}}\left(18\right)) \to (\mathit{Int})) = [-282429536481, 470715894135, 0, -366499782594, 132368667075, 92909172825, -54520532190, -6257717775, 8082823950, -601275555, -435322350, 70536825, 7404210, -2206575, 60075, 19486, -2010, 75]$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229683StripCertificate.coeff_values` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229683: canonical diagonal and antidiagonal strip colourings*. URL: <https://oeis.org/A229683>.

*Commentary.*

The entries are in increasing order of input index. The zero coefficient is at lag sixteen.

**Theorem 1.7 (Last-sector forward vectors).**

$$\forall i: \operatorname{\mathit{Fin}}\left(21\right), (\operatorname{\mathit{Function}}.\operatorname{\mathit{comp}}\left(\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{forward}}\left(\operatorname{\mathit{HardinA229683StripData}}.\operatorname{T}, \operatorname{\mathit{HardinA229683StripData}}.\operatorname{\mathit{initial}}, \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(i\right)\right), \operatorname{\mathit{Sum}}.\operatorname{\mathit{inr}}\right) = \operatorname{\mathit{HardinA229683StripCertificate}}.\operatorname{W}\left(i\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229683StripCertificate.forward_two` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229683: canonical diagonal and antidiagonal strip colourings*. URL: <https://oeis.org/A229683>.

*Commentary.*

Each update sums exact-two, exact-one and exact-zero transitions from the three sectors.

**Theorem 1.8 (Forward relation at exponent twenty).**

$$\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{forward}}\left(\operatorname{\mathit{HardinA229683StripData}}.\operatorname{T}, \operatorname{\mathit{HardinA229683StripData}}.\operatorname{\mathit{initial}}, 2 + 18\right) = \sum_{k: \operatorname{\mathit{Fin}}\left(18\right)} (\operatorname{\mathit{HSMul}}.\operatorname{\mathit{hSMul}}\left(\operatorname{\mathit{HardinA229683StripCertificate}}.\operatorname{\mathit{coeff}}\left(k\right), \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{forward}}\left(\operatorname{\mathit{HardinA229683StripData}}.\operatorname{T}, \operatorname{\mathit{HardinA229683StripData}}.\operatorname{\mathit{initial}}, 2 + \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(k\right)\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229683StripCertificate.finite_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229683: canonical diagonal and antidiagonal strip colourings*. URL: <https://oeis.org/A229683>.

*Commentary.*

Seven coordinate shifts of the order-twelve relation give the relation on the first two sectors. The last sector follows from the tabulated update.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229683StripCertificate.W`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229683StripCertificate.coeff`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229683StripCertificate.coeff_values`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229683StripCertificate.finite_certificate`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229683StripCertificate.forward_inherited`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229683StripCertificate.forward_two`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229683StripCertificate.transition_counts`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229683StripCertificate.two_counts`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233258PairTransfer](../../../Combinatorics/TraceAvoidingArrays/HardinA233258PairTransfer.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203981StripCertificate](HardinA203981StripCertificate.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203981StripData](HardinA203981StripData.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203981StripSymmetry](HardinA203981StripSymmetry.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229508StripCertificate](HardinA229508StripCertificate.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229508StripData](HardinA229508StripData.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229683StripData](HardinA229683StripData.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/DefectTransfer](../StripDefects/DefectTransfer.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229588Strip](../StripDefects/HardinA229588Strip.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229637RowColumn](../StripDefects/HardinA229637RowColumn.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefectsTwo/HardinA229696Strip](../StripDefectsTwo/HardinA229696Strip.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefectsTwo/HardinA229696StripData](../StripDefectsTwo/HardinA229696StripData.md)
