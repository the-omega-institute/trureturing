# Diagonal strip transfer

## Abstract

Exact diagonal-strip transfer identities.

**Theorem 1.1 (counts).**

$$\forall p: (\operatorname{\mathit{Fin}}\left(5\right)) \to (\operatorname{\mathit{Fin}}\left(3\right)), (\forall j: \operatorname{\mathit{Fin}}\left(8\right), (\sum_{r: (\operatorname{\mathit{Fin}}\left(5\right)) \to (\operatorname{\mathit{Fin}}\left(3\right))} (((\operatorname{\mathit{if}} ((\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA203980StripData}}.\operatorname{\mathit{between}}, p, r\right) = 0) \land (\operatorname{\mathit{HardinA203980StripData}}.\operatorname{\mathit{boundary}}\left(r\right) = j)) \operatorname{\mathit{then}} 1 \operatorname{\mathit{else}} 0): \mathit{Int})) = \operatorname{\mathit{HardinA203980StripData}}.\operatorname{T}\left(\operatorname{\mathit{HardinA203980StripData}}.\operatorname{\mathit{boundary}}\left(p\right), j\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203980StripCertificate.counts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2012). *OEIS A203980: canonical diagonal and antidiagonal strip colourings*. URL: <https://oeis.org/A203980>.

*Commentary.*

For each labelled row and each target class, the successor sum is the corresponding transfer entry. Parity-wise colour permutations and reflection reduce the source to one of eight representatives.

**Theorem 1.2 (initial_counts).**

$$\forall j: \operatorname{\mathit{Fin}}\left(8\right), (\sum_{r: (\operatorname{\mathit{Fin}}\left(5\right)) \to (\operatorname{\mathit{Fin}}\left(3\right))} (((\operatorname{\mathit{if}} (\operatorname{\mathit{HardinA203980StripData}}.\operatorname{\mathit{boundary}}\left(r\right) = j) \operatorname{\mathit{then}} 1 \operatorname{\mathit{else}} 0): \mathit{Int})) = \operatorname{\mathit{HardinA203980StripData}}.\operatorname{\mathit{initial}}\left(j\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203980StripCertificate.initial_counts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2012). *OEIS A203980: canonical diagonal and antidiagonal strip colourings*. URL: <https://oeis.org/A203980>.

*Commentary.*

The sum counts the first rows in each class.

**Definition 1.3 (W).**

$$(\operatorname{\mathit{HardinA203980StripCertificate}}.\operatorname{W}: (\operatorname{\mathit{Fin}}\left(14\right)) \to ((\operatorname{\mathit{Fin}}\left(8\right)) \to (\mathit{Int})))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203980StripCertificate.W` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2012). *OEIS A203980: canonical diagonal and antidiagonal strip colourings*. URL: <https://oeis.org/A203980>.

*Commentary.*

The fourteen by eight integer table records the zero-cost transfer powers on the all-one vector. HardinA203980StripCertificate.powers pins every coordinate.

**Theorem 1.4 (powers).**

$$\forall i: \operatorname{\mathit{Fin}}\left(14\right), (\operatorname{\mathit{Matrix}}.\operatorname{\mathit{mulVec}}\left(\operatorname{\mathit{HardinA203980StripData}}.\operatorname{T}^{\operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(i\right)}, \operatorname{\mathit{HardinA203980StripData}}.\operatorname{\mathit{terminal}}\right) = \operatorname{\mathit{HardinA203980StripCertificate}}.\operatorname{W}\left(i\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203980StripCertificate.powers` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2012). *OEIS A203980: canonical diagonal and antidiagonal strip colourings*. URL: <https://oeis.org/A203980>.

*Commentary.*

Every table row is the corresponding transfer power on the terminal vector.

**Theorem 1.5 (finite_certificate).**

$$\operatorname{\mathit{Matrix}}.\operatorname{\mathit{mulVec}}\left(\operatorname{\mathit{HardinA203980StripData}}.\operatorname{T}^{5}, \operatorname{\mathit{HardinA203980StripData}}.\operatorname{\mathit{terminal}}\right) = \sum_{j: \operatorname{\mathit{Fin}}\left(4\right)} (\operatorname{\mathit{HSMul}}.\operatorname{\mathit{hSMul}}\left(\operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(324, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left((-270), \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(0, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(15, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecEmpty}}\right)\right)\right)\right)\left(j\right), \operatorname{\mathit{Matrix}}.\operatorname{\mathit{mulVec}}\left(\operatorname{\mathit{HardinA203980StripData}}.\operatorname{T}^{1 + \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(j\right)}, \operatorname{\mathit{HardinA203980StripData}}.\operatorname{\mathit{terminal}}\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203980StripCertificate.finite_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2012). *OEIS A203980: canonical diagonal and antidiagonal strip colourings*. URL: <https://oeis.org/A203980>.

*Commentary.*

The fifth power vector is 324 times the first, minus 270 times the second, plus 15 times the fourth.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203980StripCertificate.W`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203980StripCertificate.counts`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203980StripCertificate.finite_certificate`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203980StripCertificate.initial_counts`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203980StripCertificate.powers`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/TransferMatrix](../../../Combinatorics/TraceAvoidingArrays/TransferMatrix.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/DiagonalSymmetry](DiagonalSymmetry.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203980StripData](HardinA203980StripData.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/DefectTransfer](../StripDefects/DefectTransfer.md)
