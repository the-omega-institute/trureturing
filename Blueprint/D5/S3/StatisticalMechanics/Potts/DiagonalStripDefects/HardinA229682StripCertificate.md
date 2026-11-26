# Five-column strip colourings

## Abstract

Exact-budget diagonal and antidiagonal arrays.

**Theorem 1.1 (two_counts).**

$$\forall p: (\operatorname{\mathit{Fin}}\left(5\right)) \to (\operatorname{\mathit{Fin}}\left(3\right)), (\forall j: \operatorname{\mathit{Fin}}\left(8\right), (\sum_{r: (\operatorname{\mathit{Fin}}\left(5\right)) \to (\operatorname{\mathit{Fin}}\left(3\right))} (((\operatorname{\mathit{if}} ((\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA203980StripData}}.\operatorname{\mathit{between}}, p, r\right) = 2) \land (\operatorname{\mathit{HardinA203980StripData}}.\operatorname{\mathit{boundary}}\left(r\right) = j)) \operatorname{\mathit{then}} 1 \operatorname{\mathit{else}} 0): \mathit{Int})) = \operatorname{\mathit{HardinA229682StripData}}.\operatorname{\mathit{costTwo}}\left(\operatorname{\mathit{HardinA203980StripData}}.\operatorname{\mathit{boundary}}\left(p\right), j\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229682StripCertificate.two_counts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229682: canonical diagonal and antidiagonal strip colourings*. URL: <https://oeis.org/A229682>.

*Commentary.*

Each sum counts actual labelled successor rows in the given target boundary class.

**Theorem 1.2 (transition_counts).**

$$\forall p: (\operatorname{\mathit{Fin}}\left(5\right)) \to (\operatorname{\mathit{Fin}}\left(3\right)), (\forall d: \operatorname{\mathit{Fin}}\left(3\right), (\forall j: \operatorname{\mathit{Fin}}\left(24\right), (\sum_{r: (\operatorname{\mathit{Fin}}\left(5\right)) \to (\operatorname{\mathit{Fin}}\left(3\right))} (((\operatorname{\mathit{if}} ((\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA203980StripData}}.\operatorname{\mathit{between}}, p, r\right) \le \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right)) \land (\operatorname{\mathit{HardinA229682StripData}}.\operatorname{\mathit{cl}}\left(r, \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right) - \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA203980StripData}}.\operatorname{\mathit{between}}, p, r\right)\right) = j)) \operatorname{\mathit{then}} 1 \operatorname{\mathit{else}} 0): \mathit{Int})) = \operatorname{\mathit{HardinA229682StripData}}.\operatorname{T}\left(\operatorname{\mathit{HardinA229682StripData}}.\operatorname{\mathit{cl}}\left(p, \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right)\right), j\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229682StripCertificate.transition_counts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229682: canonical diagonal and antidiagonal strip colourings*. URL: <https://oeis.org/A229682>.

*Commentary.*

Natural-number subtraction gives the remaining budget. The guard requires the bond cost to be at most the current budget. The lower-budget sectors use the preceding exact transition theorem.

**Definition 1.3 (W).**

$$(\operatorname{\mathit{HardinA229682StripCertificate}}.\operatorname{W}: (\operatorname{\mathit{Fin}}\left(14\right)) \to ((\operatorname{\mathit{Fin}}\left(24\right)) \to (\mathit{Int})))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229682StripCertificate.W` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229682: canonical diagonal and antidiagonal strip colourings*. URL: <https://oeis.org/A229682>.

*Commentary.*

The fourteen by 24 integer table appends a fourteen by eight leading table to HardinA229507StripCertificate.W. The powers theorem pins every row to the corresponding transfer power on the terminal vector.

**Theorem 1.4 (powers).**

$$\forall i: \operatorname{\mathit{Fin}}\left(14\right), (\operatorname{\mathit{Matrix}}.\operatorname{\mathit{mulVec}}\left(\operatorname{\mathit{HardinA229682StripData}}.\operatorname{T}^{\operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(i\right)}, \operatorname{\mathit{HardinA229682StripData}}.\operatorname{\mathit{terminal}}\right) = \operatorname{\mathit{HardinA229682StripCertificate}}.\operatorname{W}\left(i\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229682StripCertificate.powers` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229682: canonical diagonal and antidiagonal strip colourings*. URL: <https://oeis.org/A229682>.

*Commentary.*

Multiplication advances the added coordinates while the retained coordinates use the previous powers theorem.

**Theorem 1.5 (finite_certificate).**

$$\operatorname{\mathit{Matrix}}.\operatorname{\mathit{mulVec}}\left(\operatorname{\mathit{HardinA229682StripData}}.\operatorname{T}^{13}, \operatorname{\mathit{HardinA229682StripData}}.\operatorname{\mathit{terminal}}\right) = \sum_{k: \operatorname{\mathit{Fin}}\left(12\right)} (\operatorname{\mathit{HSMul}}.\operatorname{\mathit{hSMul}}\left(\operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(34012224, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left((-85030560), \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(70858800, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left((-14959080), \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left((-8188128), \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(3805380, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(0, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left((-211410), \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(25272, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(2565, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left((-675), \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(45, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecEmpty}}\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\left(k\right), \operatorname{\mathit{Matrix}}.\operatorname{\mathit{mulVec}}\left(\operatorname{\mathit{HardinA229682StripData}}.\operatorname{T}^{1 + \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(k\right)}, \operatorname{\mathit{HardinA229682StripData}}.\operatorname{\mathit{terminal}}\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229682StripCertificate.finite_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229682: canonical diagonal and antidiagonal strip colourings*. URL: <https://oeis.org/A229682>.

*Commentary.*

The eventual vector relation has order 12. The retained coordinates follow the preceding vector relation multiplied by the zero-cost quartic.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229682StripCertificate.W`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229682StripCertificate.finite_certificate`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229682StripCertificate.powers`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229682StripCertificate.transition_counts`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229682StripCertificate.two_counts`
- Dependency: [D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/DiagonalSymmetry](DiagonalSymmetry.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203980StripCertificate](HardinA203980StripCertificate.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203980StripData](HardinA203980StripData.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229507StripCertificate](HardinA229507StripCertificate.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229507StripData](HardinA229507StripData.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229682StripData](HardinA229682StripData.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/DefectTransfer](../StripDefects/DefectTransfer.md)
