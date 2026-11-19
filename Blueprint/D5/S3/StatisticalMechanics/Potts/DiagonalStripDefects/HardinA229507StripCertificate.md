# Five-column strip colourings

## Abstract

Exact-budget diagonal and antidiagonal arrays.

**Theorem 1.1 (one_counts).**

$$\forall p: (\operatorname{\mathit{Fin}}\left(5\right)) \to (\operatorname{\mathit{Fin}}\left(3\right)), (\forall j: \operatorname{\mathit{Fin}}\left(8\right), (\sum_{r: (\operatorname{\mathit{Fin}}\left(5\right)) \to (\operatorname{\mathit{Fin}}\left(3\right))} (((\operatorname{\mathit{if}} ((\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA203980StripData}}.\operatorname{\mathit{between}}, p, r\right) = 1) \land (\operatorname{\mathit{HardinA203980StripData}}.\operatorname{\mathit{boundary}}\left(r\right) = j)) \operatorname{\mathit{then}} 1 \operatorname{\mathit{else}} 0): \mathit{Int})) = \operatorname{\mathit{HardinA229507StripData}}.\operatorname{\mathit{costOne}}\left(\operatorname{\mathit{HardinA203980StripData}}.\operatorname{\mathit{boundary}}\left(p\right), j\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229507StripCertificate.one_counts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229507: canonical diagonal and antidiagonal strip colourings*. URL: <https://oeis.org/A229507>.

*Commentary.*

Each sum counts actual labelled successor rows in the given target boundary class.

**Theorem 1.2 (transition_counts).**

$$\forall p: (\operatorname{\mathit{Fin}}\left(5\right)) \to (\operatorname{\mathit{Fin}}\left(3\right)), (\forall d: \operatorname{\mathit{Fin}}\left(2\right), (\forall j: \operatorname{\mathit{Fin}}\left(16\right), (\sum_{r: (\operatorname{\mathit{Fin}}\left(5\right)) \to (\operatorname{\mathit{Fin}}\left(3\right))} (((\operatorname{\mathit{if}} ((\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA203980StripData}}.\operatorname{\mathit{between}}, p, r\right) \le \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right)) \land (\operatorname{\mathit{HardinA229507StripData}}.\operatorname{\mathit{cl}}\left(r, \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right) - \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA203980StripData}}.\operatorname{\mathit{between}}, p, r\right)\right) = j)) \operatorname{\mathit{then}} 1 \operatorname{\mathit{else}} 0): \mathit{Int})) = \operatorname{\mathit{HardinA229507StripData}}.\operatorname{T}\left(\operatorname{\mathit{HardinA229507StripData}}.\operatorname{\mathit{cl}}\left(p, \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right)\right), j\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229507StripCertificate.transition_counts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229507: canonical diagonal and antidiagonal strip colourings*. URL: <https://oeis.org/A229507>.

*Commentary.*

Natural-number subtraction gives the remaining budget. The guard requires the bond cost to be at most the current budget. The lower-budget sectors use the preceding exact transition theorem.

**Definition 1.3 (W).**

$$(\operatorname{\mathit{HardinA229507StripCertificate}}.\operatorname{W}: (\operatorname{\mathit{Fin}}\left(14\right)) \to ((\operatorname{\mathit{Fin}}\left(16\right)) \to (\mathit{Int})))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229507StripCertificate.W` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229507: canonical diagonal and antidiagonal strip colourings*. URL: <https://oeis.org/A229507>.

*Commentary.*

The fourteen by 16 integer table appends a fourteen by eight leading table to HardinA203980StripCertificate.W. The powers theorem pins every row to the corresponding transfer power on the terminal vector.

**Theorem 1.4 (powers).**

$$\forall i: \operatorname{\mathit{Fin}}\left(14\right), (\operatorname{\mathit{Matrix}}.\operatorname{\mathit{mulVec}}\left(\operatorname{\mathit{HardinA229507StripData}}.\operatorname{T}^{\operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(i\right)}, \operatorname{\mathit{HardinA229507StripData}}.\operatorname{\mathit{terminal}}\right) = \operatorname{\mathit{HardinA229507StripCertificate}}.\operatorname{W}\left(i\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229507StripCertificate.powers` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229507: canonical diagonal and antidiagonal strip colourings*. URL: <https://oeis.org/A229507>.

*Commentary.*

Multiplication advances the added coordinates while the retained coordinates use the previous powers theorem.

**Theorem 1.5 (finite_certificate).**

$$\operatorname{\mathit{Matrix}}.\operatorname{\mathit{mulVec}}\left(\operatorname{\mathit{HardinA229507StripData}}.\operatorname{T}^{9}, \operatorname{\mathit{HardinA229507StripData}}.\operatorname{\mathit{terminal}}\right) = \sum_{k: \operatorname{\mathit{Fin}}\left(8\right)} (\operatorname{\mathit{HSMul}}.\operatorname{\mathit{hSMul}}\left(\operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left((-104976), \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(174960, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left((-72900), \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left((-9720), \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(8748, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left((-540), \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left((-225), \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(30, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecEmpty}}\right)\right)\right)\right)\right)\right)\right)\right)\left(k\right), \operatorname{\mathit{Matrix}}.\operatorname{\mathit{mulVec}}\left(\operatorname{\mathit{HardinA229507StripData}}.\operatorname{T}^{1 + \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(k\right)}, \operatorname{\mathit{HardinA229507StripData}}.\operatorname{\mathit{terminal}}\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229507StripCertificate.finite_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229507: canonical diagonal and antidiagonal strip colourings*. URL: <https://oeis.org/A229507>.

*Commentary.*

The eventual vector relation has order 8. The retained coordinates follow the preceding vector relation multiplied by the zero-cost quartic.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229507StripCertificate.W`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229507StripCertificate.finite_certificate`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229507StripCertificate.one_counts`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229507StripCertificate.powers`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229507StripCertificate.transition_counts`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/TransferMatrix](../../../Combinatorics/TraceAvoidingArrays/TransferMatrix.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/DiagonalSymmetry](DiagonalSymmetry.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203980StripCertificate](HardinA203980StripCertificate.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203980StripData](HardinA203980StripData.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229507StripData](HardinA229507StripData.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/DefectTransfer](../StripDefects/DefectTransfer.md)
