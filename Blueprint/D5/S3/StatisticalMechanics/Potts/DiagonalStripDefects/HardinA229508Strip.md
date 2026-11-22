# Canonical six-column one-defect arrays

## Abstract

Canonical six-column one-defect arrays

**Definition 1.1 (Literal row-major canonical count).**

$$\forall n: \mathit{Nat}, (\operatorname{\mathit{HardinA229508Strip}}.\operatorname{a}\left(n\right) = \operatorname{\mathit{Finset}}.\operatorname{\mathit{card}}\left(\operatorname{\mathit{Finset}}.\operatorname{\mathit{filter}}\left(\lambda f: ((\operatorname{\mathit{Fin}}\left(n\right)) \times (\operatorname{\mathit{Fin}}\left(6\right))) \to (\operatorname{\mathit{Fin}}\left(3\right)) \mapsto ((\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{defects}}\left(\operatorname{\mathit{Finset}}.\operatorname{\mathit{empty}}, \operatorname{\mathit{HardinA229637RowColumn}}.\operatorname{\mathit{betw}}\left(6\right), \operatorname{\mathit{List}}.\operatorname{\mathit{ofFn}}\left(\lambda i: \operatorname{\mathit{Fin}}\left(n\right) \mapsto (\lambda j: \operatorname{\mathit{Fin}}\left(6\right) \mapsto (f\left((i, j)\right)))\right)\right) = 1) \land (\forall p: (\operatorname{\mathit{Fin}}\left(n\right)) \times (\operatorname{\mathit{Fin}}\left(6\right)), (\forall c: \operatorname{\mathit{Fin}}\left(3\right), ((c < f\left(p\right)) \implies (\exists q: (\operatorname{\mathit{Fin}}\left(n\right)) \times (\operatorname{\mathit{Fin}}\left(6\right)), ((6 \cdot \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(\operatorname{\mathit{Prod}}.\operatorname{\mathit{fst}}\left(q\right)\right) + \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(\operatorname{\mathit{Prod}}.\operatorname{\mathit{snd}}\left(q\right)\right) < 6 \cdot \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(\operatorname{\mathit{Prod}}.\operatorname{\mathit{fst}}\left(p\right)\right) + \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(\operatorname{\mathit{Prod}}.\operatorname{\mathit{snd}}\left(p\right)\right)) \land (f\left(q\right) = c))))))), \operatorname{\mathit{Finset}}.\operatorname{\mathit{univ}}\right)\right))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229508Strip.a` (`✓ std3`).

*Citation.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229508: canonical diagonal and antidiagonal strip colourings*. URL: <https://oeis.org/A229508>.

*Commentary.*

The index gives the number of rows. The count selects exactly one monochromatic diagonal or antidiagonal bond and introduces colours in row-major order. The published sequence starts at index one. The literal filter here also defines index zero.

**Theorem 1.2 (Labelled transfer and canonical count).**

$$\forall m: \mathit{Nat}, ((1 \le m) \implies (\operatorname{\mathit{dotProduct}}\left(\operatorname{\mathit{HardinA229508StripData}}.\operatorname{\mathit{initial}}, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{mulVec}}\left(\operatorname{\mathit{HardinA229508StripData}}.\operatorname{T}^{m}, \operatorname{\mathit{HardinA229508StripData}}.\operatorname{\mathit{terminal}}\right)\right) = 6 \cdot (\operatorname{\mathit{HardinA229508Strip}}.\operatorname{a}\left(m + 1\right): \mathit{Int})))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229508Strip.counting_bridge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229508: canonical diagonal and antidiagonal strip colourings*. URL: <https://oeis.org/A229508>.

*Commentary.*

The transfer counts labelled arrays at budget one. For at least two rows the global permutation orbit has size six.

**Theorem 1.3 (Order-twelve recurrence).**

$$\forall n: \mathit{Nat}, ((\operatorname{\mathit{HardinA229508Strip}}.\operatorname{a}\left(n + 14\right): \mathit{Int}) = 50 \cdot (\operatorname{\mathit{HardinA229508Strip}}.\operatorname{a}\left(n + 13\right): \mathit{Int}) - 715 \cdot (\operatorname{\mathit{HardinA229508Strip}}.\operatorname{a}\left(n + 12\right): \mathit{Int}) + 324 \cdot (\operatorname{\mathit{HardinA229508Strip}}.\operatorname{a}\left(n + 11\right): \mathit{Int}) + 50175 \cdot (\operatorname{\mathit{HardinA229508Strip}}.\operatorname{a}\left(n + 10\right): \mathit{Int}) - 180630 \cdot (\operatorname{\mathit{HardinA229508Strip}}.\operatorname{a}\left(n + 9\right): \mathit{Int}) - 940491 \cdot (\operatorname{\mathit{HardinA229508Strip}}.\operatorname{a}\left(n + 8\right): \mathit{Int}) + 4556250 \cdot (\operatorname{\mathit{HardinA229508Strip}}.\operatorname{a}\left(n + 7\right): \mathit{Int}) + 2329155 \cdot (\operatorname{\mathit{HardinA229508Strip}}.\operatorname{a}\left(n + 6\right): \mathit{Int}) - 27398736 \cdot (\operatorname{\mathit{HardinA229508Strip}}.\operatorname{a}\left(n + 5\right): \mathit{Int}) + 13286025 \cdot (\operatorname{\mathit{HardinA229508Strip}}.\operatorname{a}\left(n + 4\right): \mathit{Int}) + 47829690 \cdot (\operatorname{\mathit{HardinA229508Strip}}.\operatorname{a}\left(n + 3\right): \mathit{Int}) - 43046721 \cdot (\operatorname{\mathit{HardinA229508Strip}}.\operatorname{a}\left(n + 2\right): \mathit{Int}))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229508Strip.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229508: canonical diagonal and antidiagonal strip colourings*. URL: <https://oeis.org/A229508>.

*Commentary.*

The forward relation propagates by right multiplication and yields the recurrence at every index at least fourteen.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229508Strip.a`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229508Strip.counting_bridge`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229508Strip.result`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177Canonical](../../../Combinatorics/TraceAvoidingArrays/HardinA233177Canonical.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203981Strip](HardinA203981Strip.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203981StripCertificate](HardinA203981StripCertificate.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229508StripCertificate](HardinA229508StripCertificate.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229508StripData](HardinA229508StripData.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/DefectTransfer](../StripDefects/DefectTransfer.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229637RowColumn](../StripDefects/HardinA229637RowColumn.md)
