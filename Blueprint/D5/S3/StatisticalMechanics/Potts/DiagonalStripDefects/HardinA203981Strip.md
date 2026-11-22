# Canonical six-column zero-defect arrays

## Abstract

Canonical six-column zero-defect arrays

**Definition 1.1 (Literal row-major canonical count).**

$$\forall n: \mathit{Nat}, (\operatorname{\mathit{HardinA203981Strip}}.\operatorname{a}\left(n\right) = \operatorname{\mathit{Finset}}.\operatorname{\mathit{card}}\left(\operatorname{\mathit{Finset}}.\operatorname{\mathit{filter}}\left(\lambda f: ((\operatorname{\mathit{Fin}}\left(n + 1\right)) \times (\operatorname{\mathit{Fin}}\left(6\right))) \to (\operatorname{\mathit{Fin}}\left(3\right)) \mapsto ((\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{defects}}\left(\operatorname{\mathit{Finset}}.\operatorname{\mathit{empty}}, \operatorname{\mathit{HardinA229637RowColumn}}.\operatorname{\mathit{betw}}\left(6\right), \operatorname{\mathit{List}}.\operatorname{\mathit{ofFn}}\left(\lambda i: \operatorname{\mathit{Fin}}\left(n + 1\right) \mapsto (\lambda j: \operatorname{\mathit{Fin}}\left(6\right) \mapsto (f\left((i, j)\right)))\right)\right) = 0) \land (\forall p: (\operatorname{\mathit{Fin}}\left(n + 1\right)) \times (\operatorname{\mathit{Fin}}\left(6\right)), (\forall c: \operatorname{\mathit{Fin}}\left(3\right), ((c < f\left(p\right)) \implies (\exists q: (\operatorname{\mathit{Fin}}\left(n + 1\right)) \times (\operatorname{\mathit{Fin}}\left(6\right)), ((6 \cdot \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(\operatorname{\mathit{Prod}}.\operatorname{\mathit{fst}}\left(q\right)\right) + \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(\operatorname{\mathit{Prod}}.\operatorname{\mathit{snd}}\left(q\right)\right) < 6 \cdot \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(\operatorname{\mathit{Prod}}.\operatorname{\mathit{fst}}\left(p\right)\right) + \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(\operatorname{\mathit{Prod}}.\operatorname{\mathit{snd}}\left(p\right)\right)) \land (f\left(q\right) = c))))))), \operatorname{\mathit{Finset}}.\operatorname{\mathit{univ}}\right)\right))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203981Strip.a` (`✓ std3`).

*Citation.* R. H. Hardin; OEIS Foundation Inc. (2012). *OEIS A203981: canonical diagonal and antidiagonal strip colourings*. URL: <https://oeis.org/A203981>.

*Commentary.*

The arrays have one more row than the sequence index. The order is the one induced by the row-major index 6i+j, with colours introduced in increasing order. The published sequence starts at index one. The literal filter here also defines index zero.

**Theorem 1.2 (Labelled and canonical arrays at small budgets).**

$$\forall m: \mathit{Nat}, (\forall d: \mathit{Nat}, ((1 \le m) \implies ((d < 10) \implies (\left(\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{literalCount}}_{3}\right)\left(\operatorname{\mathit{Finset}}.\operatorname{\mathit{empty}}, \operatorname{\mathit{HardinA229637RowColumn}}.\operatorname{\mathit{betw}}\left(6\right), d, m + 1\right) = 6 \cdot \operatorname{\mathit{Finset}}.\operatorname{\mathit{card}}\left(\operatorname{\mathit{Finset}}.\operatorname{\mathit{filter}}\left(\lambda f: ((\operatorname{\mathit{Fin}}\left(m + 1\right)) \times (\operatorname{\mathit{Fin}}\left(6\right))) \to (\operatorname{\mathit{Fin}}\left(3\right)) \mapsto ((\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{defects}}\left(\operatorname{\mathit{Finset}}.\operatorname{\mathit{empty}}, \operatorname{\mathit{HardinA229637RowColumn}}.\operatorname{\mathit{betw}}\left(6\right), \operatorname{\mathit{List}}.\operatorname{\mathit{ofFn}}\left(\lambda i: \operatorname{\mathit{Fin}}\left(m + 1\right) \mapsto (\lambda j: \operatorname{\mathit{Fin}}\left(6\right) \mapsto (f\left((i, j)\right)))\right)\right) = d) \land (\forall p: (\operatorname{\mathit{Fin}}\left(m + 1\right)) \times (\operatorname{\mathit{Fin}}\left(6\right)), (\forall c: \operatorname{\mathit{Fin}}\left(3\right), ((c < f\left(p\right)) \implies (\exists q: (\operatorname{\mathit{Fin}}\left(m + 1\right)) \times (\operatorname{\mathit{Fin}}\left(6\right)), ((6 \cdot \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(\operatorname{\mathit{Prod}}.\operatorname{\mathit{fst}}\left(q\right)\right) + \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(\operatorname{\mathit{Prod}}.\operatorname{\mathit{snd}}\left(q\right)\right) < 6 \cdot \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(\operatorname{\mathit{Prod}}.\operatorname{\mathit{fst}}\left(p\right)\right) + \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(\operatorname{\mathit{Prod}}.\operatorname{\mathit{snd}}\left(p\right)\right)) \land (f\left(q\right) = c))))))), \operatorname{\mathit{Finset}}.\operatorname{\mathit{univ}}\right)\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203981Strip.scale_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2012). *OEIS A203981: canonical diagonal and antidiagonal strip colourings*. URL: <https://oeis.org/A203981>.

*Commentary.*

The subscript gives the palette size. Two rows contain ten diagonal and antidiagonal bonds. A smaller defect budget therefore excludes constant arrays. The global action on the colours gives six labelled arrays per canonical array.

**Theorem 1.3 (Exact transfer for the canonical count).**

$$\forall m: \mathit{Nat}, ((1 \le m) \implies (\operatorname{\mathit{dotProduct}}\left(\operatorname{\mathit{HardinA203981StripData}}.\operatorname{\mathit{initial}}, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{mulVec}}\left(\operatorname{\mathit{HardinA203981StripData}}.\operatorname{T}^{m}, (1: (\operatorname{\mathit{Fin}}\left(15\right)) \to (\mathit{Int}))\right)\right) = 6 \cdot (\operatorname{\mathit{HardinA203981Strip}}.\operatorname{a}\left(m\right): \mathit{Int})))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203981Strip.counting_bridge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2012). *OEIS A203981: canonical diagonal and antidiagonal strip colourings*. URL: <https://oeis.org/A203981>.

*Commentary.*

The transfer counts labelled arrays. The orbit size converts the count to the literal canonical form.

**Theorem 1.4 (Order-six recurrence).**

$$\forall n: \mathit{Nat}, ((\operatorname{\mathit{HardinA203981Strip}}.\operatorname{a}\left(n + 7\right): \mathit{Int}) = 25 \cdot (\operatorname{\mathit{HardinA203981Strip}}.\operatorname{a}\left(n + 6\right): \mathit{Int}) - 45 \cdot (\operatorname{\mathit{HardinA203981Strip}}.\operatorname{a}\left(n + 5\right): \mathit{Int}) - 963 \cdot (\operatorname{\mathit{HardinA203981Strip}}.\operatorname{a}\left(n + 4\right): \mathit{Int}) + 2025 \cdot (\operatorname{\mathit{HardinA203981Strip}}.\operatorname{a}\left(n + 3\right): \mathit{Int}) + 3645 \cdot (\operatorname{\mathit{HardinA203981Strip}}.\operatorname{a}\left(n + 2\right): \mathit{Int}) - 6561 \cdot (\operatorname{\mathit{HardinA203981Strip}}.\operatorname{a}\left(n + 1\right): \mathit{Int}))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203981Strip.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2012). *OEIS A203981: canonical diagonal and antidiagonal strip colourings*. URL: <https://oeis.org/A203981>.

*Commentary.*

The coefficient relation propagates under additional transfer steps. The displayed shift gives every index at least seven.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203981Strip.a`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203981Strip.counting_bridge`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203981Strip.result`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203981Strip.scale_count`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177Canonical](../../../Combinatorics/TraceAvoidingArrays/HardinA233177Canonical.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203981StripCertificate](HardinA203981StripCertificate.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203981StripData](HardinA203981StripData.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/DefectTransfer](../StripDefects/DefectTransfer.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229637RowColumn](../StripDefects/HardinA229637RowColumn.md)
