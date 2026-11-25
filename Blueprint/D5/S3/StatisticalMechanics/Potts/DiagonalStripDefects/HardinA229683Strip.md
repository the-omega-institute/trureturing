# Canonical six-column two-defect arrays

## Abstract

Canonical six-column two-defect arrays

**Definition 1.1 (Literal row-major canonical count).**

$$\forall n: \mathit{Nat}, (\operatorname{\mathit{HardinA229683Strip}}.\operatorname{a}\left(n\right) = \operatorname{\mathit{Finset}}.\operatorname{\mathit{card}}\left(\operatorname{\mathit{Finset}}.\operatorname{\mathit{filter}}\left(\lambda f: ((\operatorname{\mathit{Fin}}\left(n\right)) \times (\operatorname{\mathit{Fin}}\left(6\right))) \to (\operatorname{\mathit{Fin}}\left(3\right)) \mapsto ((\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{defects}}\left(\operatorname{\mathit{Finset}}.\operatorname{\mathit{empty}}, \operatorname{\mathit{HardinA229637RowColumn}}.\operatorname{\mathit{betw}}\left(6\right), \operatorname{\mathit{List}}.\operatorname{\mathit{ofFn}}\left(\lambda i: \operatorname{\mathit{Fin}}\left(n\right) \mapsto (\lambda j: \operatorname{\mathit{Fin}}\left(6\right) \mapsto (f\left((i, j)\right)))\right)\right) = 2) \land (\forall p: (\operatorname{\mathit{Fin}}\left(n\right)) \times (\operatorname{\mathit{Fin}}\left(6\right)), (\forall c: \operatorname{\mathit{Fin}}\left(3\right), ((c < f\left(p\right)) \implies (\exists q: (\operatorname{\mathit{Fin}}\left(n\right)) \times (\operatorname{\mathit{Fin}}\left(6\right)), ((6 \cdot \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(\operatorname{\mathit{Prod}}.\operatorname{\mathit{fst}}\left(q\right)\right) + \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(\operatorname{\mathit{Prod}}.\operatorname{\mathit{snd}}\left(q\right)\right) < 6 \cdot \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(\operatorname{\mathit{Prod}}.\operatorname{\mathit{fst}}\left(p\right)\right) + \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(\operatorname{\mathit{Prod}}.\operatorname{\mathit{snd}}\left(p\right)\right)) \land (f\left(q\right) = c))))))), \operatorname{\mathit{Finset}}.\operatorname{\mathit{univ}}\right)\right))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229683Strip.a` (`✓ std3`).

*Citation.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229683: canonical diagonal and antidiagonal strip colourings*. URL: <https://oeis.org/A229683>.

*Commentary.*

The index counts rows. The arrays have exactly two monochromatic diagonal or antidiagonal bonds, with colours introduced in row-major order. The published sequence starts at index one. The literal filter here also defines index zero.

**Theorem 1.2 (Labelled transfer and canonical count).**

$$\forall m: \mathit{Nat}, (\operatorname{\mathit{dotProduct}}\left(\operatorname{\mathit{HardinA229683StripData}}.\operatorname{\mathit{initial}}, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{mulVec}}\left(\operatorname{\mathit{HardinA229683StripData}}.\operatorname{T}^{m}, \operatorname{\mathit{HardinA229683StripData}}.\operatorname{\mathit{terminal}}\right)\right) = 6 \cdot (\operatorname{\mathit{HardinA229683Strip}}.\operatorname{a}\left(m + 1\right): \mathit{Int}))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229683Strip.counting_bridge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229683: canonical diagonal and antidiagonal strip colourings*. URL: <https://oeis.org/A229683>.

*Commentary.*

The transfer counts labelled arrays at budget two. Constant arrays have a multiple of ten defects, so each canonical array at budget two has six labelled realizations. For a single row both counts vanish.

**Theorem 1.3 (Order-eighteen recurrence).**

$$\forall n: \mathit{Nat}, ((\operatorname{\mathit{HardinA229683Strip}}.\operatorname{a}\left(n + 21\right): \mathit{Int}) = 75 \cdot (\operatorname{\mathit{HardinA229683Strip}}.\operatorname{a}\left(n + 20\right): \mathit{Int}) - 2010 \cdot (\operatorname{\mathit{HardinA229683Strip}}.\operatorname{a}\left(n + 19\right): \mathit{Int}) + 19486 \cdot (\operatorname{\mathit{HardinA229683Strip}}.\operatorname{a}\left(n + 18\right): \mathit{Int}) + 60075 \cdot (\operatorname{\mathit{HardinA229683Strip}}.\operatorname{a}\left(n + 17\right): \mathit{Int}) - 2206575 \cdot (\operatorname{\mathit{HardinA229683Strip}}.\operatorname{a}\left(n + 16\right): \mathit{Int}) + 7404210 \cdot (\operatorname{\mathit{HardinA229683Strip}}.\operatorname{a}\left(n + 15\right): \mathit{Int}) + 70536825 \cdot (\operatorname{\mathit{HardinA229683Strip}}.\operatorname{a}\left(n + 14\right): \mathit{Int}) - 435322350 \cdot (\operatorname{\mathit{HardinA229683Strip}}.\operatorname{a}\left(n + 13\right): \mathit{Int}) - 601275555 \cdot (\operatorname{\mathit{HardinA229683Strip}}.\operatorname{a}\left(n + 12\right): \mathit{Int}) + 8082823950 \cdot (\operatorname{\mathit{HardinA229683Strip}}.\operatorname{a}\left(n + 11\right): \mathit{Int}) - 6257717775 \cdot (\operatorname{\mathit{HardinA229683Strip}}.\operatorname{a}\left(n + 10\right): \mathit{Int}) - 54520532190 \cdot (\operatorname{\mathit{HardinA229683Strip}}.\operatorname{a}\left(n + 9\right): \mathit{Int}) + 92909172825 \cdot (\operatorname{\mathit{HardinA229683Strip}}.\operatorname{a}\left(n + 8\right): \mathit{Int}) + 132368667075 \cdot (\operatorname{\mathit{HardinA229683Strip}}.\operatorname{a}\left(n + 7\right): \mathit{Int}) - 366499782594 \cdot (\operatorname{\mathit{HardinA229683Strip}}.\operatorname{a}\left(n + 6\right): \mathit{Int}) + 470715894135 \cdot (\operatorname{\mathit{HardinA229683Strip}}.\operatorname{a}\left(n + 4\right): \mathit{Int}) - 282429536481 \cdot (\operatorname{\mathit{HardinA229683Strip}}.\operatorname{a}\left(n + 3\right): \mathit{Int}))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229683Strip.result` (`✓ std3`). ∎

*Resolves.* `Problems/hardin229683` (proved) by `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229683Strip.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"hardin229683","declaration_gid":"D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229683Strip.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229683: canonical diagonal and antidiagonal strip colourings*. URL: <https://oeis.org/A229683>.

*Commentary.*

The forward relation propagates under further transfer steps and gives the recurrence at all indices at least twenty-one.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229683Strip.a`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229683Strip.counting_bridge`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229683Strip.result`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177Canonical](../../../Combinatorics/TraceAvoidingArrays/HardinA233177Canonical.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203981Strip](HardinA203981Strip.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203981StripCertificate](HardinA203981StripCertificate.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229508StripData](HardinA229508StripData.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229683StripCertificate](HardinA229683StripCertificate.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229683StripData](HardinA229683StripData.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/DefectTransfer](../StripDefects/DefectTransfer.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229637RowColumn](../StripDefects/HardinA229637RowColumn.md)
