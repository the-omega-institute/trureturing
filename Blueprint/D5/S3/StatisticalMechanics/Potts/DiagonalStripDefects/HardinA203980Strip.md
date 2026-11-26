# Five-column zero-defect arrays

## Abstract

Canonical diagonal-strip arrays and their recurrence.

**Definition 1.1 (Literal canonical arrays).**

$$\forall n: \mathit{Nat}, (\operatorname{\mathit{HardinA203980Strip}}.\operatorname{a}\left(n\right) = \operatorname{\mathit{Finset}}.\operatorname{\mathit{card}}\left(\operatorname{\mathit{Finset}}.\operatorname{\mathit{filter}}\left(\lambda f: ((\operatorname{\mathit{Fin}}\left(n + 1\right)) \times (\operatorname{\mathit{Fin}}\left(5\right))) \to (\operatorname{\mathit{Fin}}\left(3\right)) \mapsto ((\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{defects}}\left(\operatorname{\mathit{HardinA203980StripData}}.\operatorname{\mathit{horizontal}}, \operatorname{\mathit{HardinA203980StripData}}.\operatorname{\mathit{between}}, \operatorname{\mathit{List}}.\operatorname{\mathit{ofFn}}\left(\lambda i: \operatorname{\mathit{Fin}}\left(n + 1\right) \mapsto (\lambda j: \operatorname{\mathit{Fin}}\left(5\right) \mapsto (f\left((i, j)\right)))\right)\right) = 0) \land (\forall p: (\operatorname{\mathit{Fin}}\left(n + 1\right)) \times (\operatorname{\mathit{Fin}}\left(5\right)), (\forall c: \operatorname{\mathit{Fin}}\left(3\right), ((c < f\left(p\right)) \implies (\exists q: (\operatorname{\mathit{Fin}}\left(n + 1\right)) \times (\operatorname{\mathit{Fin}}\left(5\right)), ((\operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(\operatorname{\mathit{Prod}}.\operatorname{\mathit{fst}}\left(q\right)\right) \cdot 5 + \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(\operatorname{\mathit{Prod}}.\operatorname{\mathit{snd}}\left(q\right)\right) < \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(\operatorname{\mathit{Prod}}.\operatorname{\mathit{fst}}\left(p\right)\right) \cdot 5 + \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(\operatorname{\mathit{Prod}}.\operatorname{\mathit{snd}}\left(p\right)\right)) \land (f\left(q\right) = c))))))), \operatorname{\mathit{Finset}}.\operatorname{\mathit{univ}}\right)\right))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203980Strip.a` (`✓ std3`).

*Citation.* R. H. Hardin; OEIS Foundation Inc. (2012). *OEIS A203980: canonical diagonal and antidiagonal strip colourings*. URL: <https://oeis.org/A203980>.

*Commentary.*

The function counts all arrays with n+1 rows and five columns, with no equal-colour diagonal or antidiagonal bond. The order index 5*i+j preserves literal row-major colour introduction.

**Theorem 1.2 (Labelled and canonical counts).**

$$\forall m: \mathit{Nat}, ((1 \le m) \implies (\operatorname{\mathit{dotProduct}}\left(\operatorname{\mathit{HardinA203980StripData}}.\operatorname{\mathit{initial}}, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{mulVec}}\left(\operatorname{\mathit{HardinA203980StripData}}.\operatorname{T}^{m}, \operatorname{\mathit{HardinA203980StripData}}.\operatorname{\mathit{terminal}}\right)\right) = 6 \cdot (\operatorname{\mathit{HardinA203980Strip}}.\operatorname{a}\left(m\right): \mathit{Int})))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203980Strip.counting_bridge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2012). *OEIS A203980: canonical diagonal and antidiagonal strip colourings*. URL: <https://oeis.org/A203980>.

*Commentary.*

At least two rows supply a bond, so every allowed array uses at least two colours. The permutation action then gives exactly six labelled arrays for each canonical array. The exact-budget transfer and the row-major canonical counting theorem give the identity.

**Theorem 1.3 (Order-four recurrence).**

$$\forall n: \mathit{Nat}, ((\operatorname{\mathit{HardinA203980Strip}}.\operatorname{a}\left(n + 5\right): \mathit{Int}) = 15 \cdot (\operatorname{\mathit{HardinA203980Strip}}.\operatorname{a}\left(n + 4\right): \mathit{Int}) - 270 \cdot (\operatorname{\mathit{HardinA203980Strip}}.\operatorname{a}\left(n + 2\right): \mathit{Int}) + 324 \cdot (\operatorname{\mathit{HardinA203980Strip}}.\operatorname{a}\left(n + 1\right): \mathit{Int}))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203980Strip.result` (`✓ std3`). ∎

*Resolves.* `Problems/hardin203980` (proved) by `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203980Strip.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"hardin203980","declaration_gid":"D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203980Strip.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2012). *OEIS A203980: canonical diagonal and antidiagonal strip colourings*. URL: <https://oeis.org/A203980>.

*Commentary.*

The transfer relation at powers one through five propagates by matrix multiplication. Dividing the labelled counts by six gives the recurrence at every index at least five.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203980Strip.a`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203980Strip.counting_bridge`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203980Strip.result`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177Canonical](../../../Combinatorics/TraceAvoidingArrays/HardinA233177Canonical.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/TransferMatrix](../../../Combinatorics/TraceAvoidingArrays/TransferMatrix.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203980StripCertificate](HardinA203980StripCertificate.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203980StripData](HardinA203980StripData.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/DefectTransfer](../StripDefects/DefectTransfer.md)
