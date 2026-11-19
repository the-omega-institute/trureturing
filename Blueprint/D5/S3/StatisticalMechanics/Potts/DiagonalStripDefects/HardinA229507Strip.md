# Five-column strip colourings

## Abstract

Exact-budget diagonal and antidiagonal arrays.

**Definition 1.1 (a).**

$$\forall n: \mathit{Nat}, (\operatorname{\mathit{HardinA229507Strip}}.\operatorname{a}\left(n\right) = \operatorname{\mathit{Finset}}.\operatorname{\mathit{card}}\left(\operatorname{\mathit{Finset}}.\operatorname{\mathit{filter}}\left(\lambda f: ((\operatorname{\mathit{Fin}}\left(n\right)) \times (\operatorname{\mathit{Fin}}\left(5\right))) \to (\operatorname{\mathit{Fin}}\left(3\right)) \mapsto ((\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{defects}}\left(\operatorname{\mathit{HardinA203980StripData}}.\operatorname{\mathit{horizontal}}, \operatorname{\mathit{HardinA203980StripData}}.\operatorname{\mathit{between}}, \operatorname{\mathit{List}}.\operatorname{\mathit{ofFn}}\left(\lambda i: \operatorname{\mathit{Fin}}\left(n\right) \mapsto (\lambda j: \operatorname{\mathit{Fin}}\left(5\right) \mapsto (f\left((i, j)\right)))\right)\right) = 1) \land (\forall p: (\operatorname{\mathit{Fin}}\left(n\right)) \times (\operatorname{\mathit{Fin}}\left(5\right)), (\forall c: \operatorname{\mathit{Fin}}\left(3\right), ((c < f\left(p\right)) \implies (\exists q: (\operatorname{\mathit{Fin}}\left(n\right)) \times (\operatorname{\mathit{Fin}}\left(5\right)), ((\operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(\operatorname{\mathit{Prod}}.\operatorname{\mathit{fst}}\left(q\right)\right) \cdot 5 + \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(\operatorname{\mathit{Prod}}.\operatorname{\mathit{snd}}\left(q\right)\right) < \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(\operatorname{\mathit{Prod}}.\operatorname{\mathit{fst}}\left(p\right)\right) \cdot 5 + \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(\operatorname{\mathit{Prod}}.\operatorname{\mathit{snd}}\left(p\right)\right)) \land (f\left(q\right) = c))))))), \operatorname{\mathit{Finset}}.\operatorname{\mathit{univ}}\right)\right))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229507Strip.a` (`✓ std3`).

*Citation.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229507: canonical diagonal and antidiagonal strip colourings*. URL: <https://oeis.org/A229507>.

*Commentary.*

The filtered count uses n rows and five columns, exactly 1 diagonal or antidiagonal equal-colour bonds, and the original row-major colour introduction predicate. The ordinal 5*i+j orders the cells.

**Theorem 1.2 (counting_bridge).**

$$\forall m: \mathit{Nat}, (\operatorname{\mathit{dotProduct}}\left(\operatorname{\mathit{HardinA229507StripData}}.\operatorname{\mathit{initial}}, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{mulVec}}\left(\operatorname{\mathit{HardinA229507StripData}}.\operatorname{T}^{m}, \operatorname{\mathit{HardinA229507StripData}}.\operatorname{\mathit{terminal}}\right)\right) = 6 \cdot (\operatorname{\mathit{HardinA229507Strip}}.\operatorname{a}\left(m + 1\right): \mathit{Int}))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229507Strip.counting_bridge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229507: canonical diagonal and antidiagonal strip colourings*. URL: <https://oeis.org/A229507>.

*Commentary.*

Constant arrays have 8*m equal-colour bonds, so exactly 1 defects excludes them. Every canonical array therefore has exactly six labelled realizations.

**Theorem 1.3 (result).**

$$\forall n: \mathit{Nat}, ((\operatorname{\mathit{HardinA229507Strip}}.\operatorname{a}\left(n + 10\right): \mathit{Int}) = 30 \cdot (\operatorname{\mathit{HardinA229507Strip}}.\operatorname{a}\left(n + 9\right): \mathit{Int}) - 225 \cdot (\operatorname{\mathit{HardinA229507Strip}}.\operatorname{a}\left(n + 8\right): \mathit{Int}) - 540 \cdot (\operatorname{\mathit{HardinA229507Strip}}.\operatorname{a}\left(n + 7\right): \mathit{Int}) + 8748 \cdot (\operatorname{\mathit{HardinA229507Strip}}.\operatorname{a}\left(n + 6\right): \mathit{Int}) - 9720 \cdot (\operatorname{\mathit{HardinA229507Strip}}.\operatorname{a}\left(n + 5\right): \mathit{Int}) - 72900 \cdot (\operatorname{\mathit{HardinA229507Strip}}.\operatorname{a}\left(n + 4\right): \mathit{Int}) + 174960 \cdot (\operatorname{\mathit{HardinA229507Strip}}.\operatorname{a}\left(n + 3\right): \mathit{Int}) - 104976 \cdot (\operatorname{\mathit{HardinA229507Strip}}.\operatorname{a}\left(n + 2\right): \mathit{Int}))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229507Strip.result` (`✓ std3`). ∎

*Resolves.* `Problems/hardin229507` (proved) by `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229507Strip.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"hardin229507","declaration_gid":"D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229507Strip.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229507: canonical diagonal and antidiagonal strip colourings*. URL: <https://oeis.org/A229507>.

*Commentary.*

The finite vector relation propagates to every later power. The canonical counting bridge gives the recurrence at every index at least 10.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229507Strip.a`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229507Strip.counting_bridge`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229507Strip.result`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177Canonical](../../../Combinatorics/TraceAvoidingArrays/HardinA233177Canonical.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203980StripCertificate](HardinA203980StripCertificate.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203980StripData](HardinA203980StripData.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229507StripCertificate](HardinA229507StripCertificate.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229507StripData](HardinA229507StripData.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/DefectTransfer](../StripDefects/DefectTransfer.md)
