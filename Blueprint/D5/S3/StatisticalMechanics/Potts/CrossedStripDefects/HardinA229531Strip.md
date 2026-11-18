# Hardin A229531: exact defect recurrence

## Abstract

Literal HDA colourings and exact defect transfer.

The literal array has n rows, 5 columns and exactly one monochromatic HDA bond. Rows are swept by an exact-budget transfer with 20 equality-and-budget classes, identifying reflection. Every proper-row diagonal block calls the published zero-temperature owner. Finite certificates check the exact image and every defect entry.

**Definition 1.1 (The literal canonical array count).**

$$\forall n: \mathit{Nat}, (\operatorname{\mathit{HardinA229531Strip}}.\operatorname{a}\left(n\right) = \operatorname{\mathit{Finset}}.\operatorname{\mathit{card}}\left(\operatorname{\mathit{Finset}}.\operatorname{\mathit{filter}}\left(\lambda A: ((\operatorname{\mathit{Fin}}\left(n\right)) \times (\operatorname{\mathit{Fin}}\left(5\right))) \to (\operatorname{\mathit{Fin}}\left(3\right)) \mapsto ((\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{defects}}\left(\operatorname{\mathit{HardinA229531StripData}}.\operatorname{\mathit{horizontal}}, \operatorname{\mathit{HardinA229531StripData}}.\operatorname{\mathit{between}}, \operatorname{\mathit{List}}.\operatorname{\mathit{ofFn}}\left(\lambda i: \operatorname{\mathit{Fin}}\left(n\right) \mapsto (\lambda j: \operatorname{\mathit{Fin}}\left(5\right) \mapsto (A\left((i, j)\right)))\right)\right) = 1) \land (\forall p: (\operatorname{\mathit{Fin}}\left(n\right)) \times (\operatorname{\mathit{Fin}}\left(5\right)), (\forall c: \operatorname{\mathit{Fin}}\left(3\right), ((c < A\left(p\right)) \implies (\exists q: (\operatorname{\mathit{Fin}}\left(n\right)) \times (\operatorname{\mathit{Fin}}\left(5\right)), ((\operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(\operatorname{\mathit{Prod}}.\operatorname{\mathit{fst}}\left(q\right)\right) \cdot 5 + \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(\operatorname{\mathit{Prod}}.\operatorname{\mathit{snd}}\left(q\right)\right) < \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(\operatorname{\mathit{Prod}}.\operatorname{\mathit{fst}}\left(p\right)\right) \cdot 5 + \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(\operatorname{\mathit{Prod}}.\operatorname{\mathit{snd}}\left(p\right)\right)) \land (A\left(q\right) = c))))))), \operatorname{\mathit{Finset}}.\operatorname{\mathit{univ}}\right)\right))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229531Strip.a` (`✓ std3`).

*Citation.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229531: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229531>.

*Commentary.*

The filter ranges over every actual array over Fin 3. Canonical uses the lifted row-major order, independently of the transfer sweep. Each listed bond contributes exactly one when its two endpoint colours agree.

**Theorem 1.2 (The registered all-index recurrence).**

$$\forall n: \mathit{Nat}, ((\operatorname{\mathit{HardinA229531Strip}}.\operatorname{a}\left(n + 14\right): \operatorname{\mathit{Int}}) = 28 \cdot (\operatorname{\mathit{HardinA229531Strip}}.\operatorname{a}\left(n + 13\right): \operatorname{\mathit{Int}}) - 286 \cdot (\operatorname{\mathit{HardinA229531Strip}}.\operatorname{a}\left(n + 12\right): \operatorname{\mathit{Int}}) + 1290 \cdot (\operatorname{\mathit{HardinA229531Strip}}.\operatorname{a}\left(n + 11\right): \operatorname{\mathit{Int}}) - 2373 \cdot (\operatorname{\mathit{HardinA229531Strip}}.\operatorname{a}\left(n + 10\right): \operatorname{\mathit{Int}}) + 304 \cdot (\operatorname{\mathit{HardinA229531Strip}}.\operatorname{a}\left(n + 9\right): \operatorname{\mathit{Int}}) + 3551 \cdot (\operatorname{\mathit{HardinA229531Strip}}.\operatorname{a}\left(n + 8\right): \operatorname{\mathit{Int}}) - 2846 \cdot (\operatorname{\mathit{HardinA229531Strip}}.\operatorname{a}\left(n + 7\right): \operatorname{\mathit{Int}}) - 546 \cdot (\operatorname{\mathit{HardinA229531Strip}}.\operatorname{a}\left(n + 6\right): \operatorname{\mathit{Int}}) + 1308 \cdot (\operatorname{\mathit{HardinA229531Strip}}.\operatorname{a}\left(n + 5\right): \operatorname{\mathit{Int}}) - 505 \cdot (\operatorname{\mathit{HardinA229531Strip}}.\operatorname{a}\left(n + 4\right): \operatorname{\mathit{Int}}) + 76 \cdot (\operatorname{\mathit{HardinA229531Strip}}.\operatorname{a}\left(n + 3\right): \operatorname{\mathit{Int}}) - 4 \cdot (\operatorname{\mathit{HardinA229531Strip}}.\operatorname{a}\left(n + 2\right): \operatorname{\mathit{Int}}))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229531Strip.result` (`✓ std3`). ∎

*Resolves.* `Problems/hardin229531` (proved) by `D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229531Strip.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"hardin229531","declaration_gid":"D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229531Strip.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229531: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229531>.

*Commentary.*

The recurrence is an identity in the integers at every index at least 14. DefectTransfer.lumped_count and forward_shift propagate the finite certificate. The literal row-major canonical representative is independent of the row sweep. canonical_pattern_card supplies the factor six in the range used here, where a constant array cannot have the prescribed defect count. This is a finite combinatorial count and makes no thermodynamic-limit claim.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229531Strip.a`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229531Strip.result`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177Canonical](../../../Combinatorics/TraceAvoidingArrays/HardinA233177Canonical.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229531StripClasses](HardinA229531StripClasses.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/DefectTransfer](../StripDefects/DefectTransfer.md)
