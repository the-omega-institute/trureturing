# Hardin A229532: exact defect recurrence

## Abstract

Literal HDA colourings and exact defect transfer.

The literal array has n rows, 6 columns and exactly one monochromatic HDA bond. Rows are swept by an exact-budget transfer with 31 equality-and-budget classes, identifying reflection. Every proper-row diagonal block calls the published zero-temperature owner. Finite certificates check the exact image and every defect entry.

**Definition 1.1 (The literal canonical array count).**

$$\forall n: \mathit{Nat}, (\operatorname{\mathit{HardinA229532Strip}}.\operatorname{a}\left(n\right) = \operatorname{\mathit{Finset}}.\operatorname{\mathit{card}}\left(\operatorname{\mathit{Finset}}.\operatorname{\mathit{filter}}\left(\lambda A: ((\operatorname{\mathit{Fin}}\left(n\right)) \times (\operatorname{\mathit{Fin}}\left(6\right))) \to (\operatorname{\mathit{Fin}}\left(3\right)) \mapsto ((\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{defects}}\left(\operatorname{\mathit{HardinA229584StripData}}.\operatorname{\mathit{horizontal}}, \operatorname{\mathit{HardinA229532StripData}}.\operatorname{\mathit{between}}, \operatorname{\mathit{List}}.\operatorname{\mathit{ofFn}}\left(\lambda i: \operatorname{\mathit{Fin}}\left(n\right) \mapsto (\lambda j: \operatorname{\mathit{Fin}}\left(6\right) \mapsto (A\left((i, j)\right)))\right)\right) = 1) \land (\forall p: (\operatorname{\mathit{Fin}}\left(n\right)) \times (\operatorname{\mathit{Fin}}\left(6\right)), (\forall c: \operatorname{\mathit{Fin}}\left(3\right), ((c < A\left(p\right)) \implies (\exists q: (\operatorname{\mathit{Fin}}\left(n\right)) \times (\operatorname{\mathit{Fin}}\left(6\right)), ((\operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(\operatorname{\mathit{Prod}}.\operatorname{\mathit{fst}}\left(q\right)\right) \cdot 6 + \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(\operatorname{\mathit{Prod}}.\operatorname{\mathit{snd}}\left(q\right)\right) < \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(\operatorname{\mathit{Prod}}.\operatorname{\mathit{fst}}\left(p\right)\right) \cdot 6 + \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(\operatorname{\mathit{Prod}}.\operatorname{\mathit{snd}}\left(p\right)\right)) \land (A\left(q\right) = c))))))), \operatorname{\mathit{Finset}}.\operatorname{\mathit{univ}}\right)\right))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/HardinA229532Strip.a` (`✓ std3`).

*Citation.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229532: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229532>.

*Commentary.*

The filter ranges over every actual array over Fin 3. Canonical uses the lifted row-major order, independently of the transfer sweep. Each listed bond contributes exactly one when its two endpoint colours agree.

**Theorem 1.2 (The registered all-index recurrence).**

$$\forall n: \operatorname{\mathit{Nat}}, ((\operatorname{\mathit{HardinA229532Strip}}.\operatorname{a}\left(n + 20\right): \operatorname{\mathit{Int}}) = 36 \cdot (\operatorname{\mathit{HardinA229532Strip}}.\operatorname{a}\left(n + 19\right): \operatorname{\mathit{Int}}) - 436 \cdot (\operatorname{\mathit{HardinA229532Strip}}.\operatorname{a}\left(n + 18\right): \operatorname{\mathit{Int}}) + 1854 \cdot (\operatorname{\mathit{HardinA229532Strip}}.\operatorname{a}\left(n + 17\right): \operatorname{\mathit{Int}}) + 340 \cdot (\operatorname{\mathit{HardinA229532Strip}}.\operatorname{a}\left(n + 16\right): \operatorname{\mathit{Int}}) - 19128 \cdot (\operatorname{\mathit{HardinA229532Strip}}.\operatorname{a}\left(n + 15\right): \operatorname{\mathit{Int}}) + 23849 \cdot (\operatorname{\mathit{HardinA229532Strip}}.\operatorname{a}\left(n + 14\right): \operatorname{\mathit{Int}}) + 56184 \cdot (\operatorname{\mathit{HardinA229532Strip}}.\operatorname{a}\left(n + 13\right): \operatorname{\mathit{Int}}) - 108224 \cdot (\operatorname{\mathit{HardinA229532Strip}}.\operatorname{a}\left(n + 12\right): \operatorname{\mathit{Int}}) - 40816 \cdot (\operatorname{\mathit{HardinA229532Strip}}.\operatorname{a}\left(n + 11\right): \operatorname{\mathit{Int}}) + 160400 \cdot (\operatorname{\mathit{HardinA229532Strip}}.\operatorname{a}\left(n + 10\right): \operatorname{\mathit{Int}}) - 34136 \cdot (\operatorname{\mathit{HardinA229532Strip}}.\operatorname{a}\left(n + 9\right): \operatorname{\mathit{Int}}) - 83203 \cdot (\operatorname{\mathit{HardinA229532Strip}}.\operatorname{a}\left(n + 8\right): \operatorname{\mathit{Int}}) + 42628 \cdot (\operatorname{\mathit{HardinA229532Strip}}.\operatorname{a}\left(n + 7\right): \operatorname{\mathit{Int}}) + 6468 \cdot (\operatorname{\mathit{HardinA229532Strip}}.\operatorname{a}\left(n + 6\right): \operatorname{\mathit{Int}}) - 6334 \cdot (\operatorname{\mathit{HardinA229532Strip}}.\operatorname{a}\left(n + 5\right): \operatorname{\mathit{Int}}) + 204 \cdot (\operatorname{\mathit{HardinA229532Strip}}.\operatorname{a}\left(n + 4\right): \operatorname{\mathit{Int}}) + 240 \cdot (\operatorname{\mathit{HardinA229532Strip}}.\operatorname{a}\left(n + 3\right): \operatorname{\mathit{Int}}) - 25 \cdot (\operatorname{\mathit{HardinA229532Strip}}.\operatorname{a}\left(n + 2\right): \operatorname{\mathit{Int}}))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/HardinA229532Strip.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229532: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229532>.

*Commentary.*

The recurrence is an identity in the integers at every index at least 20. DefectTransfer.lumped_count and forward_shift propagate the vector relation from row twenty. A separate terminal scalar certificate at row nineteen supplies the first index twenty; the full vector relation is not claimed there. The literal row-major canonical representative is independent of the row sweep. canonical_pattern_card supplies the factor six in the range used here, where a constant array cannot have the prescribed defect count. This is a finite combinatorial count and makes no thermodynamic-limit claim.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/HardinA229532Strip.a`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/HardinA229532Strip.result`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177Canonical](../../../Combinatorics/TraceAvoidingArrays/HardinA233177Canonical.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/WidthSix/HardinA229532StripClasses](WidthSix/HardinA229532StripClasses.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/WidthSix/HardinA229532StripData](WidthSix/HardinA229532StripData.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/DefectTransfer](../StripDefects/DefectTransfer.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229584StripData](../StripDefects/HardinA229584StripData.md)
