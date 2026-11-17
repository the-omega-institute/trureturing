# Hardin A229634: exact defect recurrence

## Abstract

Literal HDA colourings and exact defect transfer.

The literal array has n rows, 5 columns and exactly two monochromatic HDA bonds. Rows are swept by an exact-budget transfer with 33 equality-and-budget classes, identifying reflection. Every proper-row diagonal block calls the published zero-temperature owner. Finite certificates check the exact image and every defect entry.

**Definition 1.1 (The literal canonical array count).**

$$\forall n: \mathit{Nat}, (\operatorname{\mathit{HardinA229634Strip}}.\operatorname{a}\left(n\right) = \operatorname{\mathit{Finset}}.\operatorname{\mathit{card}}\left(\operatorname{\mathit{Finset}}.\operatorname{\mathit{filter}}\left(\lambda A: ((\operatorname{\mathit{Fin}}\left(n\right)) \times (\operatorname{\mathit{Fin}}\left(5\right))) \to (\operatorname{\mathit{Fin}}\left(3\right)) \mapsto ((\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{defects}}\left(\operatorname{\mathit{HardinA229531StripData}}.\operatorname{\mathit{horizontal}}, \operatorname{\mathit{HardinA229531StripData}}.\operatorname{\mathit{between}}, \operatorname{\mathit{List}}.\operatorname{\mathit{ofFn}}\left(\lambda i: \operatorname{\mathit{Fin}}\left(n\right) \mapsto (\lambda j: \operatorname{\mathit{Fin}}\left(5\right) \mapsto (A\left((i, j)\right)))\right)\right) = 2) \land (\forall p: (\operatorname{\mathit{Fin}}\left(n\right)) \times (\operatorname{\mathit{Fin}}\left(5\right)), (\forall c: \operatorname{\mathit{Fin}}\left(3\right), ((c < A\left(p\right)) \implies (\exists q: (\operatorname{\mathit{Fin}}\left(n\right)) \times (\operatorname{\mathit{Fin}}\left(5\right)), ((\operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(\operatorname{\mathit{Prod}}.\operatorname{\mathit{fst}}\left(q\right)\right) \cdot 5 + \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(\operatorname{\mathit{Prod}}.\operatorname{\mathit{snd}}\left(q\right)\right) < \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(\operatorname{\mathit{Prod}}.\operatorname{\mathit{fst}}\left(p\right)\right) \cdot 5 + \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(\operatorname{\mathit{Prod}}.\operatorname{\mathit{snd}}\left(p\right)\right)) \land (A\left(q\right) = c))))))), \operatorname{\mathit{Finset}}.\operatorname{\mathit{univ}}\right)\right))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/HardinA229634Strip.a` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229634: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229634>.

*Commentary.*

The filter ranges over every actual array over Fin 3. Canonical uses the lifted row-major order, independently of the transfer sweep. Each listed bond contributes exactly one when its two endpoint colours agree.

**Theorem 1.2 (The registered all-index recurrence).**

$$\forall n: \operatorname{\mathit{Nat}}, ((\operatorname{\mathit{HardinA229634Strip}}.\operatorname{a}\left(n + 21\right): \operatorname{\mathit{Int}}) = 42 \cdot (\operatorname{\mathit{HardinA229634Strip}}.\operatorname{a}\left(n + 20\right): \operatorname{\mathit{Int}}) - 723 \cdot (\operatorname{\mathit{HardinA229634Strip}}.\operatorname{a}\left(n + 19\right): \operatorname{\mathit{Int}}) + 6569 \cdot (\operatorname{\mathit{HardinA229634Strip}}.\operatorname{a}\left(n + 18\right): \operatorname{\mathit{Int}}) - 33687 \cdot (\operatorname{\mathit{HardinA229634Strip}}.\operatorname{a}\left(n + 17\right): \operatorname{\mathit{Int}}) + 94839 \cdot (\operatorname{\mathit{HardinA229634Strip}}.\operatorname{a}\left(n + 16\right): \operatorname{\mathit{Int}}) - 116010 \cdot (\operatorname{\mathit{HardinA229634Strip}}.\operatorname{a}\left(n + 15\right): \operatorname{\mathit{Int}}) - 55215 \cdot (\operatorname{\mathit{HardinA229634Strip}}.\operatorname{a}\left(n + 14\right): \operatorname{\mathit{Int}}) + 305043 \cdot (\operatorname{\mathit{HardinA229634Strip}}.\operatorname{a}\left(n + 13\right): \operatorname{\mathit{Int}}) - 230994 \cdot (\operatorname{\mathit{HardinA229634Strip}}.\operatorname{a}\left(n + 12\right): \operatorname{\mathit{Int}}) - 118011 \cdot (\operatorname{\mathit{HardinA229634Strip}}.\operatorname{a}\left(n + 11\right): \operatorname{\mathit{Int}}) + 243513 \cdot (\operatorname{\mathit{HardinA229634Strip}}.\operatorname{a}\left(n + 10\right): \operatorname{\mathit{Int}}) - 84933 \cdot (\operatorname{\mathit{HardinA229634Strip}}.\operatorname{a}\left(n + 9\right): \operatorname{\mathit{Int}}) - 40719 \cdot (\operatorname{\mathit{HardinA229634Strip}}.\operatorname{a}\left(n + 8\right): \operatorname{\mathit{Int}}) + 42804 \cdot (\operatorname{\mathit{HardinA229634Strip}}.\operatorname{a}\left(n + 7\right): \operatorname{\mathit{Int}}) - 14887 \cdot (\operatorname{\mathit{HardinA229634Strip}}.\operatorname{a}\left(n + 6\right): \operatorname{\mathit{Int}}) + 2598 \cdot (\operatorname{\mathit{HardinA229634Strip}}.\operatorname{a}\left(n + 5\right): \operatorname{\mathit{Int}}) - 228 \cdot (\operatorname{\mathit{HardinA229634Strip}}.\operatorname{a}\left(n + 4\right): \operatorname{\mathit{Int}}) + 8 \cdot (\operatorname{\mathit{HardinA229634Strip}}.\operatorname{a}\left(n + 3\right): \operatorname{\mathit{Int}}))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/HardinA229634Strip.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229634: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229634>.

*Commentary.*

The recurrence is an identity in the integers at every index at least 21. DefectTransfer.lumped_count and forward_shift propagate the finite certificate. The literal row-major canonical representative is independent of the row sweep. canonical_pattern_card supplies the factor six in the range used here, where a constant array cannot have the prescribed defect count. This is a finite combinatorial count and makes no thermodynamic-limit claim.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/HardinA229634Strip.a`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/HardinA229634Strip.result`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177Canonical](../../../Combinatorics/TraceAvoidingArrays/HardinA233177Canonical.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229531StripData](../CrossedStripDefects/HardinA229531StripData.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/HardinA229634StripClasses](HardinA229634StripClasses.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/HardinA229634StripData](HardinA229634StripData.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/DefectTransfer](../StripDefects/DefectTransfer.md)
