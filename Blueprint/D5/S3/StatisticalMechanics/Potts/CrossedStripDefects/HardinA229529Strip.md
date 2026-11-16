# Hardin A229529: exact defect recurrence

## Abstract

Literal HDA colourings and exact defect transfer.

The literal array has n rows, 3 columns and exactly 1 monochromatic HDA bonds. Rows are swept by an exact-budget transfer with 5 equality-and-budget classes, identifying reflection. Every proper-row diagonal block calls the published zero-temperature owner. Finite certificates check the exact image and every defect entry.

**Definition 1.1 (The literal canonical array count).**

$$\forall n: \mathit{Nat}, (\operatorname{\mathit{HardinA229529Strip}}.\operatorname{a}\left(n\right) = \operatorname{\mathit{Finset}}.\operatorname{\mathit{card}}\left(\operatorname{\mathit{Finset}}.\operatorname{\mathit{filter}}\left(\lambda A: ((\operatorname{\mathit{Fin}}\left(n\right)) \times (\operatorname{\mathit{Fin}}\left(3\right))) \to (\operatorname{\mathit{Fin}}\left(3\right)) \mapsto ((\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{defects}}\left(\operatorname{\mathit{HardinA229529Strip}}.\operatorname{\mathit{horizontal}}, \operatorname{\mathit{HardinA229529Strip}}.\operatorname{\mathit{between}}, \operatorname{\mathit{List}}.\operatorname{\mathit{ofFn}}\left(\lambda i: \operatorname{\mathit{Fin}}\left(n\right) \mapsto (\lambda j: \operatorname{\mathit{Fin}}\left(3\right) \mapsto (A\left((i, j)\right)))\right)\right) = 1) \land (\forall p: (\operatorname{\mathit{Fin}}\left(n\right)) \times (\operatorname{\mathit{Fin}}\left(3\right)), (\forall c: \operatorname{\mathit{Fin}}\left(3\right), ((c < A\left(p\right)) \implies (\exists q: (\operatorname{\mathit{Fin}}\left(n\right)) \times (\operatorname{\mathit{Fin}}\left(3\right)), ((\operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(\operatorname{\mathit{Prod}}.\operatorname{\mathit{fst}}\left(q\right)\right) \cdot 3 + \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(\operatorname{\mathit{Prod}}.\operatorname{\mathit{snd}}\left(q\right)\right) < \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(\operatorname{\mathit{Prod}}.\operatorname{\mathit{fst}}\left(p\right)\right) \cdot 3 + \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(\operatorname{\mathit{Prod}}.\operatorname{\mathit{snd}}\left(p\right)\right)) \land (A\left(q\right) = c))))))), \operatorname{\mathit{Finset}}.\operatorname{\mathit{univ}}\right)\right))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229529Strip.a` (`✓ std3`).

*Citation.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229529: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229529>.

*Commentary.*

The filter ranges over every actual array over Fin 3. Canonical uses the lifted row-major order, independently of the transfer sweep. Each listed bond contributes exactly one when its two endpoint colours agree.

**Theorem 1.2 (The registered all-index recurrence).**

$$\forall n: \mathit{Nat}, (\operatorname{\mathit{HardinA229529Strip}}.\operatorname{a}\left(n + 6\right) = 10 \cdot \operatorname{\mathit{HardinA229529Strip}}.\operatorname{a}\left(n + 5\right) - 29 \cdot \operatorname{\mathit{HardinA229529Strip}}.\operatorname{a}\left(n + 4\right) + 20 \cdot \operatorname{\mathit{HardinA229529Strip}}.\operatorname{a}\left(n + 3\right) - 4 \cdot \operatorname{\mathit{HardinA229529Strip}}.\operatorname{a}\left(n + 2\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229529Strip.result` (`✓ std3`). ∎

*Citation.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229529: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229529>.

*Commentary.*

The recurrence holds at every index at least 6. DefectTransfer.lumped_count and forward_shift propagate the finite certificate. The literal row-major canonical representative is independent of the row sweep. canonical_pattern_card supplies the factor six in the range used here, where a constant array cannot have the prescribed defect count. This is a finite combinatorial count and makes no thermodynamic-limit claim.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229529Strip.a`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229529Strip.result`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177Canonical](../../../Combinatorics/TraceAvoidingArrays/HardinA233177Canonical.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinThinGraphTransport](../../../Combinatorics/TraceAvoidingArrays/HardinThinGraphTransport.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/DefectTransfer](../StripDefects/DefectTransfer.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229581Strip](../StripDefects/HardinA229581Strip.md)
