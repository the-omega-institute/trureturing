# Hardin A229530: exact defect recurrence

## Abstract

Literal HDA colourings and exact defect transfer.

The literal array has n rows, 4 columns and exactly 1 monochromatic HDA bonds. Rows are swept by an exact-budget transfer with 10 equality-and-budget classes, identifying reflection. Every proper-row diagonal block calls the published zero-temperature owner. The frozen four_class_certificate supplies proper transitions through scanner_fibres at saturated Seen flags, an exact budget/class cut and division by sixteen. The remaining defective-source and defect-consuming entries are computed separately.

**Definition 1.1 (Shared between).**

Lean statement: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229530Strip.between`

*Formalization.* `D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229530Strip.between` (`✓ std3`).

*Citation.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229530: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229530>.

*Commentary.*

The exact HDA bonds between consecutive rows, shared with the two-defect extension.

**Definition 1.2 (Shared Valid).**

Lean statement: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229530Strip.Valid`

*Formalization.* `D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229530Strip.Valid` (`✓ std3`).

*Citation.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229530: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229530>.

*Commentary.*

The one-defect residual-budget domain, reused after subtracting one from the two-defect residual budget.

**Definition 1.3 (Shared cl).**

Lean statement: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229530Strip.cl`

*Formalization.* `D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229530Strip.cl` (`✓ std3`).

*Citation.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229530: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229530>.

*Commentary.*

The 10 equality-and-budget classes. The two-defect extension embeds this class index as its active leading sector.

**Definition 1.4 (Shared T).**

Lean statement: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229530Strip.T`

*Formalization.* `D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229530Strip.T` (`✓ std3`).

*Citation.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229530: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229530>.

*Commentary.*

The 10 by 10 exact integer transfer. The two-defect extension uses this matrix as its leading block.

**Definition 1.5 (Shared initial).**

Lean statement: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229530Strip.initial`

*Formalization.* `D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229530Strip.initial` (`✓ std3`).

*Citation.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229530: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229530>.

*Commentary.*

The raw labelled initial vector on Fin 10, shared as the leading initial sector.

**Definition 1.6 (Shared W).**

Lean statement: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229530Strip.W`

*Formalization.* `D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229530Strip.W` (`✓ std3`).

*Citation.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229530: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229530>.

*Commentary.*

The Fin 7 cached forward prefix on Fin 10, shared by the two-defect extension.

**Theorem 1.7 (Shared finite_certificate).**

Lean statement: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229530Strip.finite_certificate`

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229530Strip.finite_certificate` (`✓ std3`). ∎

*Citation.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229530: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229530>.

*Commentary.*

Exact terminal values, validity preservation, successor and initial counts, cached forward recurrence and polynomial relation. The two-defect extension reuses its active successor and initial projections.

**Theorem 1.8 (Proper successor counts from saturated scanner fibres).**

Lean statement: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229530Strip.raw_successors`

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229530Strip.raw_successors` (`✓ std3`). ∎

*Citation.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229530: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229530>.

*Commentary.*

At saturated Seen flags, sixteen times every actual proper three-colour successor count is the corresponding HardinSourceContinuations.M entry. The theorem applies the frozen four_class_certificate through scanner_fibres and preserves all target classes.

**Definition 1.9 (The literal canonical array count).**

$$\forall n: \mathit{Nat}, (\operatorname{\mathit{HardinA229530Strip}}.\operatorname{a}\left(n\right) = \operatorname{\mathit{Finset}}.\operatorname{\mathit{card}}\left(\operatorname{\mathit{Finset}}.\operatorname{\mathit{filter}}\left(\lambda A: ((\operatorname{\mathit{Fin}}\left(n\right)) \times (\operatorname{\mathit{Fin}}\left(4\right))) \to (\operatorname{\mathit{Fin}}\left(3\right)) \mapsto ((\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{defects}}\left(\operatorname{\mathit{HardinA229530Strip}}.\operatorname{\mathit{horizontal}}, \operatorname{\mathit{HardinA229530Strip}}.\operatorname{\mathit{between}}, \operatorname{\mathit{List}}.\operatorname{\mathit{ofFn}}\left(\lambda i: \operatorname{\mathit{Fin}}\left(n\right) \mapsto (\lambda j: \operatorname{\mathit{Fin}}\left(4\right) \mapsto (A\left((i, j)\right)))\right)\right) = 1) \land (\forall p: (\operatorname{\mathit{Fin}}\left(n\right)) \times (\operatorname{\mathit{Fin}}\left(4\right)), (\forall c: \operatorname{\mathit{Fin}}\left(3\right), ((c < A\left(p\right)) \implies (\exists q: (\operatorname{\mathit{Fin}}\left(n\right)) \times (\operatorname{\mathit{Fin}}\left(4\right)), ((\operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(\operatorname{\mathit{Prod}}.\operatorname{\mathit{fst}}\left(q\right)\right) \cdot 4 + \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(\operatorname{\mathit{Prod}}.\operatorname{\mathit{snd}}\left(q\right)\right) < \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(\operatorname{\mathit{Prod}}.\operatorname{\mathit{fst}}\left(p\right)\right) \cdot 4 + \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(\operatorname{\mathit{Prod}}.\operatorname{\mathit{snd}}\left(p\right)\right)) \land (A\left(q\right) = c))))))), \operatorname{\mathit{Finset}}.\operatorname{\mathit{univ}}\right)\right))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229530Strip.a` (`✓ std3`).

*Citation.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229530: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229530>.

*Commentary.*

The filter ranges over every actual array over Fin 3. Canonical uses the lifted row-major order, independently of the transfer sweep. Each listed bond contributes exactly one when its two endpoint colours agree.

**Theorem 1.10 (The registered all-index recurrence).**

$$\forall n: \mathit{Nat}, (\operatorname{\mathit{HardinA229530Strip}}.\operatorname{a}\left(n + 6\right) = 14 \cdot \operatorname{\mathit{HardinA229530Strip}}.\operatorname{a}\left(n + 5\right) - 57 \cdot \operatorname{\mathit{HardinA229530Strip}}.\operatorname{a}\left(n + 4\right) + 56 \cdot \operatorname{\mathit{HardinA229530Strip}}.\operatorname{a}\left(n + 3\right) - 16 \cdot \operatorname{\mathit{HardinA229530Strip}}.\operatorname{a}\left(n + 2\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229530Strip.result` (`✓ std3`). ∎

*Citation.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229530: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229530>.

*Commentary.*

The recurrence holds at every index at least 6. DefectTransfer.lumped_count and forward_shift propagate the finite certificate. The literal row-major canonical representative is independent of the row sweep. canonical_pattern_card supplies the factor six in the range used here, where a constant array cannot have the prescribed defect count. This is a finite combinatorial count and makes no thermodynamic-limit claim.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229530Strip.T`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229530Strip.Valid`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229530Strip.W`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229530Strip.a`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229530Strip.between`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229530Strip.cl`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229530Strip.finite_certificate`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229530Strip.initial`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229530Strip.raw_successors`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229530Strip.result`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177Canonical](../../../Combinatorics/TraceAvoidingArrays/HardinA233177Canonical.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255LiteralBridge](../../../Combinatorics/TraceAvoidingArrays/HardinA233255LiteralBridge.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinSourceContinuations](../../../Combinatorics/TraceAvoidingArrays/HardinSourceContinuations.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/DefectTransfer](../StripDefects/DefectTransfer.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229582Strip](../StripDefects/HardinA229582Strip.md)
