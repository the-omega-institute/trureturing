# Hardin A229536: exact defect recurrence

## Abstract

Literal HDA colourings and exact defect transfer.

Exactly 1 monochromatic HDA bonds are allowed. The proper transitions and initial class sizes apply HardinColumnContinuations.column_certificate after the exact bond, budget and class cut and natural-to-integer cast. A transfer letter has 3 cells, swept by columns. Its bond sets are the internal horizontal edges and both diagonals between rows; for the column sweep all horizontal and diagonal edges join successive columns. The 8-state matrix is indexed by remaining budget and equality pattern modulo reflection. Every proper-row diagonal block uses HardinColumnContinuations.Hfull. The finite certificate fixes each entry, initialization, terminal vector and forward polynomial identity.

**Definition 1.1 (Between-column bonds).**

$$(\operatorname{\mathit{HardinA229536Strip}}.\operatorname{\mathit{between}}: \operatorname{\mathit{Finset}}\left((\operatorname{\mathit{Fin}}\left(3\right)) \times (\operatorname{\mathit{Fin}}\left(3\right))\right)) = \{(0, 0), (0, 1), (1, 0), (1, 1), (1, 2), (2, 1), (2, 2)\}$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229536Strip.between` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229536: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229536>.

*Commentary.*

The seven ordered bonds join consecutive columns of the three-cell transfer letter.

**Definition 1.2 (The literal canonical array count).**

$$\forall n: \mathit{Nat}, (\operatorname{\mathit{HardinA229536Strip}}.\operatorname{a}\left(n\right) = \operatorname{\mathit{Finset}}.\operatorname{\mathit{card}}\left(\operatorname{\mathit{Finset}}.\operatorname{\mathit{filter}}\left(\lambda A: ((\operatorname{\mathit{Fin}}\left(3\right)) \times (\operatorname{\mathit{Fin}}\left(n\right))) \to (\operatorname{\mathit{Fin}}\left(3\right)) \mapsto ((\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{defects}}\left(\operatorname{\mathit{HardinA229588Strip}}.\operatorname{\mathit{horizontal}}, \operatorname{\mathit{HardinA229536Strip}}.\operatorname{\mathit{between}}, \operatorname{\mathit{List}}.\operatorname{\mathit{ofFn}}\left(\lambda j: \operatorname{\mathit{Fin}}\left(n\right) \mapsto (\lambda i: \operatorname{\mathit{Fin}}\left(3\right) \mapsto (A\left((i, j)\right)))\right)\right) = 1) \land (\forall p: (\operatorname{\mathit{Fin}}\left(3\right)) \times (\operatorname{\mathit{Fin}}\left(n\right)), (\forall c: \operatorname{\mathit{Fin}}\left(3\right), ((c < A\left(p\right)) \implies (\exists q: (\operatorname{\mathit{Fin}}\left(3\right)) \times (\operatorname{\mathit{Fin}}\left(n\right)), ((\operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(\operatorname{\mathit{Prod}}.\operatorname{\mathit{fst}}\left(q\right)\right) \cdot n + \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(\operatorname{\mathit{Prod}}.\operatorname{\mathit{snd}}\left(q\right)\right) < \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(\operatorname{\mathit{Prod}}.\operatorname{\mathit{fst}}\left(p\right)\right) \cdot n + \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(\operatorname{\mathit{Prod}}.\operatorname{\mathit{snd}}\left(p\right)\right)) \land (A\left(q\right) = c))))))), \operatorname{\mathit{Finset}}.\operatorname{\mathit{univ}}\right)\right))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229536Strip.a` (`✓ std3`).

*Citation.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229536: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229536>.

*Commentary.*

The filter ranges over every actual array over Fin 3. Canonical uses the lifted row-major order, independently of the transfer sweep. Each listed bond contributes exactly one when its two endpoint colours agree.

**Theorem 1.3 (The registered all-index recurrence).**

$$\forall n: \mathit{Nat}, ((\operatorname{\mathit{HardinA229536Strip}}.\operatorname{a}\left(n + 9\right): \operatorname{\mathit{Int}}) = 6 \cdot (\operatorname{\mathit{HardinA229536Strip}}.\operatorname{a}\left(n + 8\right): \operatorname{\mathit{Int}}) - 1 \cdot (\operatorname{\mathit{HardinA229536Strip}}.\operatorname{a}\left(n + 7\right): \operatorname{\mathit{Int}}) - 28 \cdot (\operatorname{\mathit{HardinA229536Strip}}.\operatorname{a}\left(n + 6\right): \operatorname{\mathit{Int}}) - 4 \cdot (\operatorname{\mathit{HardinA229536Strip}}.\operatorname{a}\left(n + 5\right): \operatorname{\mathit{Int}}) + 16 \cdot (\operatorname{\mathit{HardinA229536Strip}}.\operatorname{a}\left(n + 4\right): \operatorname{\mathit{Int}}) - 4 \cdot (\operatorname{\mathit{HardinA229536Strip}}.\operatorname{a}\left(n + 3\right): \operatorname{\mathit{Int}}))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229536Strip.result` (`✓ std3`). ∎

*Resolves.* `Problems/hardin229536` (proved) by `D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229536Strip.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"hardin229536","declaration_gid":"D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229536Strip.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229536: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229536>.

*Commentary.*

For every natural n, the recurrence holds at index n+9, hence at every index at least 9. The exact-budget transfer uses 8 classes. Its zero-temperature entries call the published owner; finite defect counts, forward iterates and a polynomial relation feed DefectTransfer.lumped_count and forward_shift. The colour-permutation action is free once two colours occur; canonical_pattern_card supplies the factor six. The nonconstant premise is proved in the range used by the recurrence. This is a statement about finite canonical counts, without a thermodynamic-limit assertion.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229536Strip.a`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229536Strip.between`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229536Strip.result`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177Canonical](../../../Combinatorics/TraceAvoidingArrays/HardinA233177Canonical.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinColumnContinuations](../../../Combinatorics/TraceAvoidingArrays/HardinColumnContinuations.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/DefectTransfer](../StripDefects/DefectTransfer.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229588Strip](../StripDefects/HardinA229588Strip.md)
