# Information-Escape Theorem Units

## Abstract

Typed primitive realizations compile theorem laws into finite executable catalogs.

**Definition 1.1 (Primitive signature).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/TheoremUnit.PrimitiveSignature`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/TheoremUnit.PrimitiveSignature` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A signature records typed readouts and separately indexed point anchors.

**Definition 1.2 (Primitive realization).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/TheoremUnit.PrimitiveRealization`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/TheoremUnit.PrimitiveRealization` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A realization supplies every typed readout and every anchor point.

**Definition 1.3 (Realization bundle).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/TheoremUnit.toPrimitiveBundle`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/TheoremUnit.toPrimitiveBundle` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Readouts compile to CUT atoms while points compile to ANCHOR atoms.

**Theorem 1.4 (Compiled agreement has the typed signature semantics).**

$$\operatorname{agrees}(\operatorname{toPrimitiveBundle}(r), x, y) \iff (\forall i, \operatorname{readout}(r, i, x) = \operatorname{readout}(r, i, y)) \land (\forall j, (x = \operatorname{anchor}(r, j) \iff y = \operatorname{anchor}(r, j))).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/TheoremUnit.toPrimitiveBundle_agrees_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The sum-indexed bundle agrees exactly when all readouts match and all point-anchor tests match.

**Theorem 1.5 (Boolean ADMIT readout reflection).**

$$\operatorname{decide}(\operatorname{A}(a)) = true \iff \operatorname{A}(a).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/TheoremUnit.admit_readout_eq_true_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Deciding the admission predicate yields true exactly when the predicate holds.

**Definition 1.6 (Theorem unit).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/TheoremUnit.TheoremUnit`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/TheoremUnit.TheoremUnit` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A theorem unit pairs a proved statement with its object-level primitive bundle.

**Definition 1.7 (Primitive-law arena).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/TheoremUnit.PrimitiveLawArena`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/TheoremUnit.PrimitiveLawArena` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A primitive-law arena extends a finite arena with a typed signature and laws over its realizations.

**Definition 1.8 (Native theorem unit).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/TheoremUnit.NativeTheoremUnit`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/TheoremUnit.NativeTheoremUnit` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A native unit proves the arena law directly for its realization.

**Definition 1.9 (Legacy primitive realization).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/TheoremUnit.LegacyPrimitiveRealization`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/TheoremUnit.LegacyPrimitiveRealization` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A legacy realization proves equivalence between an existing statement and its primitive law.

**Definition 1.10 (Theorem catalog).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/TheoremUnit.Catalog`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/TheoremUnit.Catalog` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A catalog is a finite decidable index of theorem units over one arena.

**Definition 1.11 (Catalog from a vector).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/TheoremUnit.ofVector`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/TheoremUnit.ofVector` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A Fin-indexed vector is the canonical fixed-length catalog constructor.

**Definition 1.12 (Full index set).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/TheoremUnit.fullIndexSet`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/TheoremUnit.fullIndexSet` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The full catalog selection is the universal finite set.

**Definition 1.13 (Leave-one-out set).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/TheoremUnit.without`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/TheoremUnit.without` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The leave-one-out set erases one theorem from the full selection.

**Theorem 1.14 (Leave-one-out membership).**

$$candidate \in \operatorname{without}(catalog, removed) \iff candidate \neq removed.$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/TheoremUnit.mem_without_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A candidate belongs to the leave-one-out set exactly when it differs from the removed index.

**Theorem 1.15 (Leave-one-out cardinality).**

$$\operatorname{card}(\operatorname{without}(catalog, i)) = \operatorname{card}(\operatorname{Index}(catalog)) - 1.$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/TheoremUnit.without_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Erasing a member of the universal finite set subtracts exactly one from its cardinality.

**Theorem 1.16 (Vector catalog lookup).**

$$\operatorname{theoremAt}(\operatorname{ofVector}(units), i) = \operatorname{units}(i).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/TheoremUnit.theoremAt_ofVector` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Lookup in a vector-backed catalog reduces to the supplied vector function.

## References

- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/TheoremUnit.Catalog`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/TheoremUnit.LegacyPrimitiveRealization`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/TheoremUnit.NativeTheoremUnit`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/TheoremUnit.PrimitiveLawArena`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/TheoremUnit.PrimitiveRealization`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/TheoremUnit.PrimitiveSignature`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/TheoremUnit.TheoremUnit`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/TheoremUnit.admit_readout_eq_true_iff`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/TheoremUnit.fullIndexSet`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/TheoremUnit.mem_without_iff`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/TheoremUnit.ofVector`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/TheoremUnit.theoremAt_ofVector`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/TheoremUnit.toPrimitiveBundle`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/TheoremUnit.toPrimitiveBundle_agrees_iff`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/TheoremUnit.without`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/TheoremUnit.without_card`
- Dependency: [D5/S3/ConceptDynamics/CIRPT/PrimitiveBundle](../CIRPT/PrimitiveBundle.md)
- Dependency: [D5/S3/ConceptDynamics/InformationEscape/Arena](Arena.md)
