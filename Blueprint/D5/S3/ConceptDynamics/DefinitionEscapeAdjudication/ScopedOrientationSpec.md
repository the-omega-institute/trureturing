# Scoped Orientation Specification

## Abstract

An exogenous orientation specification induces a preorder on its admissible scope.

**Definition 1.1 (Orientation specification).**

Lean statement: `D5/S3/ConceptDynamics/DefinitionEscapeAdjudication/ScopedOrientationSpec.OrientationSpec`

*Formalization.* `D5/S3/ConceptDynamics/DefinitionEscapeAdjudication/ScopedOrientationSpec.OrientationSpec` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The specification stores an external relation, provenance, version, scope, and relation laws whose hypotheses explicitly consume eligibility and scope.

**Definition 1.2 (Admissible scoped target).**

Lean statement: `D5/S3/ConceptDynamics/DefinitionEscapeAdjudication/ScopedOrientationSpec.AdmissibleTarget`

*Formalization.* `D5/S3/ConceptDynamics/DefinitionEscapeAdjudication/ScopedOrientationSpec.AdmissibleTarget` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The operator domain is the subtype of targets that are both eligible for the fixed goal and members of the specification scope.

**Definition 1.3 (Orientation projection).**

Lean statement: `D5/S3/ConceptDynamics/DefinitionEscapeAdjudication/ScopedOrientationSpec.orient`

*Formalization.* `D5/S3/ConceptDynamics/DefinitionEscapeAdjudication/ScopedOrientationSpec.orient` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The orientation operator projects the external relation to two admissible scoped targets; an out-of-scope target cannot be passed to this operator.

**Theorem 1.4 (Scoped orientation is a preorder).**

$$\begin{gathered}\forall Goal, Target, Source, Version: \operatorname{Type},\\{}G: Goal, Eligible: Target \to \left(Goal \to Prop\right),\\{}spec: \operatorname{OrientationSpec}\left(Goal, Target, Source, Version, G, Eligible\right),\\{}(\forall a: \operatorname{AdmissibleTarget}\left(spec\right), \operatorname{orient}\left(spec, a, a\right)) \land\\{}(\forall a, b, c: \operatorname{AdmissibleTarget}\left(spec\right), \operatorname{orient}\left(spec, a, b\right) \Rightarrow \operatorname{orient}\left(spec, b, c\right) \Rightarrow \operatorname{orient}\left(spec, a, c\right)).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DefinitionEscapeAdjudication/ScopedOrientationSpec.scoped_orientation_is_preorder` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each admissible target carries the eligibility and scope witnesses required by the specification's reflexivity proof.

Three such targets similarly supply every premise of the external transitivity proof. The specification therefore induces a preorder without manufacturing the goal or any normative source.

**Definition 1.5 (Scoped preorder structure).**

Lean statement: `D5/S3/ConceptDynamics/DefinitionEscapeAdjudication/ScopedOrientationSpec.scopedPreorder`

*Formalization.* `D5/S3/ConceptDynamics/DefinitionEscapeAdjudication/ScopedOrientationSpec.scopedPreorder` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The proven relation laws are packaged as a Preorder on the admissible subtype.

## References

- Truth anchor: `D5/S3/ConceptDynamics/DefinitionEscapeAdjudication/ScopedOrientationSpec.AdmissibleTarget`
- Truth anchor: `D5/S3/ConceptDynamics/DefinitionEscapeAdjudication/ScopedOrientationSpec.OrientationSpec`
- Truth anchor: `D5/S3/ConceptDynamics/DefinitionEscapeAdjudication/ScopedOrientationSpec.orient`
- Truth anchor: `D5/S3/ConceptDynamics/DefinitionEscapeAdjudication/ScopedOrientationSpec.scopedPreorder`
- Truth anchor: `D5/S3/ConceptDynamics/DefinitionEscapeAdjudication/ScopedOrientationSpec.scoped_orientation_is_preorder`
