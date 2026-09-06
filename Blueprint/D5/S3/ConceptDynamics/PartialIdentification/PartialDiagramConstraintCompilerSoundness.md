# Partial-Diagram Constraint Compiler Soundness

## Abstract

Required edges, forbidden edges, and query-order admissibility compile to an exact finite support polytope over candidate causal completions.

A finite completion supplies a directed-edge table and a query-order compatibility judgment. The compiler introduces simplex rows and one zero-support row for every witnessed edge or order violation.

The generated linear system is exact. Its feasible vectors are precisely normalized nonnegative masses supported on completions compatible with the partial diagram and the query-implied causal order.

This support polytope has latent-completion mixture semantics. When one complete graph is a single global unknown object, completion-specific identified ranges must instead be combined by the completion-union construction.

**Theorem 1.1 (The compiled LP exactly characterizes admissible completion mixtures).**

Lean statement: `D5/S3/ConceptDynamics/PartialIdentification/PartialDiagramConstraintCompilerSoundness.feasible_iff_compatible_completion_mixture`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/PartialIdentification/PartialDiagramConstraintCompilerSoundness.feasible_iff_compatible_completion_mixture` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Nonnegativity and two normalization rows produce a probability law. Active violation rows force every inadmissible completion coordinate to zero. Conversely, an admissibly supported probability law satisfies every generated row.

**Theorem 1.2 (A deterministic completion witness is feasible exactly when it is admissible).**

Lean statement: `D5/S3/ConceptDynamics/PartialIdentification/PartialDiagramConstraintCompilerSoundness.pointMass_feasible_iff_admissible`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/PartialIdentification/PartialDiagramConstraintCompilerSoundness.pointMass_feasible_iff_admissible` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The unit mass concentrated on one completion passes the compiler exactly when that completion satisfies every required edge, every forbidden-edge exclusion, and the query-order condition.

**Theorem 1.3 (The support polytope is inhabited exactly when an admissible completion exists).**

Lean statement: `D5/S3/ConceptDynamics/PartialIdentification/PartialDiagramConstraintCompilerSoundness.compiled_problem_nonempty_iff_exists_admissible`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/PartialIdentification/PartialDiagramConstraintCompilerSoundness.compiled_problem_nonempty_iff_exists_admissible` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A normalized feasible mass has at least one nonzero support coordinate, which supplies an admissible completion. The reverse implication uses its point mass.

**Theorem 1.4 (Adding partial-graph information shrinks the compiled feasible set).**

Lean statement: `D5/S3/ConceptDynamics/PartialIdentification/PartialDiagramConstraintCompilerSoundness.feasible_antitone_under_refinement`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/PartialIdentification/PartialDiagramConstraintCompilerSoundness.feasible_antitone_under_refinement` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every completion supporting a stronger diagram also supports the weaker diagram. The same normalized mass therefore remains feasible after forgetting graph assertions.

**Theorem 1.5 (A weaker-diagram lower certificate remains valid after refinement).**

Lean statement: `D5/S3/ConceptDynamics/PartialIdentification/PartialDiagramConstraintCompilerSoundness.lower_bound_survives_refinement`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/PartialIdentification/PartialDiagramConstraintCompilerSoundness.lower_bound_survives_refinement` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Feasible-set inclusion transports any replayable rational lower certificate from a weaker partial diagram to every stronger one with the same completion semantics and query.

**Theorem 1.6 (A weaker-diagram upper certificate remains valid after refinement).**

Lean statement: `D5/S3/ConceptDynamics/PartialIdentification/PartialDiagramConstraintCompilerSoundness.upper_bound_survives_refinement`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/PartialIdentification/PartialDiagramConstraintCompilerSoundness.upper_bound_survives_refinement` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The dual monotonicity statement holds at the upper endpoint. Additional graph assertions cannot invalidate a universal upper bound proved on the larger feasible family.

## References

- Truth anchor: `D5/S3/ConceptDynamics/PartialIdentification/PartialDiagramConstraintCompilerSoundness.compiled_problem_nonempty_iff_exists_admissible`
- Truth anchor: `D5/S3/ConceptDynamics/PartialIdentification/PartialDiagramConstraintCompilerSoundness.feasible_antitone_under_refinement`
- Truth anchor: `D5/S3/ConceptDynamics/PartialIdentification/PartialDiagramConstraintCompilerSoundness.feasible_iff_compatible_completion_mixture`
- Truth anchor: `D5/S3/ConceptDynamics/PartialIdentification/PartialDiagramConstraintCompilerSoundness.lower_bound_survives_refinement`
- Truth anchor: `D5/S3/ConceptDynamics/PartialIdentification/PartialDiagramConstraintCompilerSoundness.pointMass_feasible_iff_admissible`
- Truth anchor: `D5/S3/ConceptDynamics/PartialIdentification/PartialDiagramConstraintCompilerSoundness.upper_bound_survives_refinement`
- Dependency: [D5/S3/ConceptDynamics/Causal/FiniteLinearCausalIdentification](../Causal/FiniteLinearCausalIdentification.md)
- Dependency: [D5/S3/ConceptDynamics/PartialIdentification/PartialGraphInformationOrder](PartialGraphInformationOrder.md)
