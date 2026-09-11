# Finite Domain Selection Refutation

## Abstract

Support pruning and complete finite branching preserve all shared table-selection solutions and soundly certify their absence at arbitrary finite color capacity.

**Definition 1.1 (Assignment).**

Lean statement: `D5/S0/Certificates/FiniteDomainSelectionRefutation.Assignment`

*Formalization.* `D5/S0/Certificates/FiniteDomainSelectionRefutation.Assignment` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A finite assignment into an arbitrary finite color carrier.

**Definition 1.2 (Domains).**

Lean statement: `D5/S0/Certificates/FiniteDomainSelectionRefutation.Domains`

*Formalization.* `D5/S0/Certificates/FiniteDomainSelectionRefutation.Domains` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Allowed values for every transition-table or trace variable at the chosen finite color capacity.

**Definition 1.3 (InDomains).**

Lean statement: `D5/S0/Certificates/FiniteDomainSelectionRefutation.InDomains`

*Formalization.* `D5/S0/Certificates/FiniteDomainSelectionRefutation.InDomains` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

All coordinates of an assignment remain inside the current domains.

**Definition 1.4 (Selection).**

Lean statement: `D5/S0/Certificates/FiniteDomainSelectionRefutation.Selection`

*Formalization.* `D5/S0/Certificates/FiniteDomainSelectionRefutation.Selection` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A shared transition table is selected by the finite color of the parent node.

**Definition 1.5 (restrict).**

Lean statement: `D5/S0/Certificates/FiniteDomainSelectionRefutation.restrict`

*Formalization.* `D5/S0/Certificates/FiniteDomainSelectionRefutation.restrict` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Intersect one domain, leaving the other coordinates unchanged.

**Theorem 1.6 (restrict_preserves).**

Lean statement: `D5/S0/Certificates/FiniteDomainSelectionRefutation.restrict_preserves`

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/FiniteDomainSelectionRefutation.restrict_preserves` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Restriction is sound whenever the actual value is among the allowed ones.

**Definition 1.7 (pruneParent).**

Lean statement: `D5/S0/Certificates/FiniteDomainSelectionRefutation.pruneParent`

*Formalization.* `D5/S0/Certificates/FiniteDomainSelectionRefutation.pruneParent` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Remove parent values lacking any compatible transition target.

**Definition 1.8 (pruneChild).**

Lean statement: `D5/S0/Certificates/FiniteDomainSelectionRefutation.pruneChild`

*Formalization.* `D5/S0/Certificates/FiniteDomainSelectionRefutation.pruneChild` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Remove child values lacking a compatible parent and table entry.

**Definition 1.9 (pruneRow).**

Lean statement: `D5/S0/Certificates/FiniteDomainSelectionRefutation.pruneRow`

*Formalization.* `D5/S0/Certificates/FiniteDomainSelectionRefutation.pruneRow` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

When the parent has one value, intersect that table row with the child.

**Theorem 1.10 (pruneParent_preserves).**

Lean statement: `D5/S0/Certificates/FiniteDomainSelectionRefutation.pruneParent_preserves`

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/FiniteDomainSelectionRefutation.pruneParent_preserves` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Removing an unsupported parent never removes a satisfying assignment.

**Theorem 1.11 (pruneChild_preserves).**

Lean statement: `D5/S0/Certificates/FiniteDomainSelectionRefutation.pruneChild_preserves`

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/FiniteDomainSelectionRefutation.pruneChild_preserves` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Removing an unsupported child never removes a satisfying assignment.

**Theorem 1.12 (pruneRow_preserves).**

Lean statement: `D5/S0/Certificates/FiniteDomainSelectionRefutation.pruneRow_preserves`

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/FiniteDomainSelectionRefutation.pruneRow_preserves` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A singleton-parent table-row intersection is also solution preserving.

**Definition 1.13 (Instruction).**

Lean statement: `D5/S0/Certificates/FiniteDomainSelectionRefutation.Instruction`

*Formalization.* `D5/S0/Certificates/FiniteDomainSelectionRefutation.Instruction` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A pruning instruction names an existing constraint, never a new premise.

**Definition 1.14 (applyInstruction).**

Lean statement: `D5/S0/Certificates/FiniteDomainSelectionRefutation.applyInstruction`

*Formalization.* `D5/S0/Certificates/FiniteDomainSelectionRefutation.applyInstruction` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Executable semantics of one support-pruning instruction.

**Theorem 1.15 (instruction_preserves).**

Lean statement: `D5/S0/Certificates/FiniteDomainSelectionRefutation.instruction_preserves`

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/FiniteDomainSelectionRefutation.instruction_preserves` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every permitted instruction preserves every genuine solution.

**Definition 1.16 (applySchedule).**

Lean statement: `D5/S0/Certificates/FiniteDomainSelectionRefutation.applySchedule`

*Formalization.* `D5/S0/Certificates/FiniteDomainSelectionRefutation.applySchedule` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Replay an arbitrary finite pruning schedule. A fixed-point hypothesis is unnecessary for soundness, so scheduling and early stopping remain untrusted.

**Theorem 1.17 (schedule_preserves).**

Lean statement: `D5/S0/Certificates/FiniteDomainSelectionRefutation.schedule_preserves`

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/FiniteDomainSelectionRefutation.schedule_preserves` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Soundness is independent of the choice and order of pruning instructions.

**Definition 1.18 (Refutation).**

Lean statement: `D5/S0/Certificates/FiniteDomainSelectionRefutation.Refutation`

*Formalization.* `D5/S0/Certificates/FiniteDomainSelectionRefutation.Refutation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Finite proof trees retain one child for every finite color. A child is skipped only when its value is absent from the current domain.

**Definition 1.19 (check).**

Lean statement: `D5/S0/Certificates/FiniteDomainSelectionRefutation.check`

*Formalization.* `D5/S0/Certificates/FiniteDomainSelectionRefutation.check` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The checker accepts only an empty-domain leaf or every feasible color branch. It does not accept an external UNSAT flag as a premise.

**Theorem 1.20 (accepted_refutation_excludes_solution).**

Lean statement: `D5/S0/Certificates/FiniteDomainSelectionRefutation.accepted_refutation_excludes_solution`

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/FiniteDomainSelectionRefutation.accepted_refutation_excludes_solution` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Accepted finite refutations exclude every assignment satisfying both the original domains and all shared transition equations at any finite color capacity.

## References

- Truth anchor: `D5/S0/Certificates/FiniteDomainSelectionRefutation.Assignment`
- Truth anchor: `D5/S0/Certificates/FiniteDomainSelectionRefutation.Domains`
- Truth anchor: `D5/S0/Certificates/FiniteDomainSelectionRefutation.InDomains`
- Truth anchor: `D5/S0/Certificates/FiniteDomainSelectionRefutation.Instruction`
- Truth anchor: `D5/S0/Certificates/FiniteDomainSelectionRefutation.Refutation`
- Truth anchor: `D5/S0/Certificates/FiniteDomainSelectionRefutation.Selection`
- Truth anchor: `D5/S0/Certificates/FiniteDomainSelectionRefutation.accepted_refutation_excludes_solution`
- Truth anchor: `D5/S0/Certificates/FiniteDomainSelectionRefutation.applyInstruction`
- Truth anchor: `D5/S0/Certificates/FiniteDomainSelectionRefutation.applySchedule`
- Truth anchor: `D5/S0/Certificates/FiniteDomainSelectionRefutation.check`
- Truth anchor: `D5/S0/Certificates/FiniteDomainSelectionRefutation.instruction_preserves`
- Truth anchor: `D5/S0/Certificates/FiniteDomainSelectionRefutation.pruneChild`
- Truth anchor: `D5/S0/Certificates/FiniteDomainSelectionRefutation.pruneChild_preserves`
- Truth anchor: `D5/S0/Certificates/FiniteDomainSelectionRefutation.pruneParent`
- Truth anchor: `D5/S0/Certificates/FiniteDomainSelectionRefutation.pruneParent_preserves`
- Truth anchor: `D5/S0/Certificates/FiniteDomainSelectionRefutation.pruneRow`
- Truth anchor: `D5/S0/Certificates/FiniteDomainSelectionRefutation.pruneRow_preserves`
- Truth anchor: `D5/S0/Certificates/FiniteDomainSelectionRefutation.restrict`
- Truth anchor: `D5/S0/Certificates/FiniteDomainSelectionRefutation.restrict_preserves`
- Truth anchor: `D5/S0/Certificates/FiniteDomainSelectionRefutation.schedule_preserves`
