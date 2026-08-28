# Role-Ledger Prefix Stability

## Abstract

A valid role ledger rejects events unseen at their own index, and events appended strictly after a frozen decision cannot alter its adjudication prefix.

**Theorem 1.1 (An unseen recorded event invalidates the whole trace).**

$$\left(e \in \operatorname{events}(L) \land \left(\neg \operatorname{evidence}(e) \in \operatorname{seen}(F, \operatorname{eventId}(e))\right)\right) \Rightarrow \left(\neg \operatorname{ValidRoleTrace}(L, F)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DefinitionEscapeAdjudication/RoleLedgerPrefixStability.invalid_trace_of_unseen_recorded_event` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

ValidRoleTrace universally binds every recorded event to the evidence visible at that event's own identifier. A recorded counterexample therefore negates the whole trace; no consumer can recover validity by silently dropping that event.

**Theorem 1.2 (A post-decision append preserves the frozen three-coordinate prefix).**

$$\forall F, L, LNew, d, n, \tau, \left(\operatorname{ValidRoleTrace}(L, F) \land \left(\operatorname{ValidRoleTrace}(LNew, F) \land \operatorname{AppendOnlyRoleExtension}(L, LNew, d)\right)\right) \Rightarrow \operatorname{AdjudicationRolePrefix}(LNew, d, n, \tau) = \operatorname{AdjudicationRolePrefix}(L, d, n, \tau).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DefinitionEscapeAdjudication/RoleLedgerPrefixStability.append_only_adjudication_role_prefix_unchanged` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The full RoleUseEvent stores a unique event identifier, evidence, round, role, dependencies, protocol, and physical time. The ledger requires unique strictly ordered identifiers and monotone round and time coordinates. RolesAtInPrefix remains a relational set, so separate uses of the same record are not collapsed.

AdjudicationRolePrefix simultaneously restricts event identifier, round, and time. AppendOnlyRoleExtension exposes a literal list tail and proves every tail identifier is strictly greater than the old decision identifier.

List membership in the extended ledger splits between the old list and the tail. The tail case contradicts the prefix's at-or-before decision bound, while old events embed into the append. This proves set equality of the full frozen prefix under valid old and new trace hypotheses.

This discharges the reject-on-mismatch and append-only prefix-stability claims of definition-escape-completion-theory Part 48.2, atom generic-residual-ae65843df6a0e51d2e107e681bbcbfa35cd1bb922d011d85ece1c3f466fa444e. The source's semantic gloss for the five role names is represented by the constructors; no statistical independence or generalization claim is added.

## References

- Truth anchor: `D5/S3/ConceptDynamics/DefinitionEscapeAdjudication/RoleLedgerPrefixStability.append_only_adjudication_role_prefix_unchanged`
- Truth anchor: `D5/S3/ConceptDynamics/DefinitionEscapeAdjudication/RoleLedgerPrefixStability.invalid_trace_of_unseen_recorded_event`
