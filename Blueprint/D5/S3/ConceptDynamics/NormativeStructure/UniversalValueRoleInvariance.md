# Universal Values as Role Invariants

## Abstract

Structural value schemas survive role relabeling, while named privilege does not.

**Theorem 1.1 (The structural core is natural under role equivalence).**

$$\forall A, B: Type, e: \operatorname{Equiv}\left(A, B\right), N: \operatorname{InteractionNorm}\left(A\right),\\{}\operatorname{StructuralUniversalCore}\left(\operatorname{relabel}\left(e, N\right)\right) \iff \operatorname{StructuralUniversalCore}\left(N\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/NormativeStructure/UniversalValueRoleInvariance.structural_universal_core_is_role_natural` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An interaction norm carries separate permission, harm, and truthful-treatment relations. Its structural core conjoins equal standing, reciprocity, non-harm, and truthful treatment.

Relabeling transports every relation together through an equivalence of role carriers. The theorem proves that the entire conjunction holds after transport exactly when it held before transport.

Equal standing is the only clause requiring a conjugate permutation. The other three clauses transport their two role variables directly. No finiteness assumption or distinguished role is used.

This is formal universality, not a survey claim that every person or culture endorses these values. It also does not decide which real differences are morally irrelevant and may therefore be relabeled.

Relevant history, consent, need, or responsibility must be represented in the normative profile rather than erased as a role name. Repository search found adjacent symmetry and norm-separation results, but no existing declaration with this role-natural boundary.

**Lemma 1.2 (Role naturality yields universality).**

$$\forall A: Type, \operatorname{IsUniversalSchema}\left(\operatorname{StructuralUniversalCore}\left(A\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/NormativeStructure/UniversalValueRoleInvariance.structural_universal_core_is_universal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Specializing the carrier equivalence to a permutation proves that every role renaming preserves the structural core. This fixed-point property is the precise sense in which the four schemas are universal here.

**Lemma 1.3 (A fixed named privilege fails universality).**

$$\neg \operatorname{IsUniversalSchema}\left(\operatorname{NamedPrivilege}\left(false\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/NormativeStructure/UniversalValueRoleInvariance.named_privilege_is_not_universal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A two-role model permits every interaction initiated by the role named false. Before relabeling, that fixed name has the asserted privilege. Swapping false and true transports the permission relation but leaves the external favorite name fixed, so the privilege fails.

The countermodel separates structural values from identity-anchored preferences using the same universality test. Universality therefore comes from role-independent form, not from attaching a preferred outcome to a particular name.

## References

- Truth anchor: `D5/S3/ConceptDynamics/NormativeStructure/UniversalValueRoleInvariance.named_privilege_is_not_universal`
- Truth anchor: `D5/S3/ConceptDynamics/NormativeStructure/UniversalValueRoleInvariance.structural_universal_core_is_role_natural`
- Truth anchor: `D5/S3/ConceptDynamics/NormativeStructure/UniversalValueRoleInvariance.structural_universal_core_is_universal`
