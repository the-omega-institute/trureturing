# Identity and Jordan Full Group Trace

## Abstract

The identity and rational Jordan actions have trace two on every integer element.

**Theorem 1.1 (Every integer Jordan power has a linear upper-right entry).**

$$\forall m, \operatorname{act}\left(rhoUnipotent, m\right) = \operatorname{matrix2}\left(1, m, 0, 1\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Representation/IdentityJordanFullGroupTrace.rho_unipotent_integer_power` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The modular-group power formula is mapped entrywise from integers to rationals. Its generator is the existing rational Jordan unit, so the cyclic action at m has upper-right entry m.

**Theorem 1.2 (Both traces equal two on the full integer group).**

$$\forall m, \operatorname{trace}\left(\operatorname{act}\left(rhoUnipotent, m\right)\right) = 2 \land \operatorname{trace}\left(\operatorname{act}\left(rhoZero, m\right)\right) = 2$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Representation/IdentityJordanFullGroupTrace.full_group_trace_two` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The integer power formula leaves both diagonal entries equal to one. The identity action has the same diagonal, so both traces are two for every integer group element.

**Theorem 1.3 (Exponent zero collapses both actions to identity).**

$$\operatorname{act}\left(rhoUnipotent, 0\right) = \operatorname{identityMatrix}\left(2\right) \land \operatorname{act}\left(rhoUnipotent, 0\right) = \operatorname{act}\left(rhoZero, 0\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Representation/IdentityJordanFullGroupTrace.zero_exponent_audit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At m equal to zero, the off-diagonal entry vanishes. The Jordan action is the identity matrix and agrees with the constant identity representation.

**Theorem 1.4 (Negative one gives the inverse and preserves trace two).**

$$\operatorname{act}\left(rhoUnipotent, -1\right) = \operatorname{matrix2}\left(1, -1, 0, 1\right) \land \operatorname{trace}\left(\operatorname{act}\left(rhoUnipotent, -1\right)\right) = 2$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Representation/IdentityJordanFullGroupTrace.negative_exponent_audit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At m equal to negative one, the upper-right entry is negative one. This is the explicit inverse Jordan matrix, whose diagonal still has trace two.

**Theorem 1.5 (Full trace equality does not imply representation isomorphism).**

$$(\forall m, \operatorname{trace}\left(\operatorname{act}\left(rhoUnipotent, m\right)\right) = \operatorname{trace}\left(\operatorname{act}\left(rhoZero, m\right)\right)) \land \neg \operatorname{IsConj}\left(\operatorname{act}\left(rhoZero, cycleGenerator\right), \operatorname{act}\left(rhoUnipotent, cycleGenerator\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Representation/IdentityJordanFullGroupTrace.same_full_trace_but_not_isomorphic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The traces agree at every integer element, while the existing minimal polynomial argument proves the two generator matrices are not conjugate. Full character data therefore misses this extension.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Representation/IdentityJordanFullGroupTrace.full_group_trace_two`
- Truth anchor: `D5/S3/ConceptDynamics/Representation/IdentityJordanFullGroupTrace.negative_exponent_audit`
- Truth anchor: `D5/S3/ConceptDynamics/Representation/IdentityJordanFullGroupTrace.rho_unipotent_integer_power`
- Truth anchor: `D5/S3/ConceptDynamics/Representation/IdentityJordanFullGroupTrace.same_full_trace_but_not_isomorphic`
- Truth anchor: `D5/S3/ConceptDynamics/Representation/IdentityJordanFullGroupTrace.zero_exponent_audit`
- Dependency: [D5/S3/ConceptDynamics/Representation/IdentityJordanGeneratorContrast](IdentityJordanGeneratorContrast.md)
