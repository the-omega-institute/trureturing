# UniformNativeUnificationDomain

## Abstract

Original-domain native unification

A solver input is a natural-number domain size together with an ordered finite list of equations between finite binary trees. Leaves carry Boolean constants or natural-number variable indices. The solver returns outer none exactly when an occurring index lies outside the declared domain. A well-formed native failure returns some none. Success returns some of some of the original-domain bindings, in ascending index order, with the fully composed native substitution applied to each bound original variable.

The domain includes zero variables, empty equations, arbitrary finite trees, contradictions, aliases to unbound variables and every malformed finite input. These unification results alone do not construct a history materializer, a source-free service criterion or a stationary original service run.

**Definition 1.1 (Original index embedding).**

Lean statement: `D5/S0/Rewriting/UniformNativeUnificationDomain.liftTerm`

*Formalization.* `D5/S0/Rewriting/UniformNativeUnificationDomain.liftTerm` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The embedding changes each Fin index to its natural-number value and preserves Boolean leaves and ordered binary constructors.

**Definition 1.2 (Ordered equation embedding).**

Lean statement: `D5/S0/Rewriting/UniformNativeUnificationDomain.liftEquations`

*Formalization.* `D5/S0/Rewriting/UniformNativeUnificationDomain.liftEquations` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each equation is embedded without changing the list order, its two sides or repeated variable occurrences.

**Definition 1.3 (Occurrence range check).**

Lean statement: `D5/S0/Rewriting/UniformNativeUnificationDomain.inRange`

*Formalization.* `D5/S0/Rewriting/UniformNativeUnificationDomain.inRange` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every variable occurrence must be strictly below the declared domain size. Boolean leaves are always in range; both children of a binary node must be in range.

**Definition 1.4 (Finite-domain reconstruction).**

Lean statement: `D5/S0/Rewriting/UniformNativeUnificationDomain.lowerTerm`

*Formalization.* `D5/S0/Rewriting/UniformNativeUnificationDomain.lowerTerm` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every in-range natural-number variable becomes its original Fin index. Any out-of-range occurrence rejects the entire term.

**Definition 1.5 (Finite-domain equation reconstruction).**

Lean statement: `D5/S0/Rewriting/UniformNativeUnificationDomain.lowerEquations`

*Formalization.* `D5/S0/Rewriting/UniformNativeUnificationDomain.lowerEquations` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Reconstruction retains all equation and constructor order and rejects any malformed occurrence in either side of any equation.

**Definition 1.6 (Ascending native action projection).**

Lean statement: `D5/S0/Rewriting/UniformNativeUnificationDomain.project`

*Formalization.* `D5/S0/Rewriting/UniformNativeUnificationDomain.project` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The native key set filters the ascending original Fin domain. Each retained key is paired with its fully substituted native action, decoded into finite terms and embedded back into natural-number indices.

**Definition 1.7 (Total uniform solver).**

Lean statement: `D5/S0/Rewriting/UniformNativeUnificationDomain.F`

*Formalization.* `D5/S0/Rewriting/UniformNativeUnificationDomain.F` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The function rejects malformed finite inputs and otherwise executes the exact native unifier from its empty substitution. Native failure and native success remain distinct from malformed input.

**Theorem 1.8 (Universal native correspondence).**

Lean statement: `D5/S0/Rewriting/UniformNativeUnificationDomain.exact_native`

*Proof.* Machine-checked in Lean as `D5/S0/Rewriting/UniformNativeUnificationDomain.exact_native` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every domain size and every finite Fin-indexed equation list, the solver on the index embedding equals the exact native result projection. The equality uses the native solver's own branch and fully composed substitution action.

**Theorem 1.9 (Exact malformed-input rejection).**

Lean statement: `D5/S0/Rewriting/UniformNativeUnificationDomain.rejection_exact`

*Proof.* Machine-checked in Lean as `D5/S0/Rewriting/UniformNativeUnificationDomain.rejection_exact` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural-number domain size and every finite Nat-indexed equation list, the outer result is none if and only if at least one occurring index is outside the domain. A native unification failure never produces outer rejection.

**Definition 1.10 (Native tree coding).**

Lean statement: `D5/S0/Rewriting/UniformNativeUnificationDomain.nativeTerm`

*Formalization.* `D5/S0/Rewriting/UniformNativeUnificationDomain.nativeTerm` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Boolean leaves and ordered binary nodes use the existing native constructors. An ordinal variable uses the exact native finName of its natural-number index.

**Theorem 1.11 (Exact term reconstruction range).**

Lean statement: `D5/S0/Rewriting/UniformNativeUnificationDomain.lower_range`

*Proof.* Machine-checked in Lean as `D5/S0/Rewriting/UniformNativeUnificationDomain.lower_range` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every domain size and finite term, reconstruction succeeds exactly when every variable occurrence is in range. The retained computability implementation uses this original helper to validate clipped terms.

**Theorem 1.12 (Exact equation reconstruction range).**

Lean statement: `D5/S0/Rewriting/UniformNativeUnificationDomain.lower_equations_range`

*Proof.* Machine-checked in Lean as `D5/S0/Rewriting/UniformNativeUnificationDomain.lower_equations_range` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every domain size and ordered finite equation list, reconstruction succeeds exactly when both sides of every equation are in range. The retained encoded solver uses this original helper for its malformed-input branches.

## References

- Truth anchor: `D5/S0/Rewriting/UniformNativeUnificationDomain.F`
- Truth anchor: `D5/S0/Rewriting/UniformNativeUnificationDomain.exact_native`
- Truth anchor: `D5/S0/Rewriting/UniformNativeUnificationDomain.inRange`
- Truth anchor: `D5/S0/Rewriting/UniformNativeUnificationDomain.liftEquations`
- Truth anchor: `D5/S0/Rewriting/UniformNativeUnificationDomain.liftTerm`
- Truth anchor: `D5/S0/Rewriting/UniformNativeUnificationDomain.lowerEquations`
- Truth anchor: `D5/S0/Rewriting/UniformNativeUnificationDomain.lowerTerm`
- Truth anchor: `D5/S0/Rewriting/UniformNativeUnificationDomain.lower_equations_range`
- Truth anchor: `D5/S0/Rewriting/UniformNativeUnificationDomain.lower_range`
- Truth anchor: `D5/S0/Rewriting/UniformNativeUnificationDomain.nativeTerm`
- Truth anchor: `D5/S0/Rewriting/UniformNativeUnificationDomain.project`
- Truth anchor: `D5/S0/Rewriting/UniformNativeUnificationDomain.rejection_exact`
- Dependency: [D5/S0/Computability/PreorderTreeEvaluation](../Computability/PreorderTreeEvaluation.md)
- Dependency: [D5/S0/Rewriting/UnificationFuel](UnificationFuel.md)
