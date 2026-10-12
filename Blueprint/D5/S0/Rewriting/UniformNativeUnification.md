# UniformNativeUnification

## Abstract

Uniform computable native unification

A solver input is a natural-number domain size together with an ordered finite list of equations between finite binary trees. Leaves carry Boolean constants or natural-number variable indices. The solver returns outer none exactly when an occurring index lies outside the declared domain. A well-formed native failure returns some none. Success returns some of some of the original-domain bindings, in ascending index order, with the fully composed native substitution applied to each bound original variable.

The finite-tree representation preserves constructor order, equation order, Boolean leaves and every repeated variable occurrence. A list representation of the native substitution preserves each original-key lookup. Fresh insertion composes the new binding into all old values. The bounded evaluator follows the existing native variable, occurs-check, constructor and alias branches. Its mutual simulation preserves the actual native substitution action; no alternative most-general unifier is substituted.

Primitive recursive tree folds compute substitution, variables, branch selection, range checking and output projection. A partial recursive code fixed point implements the bounded mutual evaluator. Fuel induction proves that its code evaluation is total at every fuel. The existing exact finite native simulation supplies termination for the unbounded first-finished search. Partial recursive search and this termination proof establish a total computable solver, with no uniform primitive recursive bound or complexity assertion.

The domain includes zero variables, empty equations, arbitrary finite trees, contradictions, aliases to unbound variables and every malformed finite input. These unification results alone do not construct a history materializer, a source-free service criterion or a stationary original service run.

**Definition 1.1 (Original index embedding).**

Lean statement: `D5/S0/Rewriting/UniformNativeUnification.liftTerm`

*Formalization.* `D5/S0/Rewriting/UniformNativeUnification.liftTerm` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The embedding changes each Fin index to its natural-number value and preserves Boolean leaves and ordered binary constructors.

**Definition 1.2 (Ordered equation embedding).**

Lean statement: `D5/S0/Rewriting/UniformNativeUnification.liftEquations`

*Formalization.* `D5/S0/Rewriting/UniformNativeUnification.liftEquations` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each equation is embedded without changing the list order, its two sides or repeated variable occurrences.

**Definition 1.3 (Occurrence range check).**

Lean statement: `D5/S0/Rewriting/UniformNativeUnification.inRange`

*Formalization.* `D5/S0/Rewriting/UniformNativeUnification.inRange` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every variable occurrence must be strictly below the declared domain size. Boolean leaves are always in range; both children of a binary node must be in range.

**Definition 1.4 (Finite-domain reconstruction).**

Lean statement: `D5/S0/Rewriting/UniformNativeUnification.lowerTerm`

*Formalization.* `D5/S0/Rewriting/UniformNativeUnification.lowerTerm` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every in-range natural-number variable becomes its original Fin index. Any out-of-range occurrence rejects the entire term.

**Definition 1.5 (Finite-domain equation reconstruction).**

Lean statement: `D5/S0/Rewriting/UniformNativeUnification.lowerEquations`

*Formalization.* `D5/S0/Rewriting/UniformNativeUnification.lowerEquations` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Reconstruction retains all equation and constructor order and rejects any malformed occurrence in either side of any equation.

**Definition 1.6 (Ascending native action projection).**

Lean statement: `D5/S0/Rewriting/UniformNativeUnification.project`

*Formalization.* `D5/S0/Rewriting/UniformNativeUnification.project` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The native key set filters the ascending original Fin domain. Each retained key is paired with its fully substituted native action, decoded into finite terms and embedded back into natural-number indices.

**Definition 1.7 (Total uniform solver).**

Lean statement: `D5/S0/Rewriting/UniformNativeUnification.F`

*Formalization.* `D5/S0/Rewriting/UniformNativeUnification.F` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The function rejects malformed finite inputs and otherwise executes the exact native unifier from its empty substitution. Native failure and native success remain distinct from malformed input.

**Theorem 1.8 (Universal native correspondence).**

Lean statement: `D5/S0/Rewriting/UniformNativeUnification.exact_native`

*Proof.* Machine-checked in Lean as `D5/S0/Rewriting/UniformNativeUnification.exact_native` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every domain size and every finite Fin-indexed equation list, the solver on the index embedding equals the exact native result projection. The equality uses the native solver's own branch and fully composed substitution action.

**Theorem 1.9 (Exact malformed-input rejection).**

Lean statement: `D5/S0/Rewriting/UniformNativeUnification.rejection_exact`

*Proof.* Machine-checked in Lean as `D5/S0/Rewriting/UniformNativeUnification.rejection_exact` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural-number domain size and every finite Nat-indexed equation list, the outer result is none if and only if at least one occurring index is outside the domain. A native unification failure never produces outer rejection.

**Definition 1.10 (Native tree coding).**

Lean statement: `D5/S0/Rewriting/UniformNativeUnification.nativeTerm`

*Formalization.* `D5/S0/Rewriting/UniformNativeUnification.nativeTerm` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Boolean leaves and ordered binary nodes use the existing native constructors. An ordinal variable uses the exact native finName of its natural-number index.

**Definition 1.11 (Finite composed action).**

Lean statement: `D5/S0/Rewriting/UniformNativeUnification.apply`

*Formalization.* `D5/S0/Rewriting/UniformNativeUnification.apply` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The finite substitution representation acts by original-key lookup on variables and structurally on Boolean and binary constructors.

**Definition 1.12 (Ordered variable occurrences).**

Lean statement: `D5/S0/Rewriting/UniformNativeUnification.vars`

*Formalization.* `D5/S0/Rewriting/UniformNativeUnification.vars` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The finite list retains all variable occurrences in left-to-right tree order, including repeated names.

**Definition 1.13 (Exact native lookup relation).**

Lean statement: `D5/S0/Rewriting/UniformNativeUnification.Represents`

*Formalization.* `D5/S0/Rewriting/UniformNativeUnification.Represents` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For each natural-number ordinal, native lookup equals the native encoding of the finite representation's lookup. Hash-bucket order has no role in this relation.

**Definition 1.14 (Composed fresh insertion).**

Lean statement: `D5/S0/Rewriting/UniformNativeUnification.insert`

*Formalization.* `D5/S0/Rewriting/UniformNativeUnification.insert` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A fresh original binding is inserted after its action has been composed into each prior value. The finite list retains the native first-lookup convention.

**Definition 1.15 (Coded bounded equation evaluation).**

Lean statement: `D5/S0/Rewriting/UniformNativeUnification.one`

*Formalization.* `D5/S0/Rewriting/UniformNativeUnification.one` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The finite representation follows the existing native one-equation evaluator at identical fuel, retaining equality, both variable orientations, occurs checks, aliases and constructor decomposition.

**Definition 1.16 (Coded bounded list evaluation).**

Lean statement: `D5/S0/Rewriting/UniformNativeUnification.core`

*Formalization.* `D5/S0/Rewriting/UniformNativeUnification.core` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The finite representation evaluates the ordered equation list at identical fuel and transfers each successful composed substitution to the remaining equations.

**Definition 1.17 (Exact bounded result relation).**

Lean statement: `D5/S0/Rewriting/UniformNativeUnification.Matches`

*Formalization.* `D5/S0/Rewriting/UniformNativeUnification.Matches` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Exhaustion matches exhaustion; failure matches the native error branch; success preserves every original-key lookup of the native substitution. Only the outer solver interface discards error payloads.

**Definition 1.18 (Finite tree case analysis).**

Lean statement: `D5/S0/Rewriting/UniformNativeUnification.view`

*Formalization.* `D5/S0/Rewriting/UniformNativeUnification.view` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The view separates a Boolean or variable leaf from an ordered pair of child trees.

**Theorem 1.19 (Uniform total computability).**

Lean statement: `D5/S0/Rewriting/UniformNativeUnification.computable_F`

*Proof.* Machine-checked in Lean as `D5/S0/Rewriting/UniformNativeUnification.computable_F` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The single solver function on all finite Nat-indexed equations is computable. Exact bounded simulation, finite native halting and encoded first-finished search establish this result for arbitrary domain sizes, with no supplied solver or normalization oracle.

## References

- Truth anchor: `D5/S0/Rewriting/UniformNativeUnification.F`
- Truth anchor: `D5/S0/Rewriting/UniformNativeUnification.Matches`
- Truth anchor: `D5/S0/Rewriting/UniformNativeUnification.Represents`
- Truth anchor: `D5/S0/Rewriting/UniformNativeUnification.apply`
- Truth anchor: `D5/S0/Rewriting/UniformNativeUnification.computable_F`
- Truth anchor: `D5/S0/Rewriting/UniformNativeUnification.core`
- Truth anchor: `D5/S0/Rewriting/UniformNativeUnification.exact_native`
- Truth anchor: `D5/S0/Rewriting/UniformNativeUnification.inRange`
- Truth anchor: `D5/S0/Rewriting/UniformNativeUnification.insert`
- Truth anchor: `D5/S0/Rewriting/UniformNativeUnification.liftEquations`
- Truth anchor: `D5/S0/Rewriting/UniformNativeUnification.liftTerm`
- Truth anchor: `D5/S0/Rewriting/UniformNativeUnification.lowerEquations`
- Truth anchor: `D5/S0/Rewriting/UniformNativeUnification.lowerTerm`
- Truth anchor: `D5/S0/Rewriting/UniformNativeUnification.nativeTerm`
- Truth anchor: `D5/S0/Rewriting/UniformNativeUnification.one`
- Truth anchor: `D5/S0/Rewriting/UniformNativeUnification.project`
- Truth anchor: `D5/S0/Rewriting/UniformNativeUnification.rejection_exact`
- Truth anchor: `D5/S0/Rewriting/UniformNativeUnification.vars`
- Truth anchor: `D5/S0/Rewriting/UniformNativeUnification.view`
- Dependency: [D5/S0/Computability/PreorderTreeEvaluation](../Computability/PreorderTreeEvaluation.md)
- Dependency: [D5/S0/Rewriting/UnificationFuel](UnificationFuel.md)
