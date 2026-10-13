# UniformNativeUnification

## Abstract

Uniform computable native unification

The finite-tree representation preserves constructor order, equation order, Boolean leaves and every repeated variable occurrence. A list representation of the native substitution preserves each original-key lookup. Fresh insertion composes the new binding into all old values. The bounded evaluator follows the existing native variable, occurs-check, constructor and alias branches. Its mutual simulation preserves the actual native substitution action; no alternative most-general unifier is substituted.

Primitive recursive tree folds compute substitution, variables, branch selection, range checking and output projection. A partial recursive code fixed point implements the bounded mutual evaluator. Fuel induction proves that its code evaluation is total at every fuel. The existing exact finite native simulation supplies termination for the unbounded first-finished search. Partial recursive search and this termination proof establish a total computable solver, with no uniform primitive recursive bound or complexity assertion.

**Definition 1.1 (Finite composed action).**

Lean statement: `D5/S0/Rewriting/UniformNativeUnification.apply`

*Formalization.* `D5/S0/Rewriting/UniformNativeUnification.apply` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The finite substitution representation acts by original-key lookup on variables and structurally on Boolean and binary constructors.

**Definition 1.2 (Ordered variable occurrences).**

Lean statement: `D5/S0/Rewriting/UniformNativeUnification.vars`

*Formalization.* `D5/S0/Rewriting/UniformNativeUnification.vars` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The finite list retains all variable occurrences in left-to-right tree order, including repeated names.

**Definition 1.3 (Exact native lookup relation).**

Lean statement: `D5/S0/Rewriting/UniformNativeUnification.Represents`

*Formalization.* `D5/S0/Rewriting/UniformNativeUnification.Represents` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For each natural-number ordinal, native lookup equals the native encoding of the finite representation's lookup. Hash-bucket order has no role in this relation.

**Definition 1.4 (Composed fresh insertion).**

Lean statement: `D5/S0/Rewriting/UniformNativeUnification.insert`

*Formalization.* `D5/S0/Rewriting/UniformNativeUnification.insert` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A fresh original binding is inserted after its action has been composed into each prior value. The finite list retains the native first-lookup convention.

**Definition 1.5 (Coded bounded equation evaluation).**

Lean statement: `D5/S0/Rewriting/UniformNativeUnification.one`

*Formalization.* `D5/S0/Rewriting/UniformNativeUnification.one` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The finite representation follows the existing native one-equation evaluator at identical fuel, retaining equality, both variable orientations, occurs checks, aliases and constructor decomposition.

**Definition 1.6 (Coded bounded list evaluation).**

Lean statement: `D5/S0/Rewriting/UniformNativeUnification.core`

*Formalization.* `D5/S0/Rewriting/UniformNativeUnification.core` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The finite representation evaluates the ordered equation list at identical fuel and transfers each successful composed substitution to the remaining equations.

**Definition 1.7 (Exact bounded result relation).**

Lean statement: `D5/S0/Rewriting/UniformNativeUnification.Matches`

*Formalization.* `D5/S0/Rewriting/UniformNativeUnification.Matches` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Exhaustion matches exhaustion; failure matches the native error branch; success preserves every original-key lookup of the native substitution. Only the outer solver interface discards error payloads.

**Definition 1.8 (Finite tree case analysis).**

Lean statement: `D5/S0/Rewriting/UniformNativeUnification.view`

*Formalization.* `D5/S0/Rewriting/UniformNativeUnification.view` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The view separates a Boolean or variable leaf from an ordered pair of child trees.

**Theorem 1.9 (Uniform total computability).**

Lean statement: `D5/S0/Rewriting/UniformNativeUnification.computable_F`

*Proof.* Machine-checked in Lean as `D5/S0/Rewriting/UniformNativeUnification.computable_F` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The single solver function on all finite Nat-indexed equations is computable. Exact bounded simulation, finite native halting and encoded first-finished search establish this result for arbitrary domain sizes, with no supplied solver or normalization oracle.

## References

- Truth anchor: `D5/S0/Rewriting/UniformNativeUnification.Matches`
- Truth anchor: `D5/S0/Rewriting/UniformNativeUnification.Represents`
- Truth anchor: `D5/S0/Rewriting/UniformNativeUnification.apply`
- Truth anchor: `D5/S0/Rewriting/UniformNativeUnification.computable_F`
- Truth anchor: `D5/S0/Rewriting/UniformNativeUnification.core`
- Truth anchor: `D5/S0/Rewriting/UniformNativeUnification.insert`
- Truth anchor: `D5/S0/Rewriting/UniformNativeUnification.one`
- Truth anchor: `D5/S0/Rewriting/UniformNativeUnification.vars`
- Truth anchor: `D5/S0/Rewriting/UniformNativeUnification.view`
- Dependency: [D5/S0/Computability/PreorderTreeEvaluation](../Computability/PreorderTreeEvaluation.md)
- Dependency: [D5/S0/Rewriting/UnificationFuel](UnificationFuel.md)
- Dependency: [D5/S0/Rewriting/UniformNativeUnificationDomain](UniformNativeUnificationDomain.md)
