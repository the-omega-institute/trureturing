# Positive contexts and unrestricted role valuations

## Abstract

NativePositiveContextFiber

**Definition 1.1 (Original addressed exterior).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativePositiveContextFiber.WellAddressed`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativePositiveContextFiber.WellAddressed` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Source is the free ordered binary tree on Boolean leaves. A HoleExterior has either a concrete Boolean leaf, an original hole address, or an ordered pair. For a finite cut P, WellAddressed checks the displayed syntax from a specified current address: concrete leaves and pairs lie outside P; every hole is labelled by precisely its current address in P; pair children continue at the original left and right addresses.

The condition is syntactic and independent of any source or valuation. It does not assume that P is prefix-free. Cuts lying below an already displayed hole are not exposed by this exterior, so no preservation of their individual reach status is asserted.

**Definition 1.2 (Independent exterior and positive role equalities).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativePositiveContextFiber.PositiveContext`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativePositiveContextFiber.PositiveContext` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A role label assigns a natural name to each original address. ActualCutPartitionDecoder.nameExterior replaces the addressed holes in X by their role names and retains every concrete leaf and ordered pair. PositiveContext means that cutting the original source produces exactly X and that any two displayed holes with the same role have equal original subtrees. It imposes no inequality between different roles.

A representative map chooses one displayed occurrence of every supported role. The premise concerns only names in labels(nameExterior(label,X)); unused names and their representatives have no constraint. The independent exterior equality ensures that all displayed role occurrences, including the chosen representatives, are reached in the source.

**Theorem 1.3 (Exact finite history for a positive context).**

$$\forall P: CutSet, (\forall X: HoleExterior, (\forall label: Address \to Nat, (\forall rep: Nat \to Address, ((\operatorname{WellAddressed}\left(P, nil, X\right)) \implies ((\forall n: Nat, ((n \in \operatorname{labels}\left(\operatorname{nameExterior}\left(label, X\right)\right)) \implies (\operatorname{rowAt}\left(\operatorname{rep}\left(n\right), \operatorname{nameExterior}\left(label, X\right)\right) = \operatorname{some}\left(\operatorname{of}\left(\operatorname{inr}\left(n\right)\right)\right)))) \implies (\forall U: Source, ((\operatorname{PositiveContext}\left(P, X, label, U\right)) \iff (\operatorname{Holds}\left(U, \operatorname{compile}\left(rep, nil, \operatorname{expression}\left(\operatorname{nameExterior}\left(label, X\right)\right)\right)\right)))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativePositiveContextFiber.positive_context_history_exact` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

expression turns a role row into a native MixedExpr: a concrete Boolean leaf is a ground tree, a role is a generator with substitution power zero, and an ordered pair is preserved. The existing compiler runs at the original root with the chosen representative map. It receives neither a source nor a role valuation.

The equivalence retains the complete concrete exterior and all within-role equalities. Every compiler link is an actual guarded positive equality, so both endpoints must be reached. Structural induction on the addressed exterior relates compiler literals and links to the independent cut and representative equalities. Transitivity recovers every pairwise equality for a repeated role.

The finite context may be completely ground, have no supported roles, or consist only of a root hole. Repeated roles and equal values at different roles are permitted. Concrete terminal leaves exclude hidden descendants, while values inserted at displayed holes have no size bound.

**Definition 1.4 (Explicit inverse by representative readout).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativePositiveContextFiber.recoverRoles`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativePositiveContextFiber.recoverRoles` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For each supported role, recoverRoles reads its original representative subtree. The total function has a fixed Boolean default, but reachedness is proved on every source in PositiveContext before that default is eliminated. This is a mathematical source operation and supplies no observer-accessible equality port.

**Definition 1.5 (Unrestricted valuation and source equivalence).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativePositiveContextFiber.positiveContextEquiv`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativePositiveContextFiber.positiveContextEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

With the same well-addressed and representative hypotheses, positiveContextEquiv is an equivalence from all functions Classes(nameExterior(label,X)) to Source onto the subtype of sources satisfying PositiveContext. Classes contains exactly the supported role names. The forward map fills the row using evaluateRow and extend; the inverse reads the representatives with recoverRoles.

The existing unrestricted rowAt_evaluate theorem proves that filling reaches each representative with its assigned value. NativePayloadHistoryInstallation.payload_history_exact then identifies the whole root source with the evaluated row. These facts establish both inverse equations, including the empty role domain. No injectivity of the role valuation is assumed; the distinct-class condition in NativeCutFibers.LegalValues belongs to the separate full-partition problem.

This finite-tree reconstruction uses ordinary structural induction and existing native evaluation results; no literature-originality claim is made. It supplies the original-exterior and within-role part of a positive correspondence. Atomic feedback, rank-only refinements, different-role inequalities, additional negative records and the complete acquired-fiber construction remain separate conditions. No arbitrary-policy decision procedure or complexity bound follows here.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativePositiveContextFiber.PositiveContext`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativePositiveContextFiber.WellAddressed`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativePositiveContextFiber.positiveContextEquiv`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativePositiveContextFiber.positive_context_history_exact`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativePositiveContextFiber.recoverRoles`
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/NativeCutFibers](NativeCutFibers.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/NativePayloadHistoryInstallation](NativePayloadHistoryInstallation.md)
