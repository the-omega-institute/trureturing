# NativeUniformPlan

## Abstract

NativeUniformPlan

Finite singleton-equation native plans preserve the required branch order: native failure, collapse of any old disequality under the fully composed action, all actual bound variables ground, and feasible nonground action. Empty bound domains pass groundness vacuously. The original solver is reused. Presentation transport preserves its exact native input and deterministic output.

**Definition 1.1 (templateWord).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformPlan.templateWord`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformPlan.templateWord` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Serialize a finite ordinal term after replacing residual variables by the fixed Boolean test leaf.

**Definition 1.2 (kindCode).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformPlan.kindCode`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformPlan.kindCode` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The four native branches are encoded as zero for failure, one for old collapse, two for ground bindings and three for feasible nonground action.

**Definition 1.3 (codePlan).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformPlan.codePlan`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformPlan.codePlan` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Preserve both addresses, the native branch and the ordered finite-domain binding list. Each ground source retains its complete constructor word.

**Definition 1.4 (codedPlan).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformPlan.codedPlan`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformPlan.codedPlan` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Unify the singleton new equality. Test every old disequality under the normalized returned action before testing groundness of the actual bound domain. Identity outside that domain stays free; an empty domain passes the ground test vacuously.

**Theorem 1.5 (coded_plan_computable).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformPlan.coded_plan_computable`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformPlan.coded_plan_computable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The fixed finite input algorithm is computable. The proof uses the existing uniform native solver and primitive checks of the fully composed action; it does not assume that unification is primitive recursive.

**Theorem 1.6 (coded_plan_exact).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformPlan.coded_plan_exact`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformPlan.coded_plan_exact` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite ordinal presentation and every complete old-disequality list, the computed code equals the original native singleton-equation pair plan, including branch order and ground bindings.

**Definition 1.7 (renameTerm).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformPlan.renameTerm`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformPlan.renameTerm` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Rename residual variables while retaining Boolean constructors and the exact ordered binary tree.

**Definition 1.8 (ordinalPlan).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformPlan.ordinalPlan`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformPlan.ordinalPlan` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Serialize a variable-indexed native pair plan through the supplied ordinal map, retaining both addresses, branch and every binding template.

**Theorem 1.9 (plan_transport).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformPlan.plan_transport`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformPlan.plan_transport` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Transport a presentation along an equivalence while preserving the exact underlying native String input. The original solver therefore chooses the same native result; arbitrary-renaming invariance of a chosen MGU is not assumed.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformPlan.codePlan`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformPlan.codedPlan`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformPlan.coded_plan_computable`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformPlan.coded_plan_exact`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformPlan.kindCode`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformPlan.ordinalPlan`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformPlan.plan_transport`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformPlan.renameTerm`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformPlan.templateWord`
- Dependency: [D5/S0/Rewriting/UniformNativeUnification](../../../../S0/Rewriting/UniformNativeUnification.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformVariables](NativeUniformVariables.md)
