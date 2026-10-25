# Finite dependencies and completed extensions of native functional systems

## Abstract

NativeFunctionalObstruction

**Theorem 1.1 (A finite coordinate has no strict dependency cycle).**

$$\forall m: Nat, (\forall S: \operatorname{System}\left(m\right), (\forall v: \operatorname{NativeValues}\left(m\right), ((\operatorname{Satisfies}\left(S, v\right)) \implies (\forall i: \operatorname{Fin}\left(m\right), (\forall w: \operatorname{Walk}\left(S, i, i\right), ((\operatorname{IsFinite}\left(\operatorname{valueAt}\left(v, i\right)\right)) \implies (\neg \operatorname{Strict}\left(w\right))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeFunctionalObstruction.finite_cycle_is_silent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

System(m) assigns each of its m states either one finite expression or no equation. An expression is a finite native ground, a fixed nonnegative power of one state, or an ordered pair of expressions. It uses the existing expression type with zero scalar tokens. Every original equation is imposed jointly by Satisfies. Undefined states are unrestricted, repeated names denote the same value, and disconnected or unused states remain present.

Values are unrestricted finite or infinite full ordered Boolean-leaf trees. The operation rho replaces alpha by beta and beta by the ordered pair (beta,alpha), and distributes through branches. It is interpreted native substitution, including the atomic sibling collisions. No rank, regularity, depth or state bound is imposed beyond the supplied finite number of states.

A dependency retains its original defining expression, the occurrence address and the fixed power. A walk follows such dependencies. Strict means that at least one occurrence is below a pair, or at least one fixed power is positive. The theorem says that every cycle based at a finite-valued coordinate has no strict edge. Zero-power root links and alias cycles remain permitted. Finiteness is required only at that cycle's base; auxiliary values elsewhere may be infinite.

The proof assigns alpha weight one and beta weight two, and sums weights through native pairs. Every finite tree has positive weight. A containing pair has strictly greater weight than either child, and every native substitution strictly increases weight. Original occurrence semantics and preservation of finiteness transport these comparisons along each dependency and then along the walk. A strict cycle would strictly decrease a natural number back to itself.

In the formula, NativeValues(m) abbreviates functions from Fin(m) to CompletionTree, valueAt(v,i) means v applied to i, and Strict is Walk.Strict. The theorem concerns cycles in original simultaneous systems. It supplies neither a whole-system extension theorem nor an exact description of the projections of their solution sets. Its content is an unbounded structural descent argument, rather than a finite enumeration, checker, numeric reduction or certified instance. No external novelty is asserted.

**Theorem 1.2 (A closed boundary extends to a whole-system solution).**

$$\forall m: Nat, (\forall S: \operatorname{System}\left(m\right), (\forall B: \operatorname{NativePredicates}\left(m\right), (\forall v: \operatorname{NativeValues}\left(m\right), ((\operatorname{BoundaryClosed}\left(S, B\right)) \implies ((\operatorname{BoundaryValid}\left(S, B, v\right)) \implies (\exists w: \operatorname{NativeValues}\left(m\right), ((\operatorname{Satisfies}\left(S, w\right)) \land (\forall i: \operatorname{Fin}\left(m\right), ((\operatorname{holds}\left(B, i\right)) \implies (\operatorname{valueAt}\left(w, i\right) = \operatorname{valueAt}\left(v, i\right)))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeFunctionalObstruction.whole_system_boundary_extension` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

BoundaryClosed(S,B) means that every variable occurrence in the defining expression of a state in B is also in B. This includes occurrences below ordered pairs and with any fixed nonnegative power. BoundaryValid(S,B,v) means that v satisfies each original equation whose state belongs to B. Undefined states contribute no equation. The assigned values may be arbitrary completed trees.

Every such assignment extends to one joint solution w of all original equations, with w equal to v on B. The theorem imposes no condition on values at states outside B, and retains unused and disconnected auxiliaries. Taking B empty gives a completed solution of every functional system. Taking B to be the undefined states permits arbitrary values there. These are applications of the theorem, rather than additional hypotheses.

The construction records a tree by all its labelled leaf occurrences. The leafless tree is below every tree in the inclusion order on these facts. An increasing sequence has a native completed limit: at each reached position the limit has the unique eventual leaf label if one appears, and branches otherwise. Native substitution preserves this limit because each output leaf descends from a single input leaf through the actual finite replacement of that label. In particular, substitution remains interpreted native evolution, with all atomic sibling collisions retained.

Keep the supplied boundary values fixed, use the original right side at every other defined state, and use the leafless tree at the remaining undefined states. Iterating this operation from the constant leafless assignment yields increasing leaf facts. Their limits commute with every finite expression and therefore satisfy the fixed equations outside B. Closure of B transfers the already satisfied boundary equations to the same limiting assignment. This proves simultaneous satisfaction even when finite designated values coexist with infinite auxiliaries.

In the formula, NativePredicates(m) means predicates on Fin(m), NativeValues(m) means functions from Fin(m) to CompletionTree, holds(B,i) means B applied to i, and valueAt(v,i) means v applied to i. The theorem establishes extension of a specified closed boundary. Finite reconstruction from free boundary values and the finite-union conversion obstruction require further mathematical arguments. No external novelty is asserted.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeFunctionalObstruction.finite_cycle_is_silent`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeFunctionalObstruction.whole_system_boundary_extension`
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/CompletionPositiveDriftRegion](../CompletionPositiveDriftRegion.md)
