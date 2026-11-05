# Rank-free obstruction for native functional systems

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

Every such assignment extends to one joint solution w of all original equations, with w equal to v on B. The supplied values of v outside B are unrestricted, and unused and disconnected auxiliaries remain in the joint system. Taking B empty gives a completed solution of every functional system. Taking B to be the undefined states permits arbitrary values there. These are applications of the theorem, rather than additional hypotheses.

The construction records a tree by all its labelled leaf occurrences. The leafless tree is below every tree in the inclusion order on these facts. An increasing sequence has a native completed limit: at each reached position the limit has the unique eventual leaf label if one appears, and branches otherwise. Native substitution preserves this limit because each output leaf descends from a single input leaf through the actual finite replacement of that label. In particular, substitution remains interpreted native evolution, with all atomic sibling collisions retained.

Keep the supplied boundary values fixed, use the original right side at every other defined state, and use the leafless tree at the remaining undefined states. Iterating this operation from the constant leafless assignment yields increasing leaf facts. Their limits commute with every finite expression and therefore satisfy the fixed equations outside B. Closure of B transfers the already satisfied boundary equations to the same limiting assignment. This proves simultaneous satisfaction even when finite designated values coexist with infinite auxiliaries.

In the formula, NativePredicates(m) means predicates on Fin(m), NativeValues(m) means functions from Fin(m) to CompletionTree, holds(B,i) means B applied to i, and valueAt(v,i) means v applied to i. The theorem establishes extension of a specified closed boundary. Finite reconstruction from free boundary values and the finite-union conversion obstruction require further mathematical arguments. No external novelty is asserted.

**Theorem 1.3 (A varying finite coordinate admits positive native mass).**

$$\forall m: Nat, (\forall S: \operatorname{System}\left(m\right), (\forall u: \operatorname{NativeValues}\left(m\right), (\forall v: \operatorname{NativeValues}\left(m\right), ((\operatorname{Satisfies}\left(S, u\right)) \implies ((\operatorname{Satisfies}\left(S, v\right)) \implies (\forall i: \operatorname{Fin}\left(m\right), ((\operatorname{IsFinite}\left(\operatorname{valueAt}\left(v, i\right)\right)) \implies (\exists w: \operatorname{NativeValues}\left(m\right), ((\operatorname{Satisfies}\left(S, w\right)) \land (\exists t: Source, ((\operatorname{embed}\left(t\right) = \operatorname{valueAt}\left(w, i\right)) \land ((\operatorname{valueAt}\left(u, i\right) \neq \operatorname{valueAt}\left(v, i\right)) \implies (0 < \operatorname{gamma}\left(t\right))))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeFunctionalObstruction.finite_coordinate_perturbation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let u and v be two simultaneous solutions of the same original functional system S, and suppose only v(i) is finite. There is a simultaneous solution w and a finite native tree t with embed(t)=w(i). If u(i) and v(i) differ, t has strictly positive native mass gamma. The other values of u, v and w may be infinite, including unrestricted nonregular trees. No equation, auxiliary coordinate or repeated dependency is removed.

A zero-power root-link path follows equations of the form X_j=X_k. Define the free region as the states for which every such path encounters only another zero-power root link or an undefined state. This region is closed under every original variable occurrence, and assigning one common tree to the entire region satisfies all of its original equations. Choose the finite ordered pair (alpha,alpha), which has positive native mass, and extend this boundary by the whole-system boundary extension theorem.

For a state outside that region, some finite root-link path ends at an original defining expression which is not a zero-power root link. Every variable occurrence of this expression is below a pair or has a positive fixed power. If the original coordinate is finite, finite dependency descent therefore gives strictly smaller positive leaf weight at every such dependency. Strong induction on that weight proves that the extended coordinate is finite.

The same induction compares u and v. A difference at an expression value requires a difference at some variable occurrence. The inductive positive mass at that occurrence survives each native power and cannot decrease through a containing ordered pair. Grounds cannot produce a difference. Equality along every original root-link path transfers the result back to the designated coordinate. This is an unbounded native construction and descent proof; no finite enumeration or external novelty is claimed.

In the formula, NativeValues(m) abbreviates Fin(m) to CompletionTree, valueAt(v,i) means v(i), and gamma is native finite-tree mass. The existence of w is unconditional under the two original solution premises and the one coordinate finiteness premise. Positive mass is conditional only on those two designated values differing. This bridge does not itself conclude the finite-union obstruction.

**Theorem 1.4 (The whole homogeneous solution set has no finite functional representation).**

$$\forall a: Nat, (\forall H: Homogeneous, ((\operatorname{PairRoot}\left(H\right)) \implies ((\operatorname{eval}\left(H, \operatorname{leaf}\left(true\right)\right) = \operatorname{atomic}\left(a\right)) \implies (\forall F: FiniteComponents, (\operatorname{SolutionSet}\left(a, H\right) \neq \operatorname{nativeRepresented}\left(F\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeFunctionalObstruction.rank_free_obstruction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural a and finite homogeneous ordered pair expression H, suppose H has a pair at its root, its frontier consists of fixed nonnegative powers of one residual, and H(alpha)=T_a. The entire completed solution set of rho^a X=H(X) differs from the union represented by every finite list of original functional components. H has no ground and no second residual. The only anchor hypothesis is the stated alpha equality.

A component consists of an arbitrary finite number of states, at most one original defining expression per state, and its actual designated state. Its projection existentially quantifies one joint assignment satisfying every original equation, and reads that same designated native value. NativeExpr allows finite native grounds, original variables, ordered pairs and fixed nonnegative powers around arbitrary subexpressions. A structural translation distributes powers and evaluates powered grounds. Its value-preservation proof uses the native pair law and iteration, and its whole-system equivalence retains the same assignments and designated coordinate. No normalization premise is supplied. The component syntax includes repeated states and undefined states. The finite list can be empty; components are independent. Zero-power alias cycles, positive-shift cycles, guarded cycles and unused or disconnected auxiliaries are all included. A finite designated output can coexist with infinite auxiliary values.

The completed homogeneous split identifies the target as all distinct finite atomic iterates together with the leafless tree. If one component contained in that target produced two different atomic iterates, finite-coordinate perturbation would give a solution of the same whole component with finite positive native mass at the designated state. The leafless tree is not finite, while every atomic iterate has zero native mass. The new output contradicts containment in the target. Hence each such component contains at most one atomic iterate.

Induction over the actual finite list makes the set of represented atomic ranks finite: each component contributes a subsingleton set of ranks, and adjoining a component takes a union. Equality with the entire target would represent every natural atomic rank, contradicting infinitude of the naturals. The argument uses the perturbation construction on its live inference path and preserves all original equations throughout.

The displayed formula unfolds the proposition NativeObstruction. SolutionSet(a,H) means the set of all completed native values X satisfying rho^a X=eval(H,X); nativeRepresented(F) is the actual finite union of designated projections. FiniteComponents is List(NativeComponent). There is no normalization, extension, rigidity, canonical-solution or decoder premise, and no rank, depth, size, regularity or finite-value restriction on the completed domain. The result addresses exact representation of that coordinate set. It makes no claim about control, service, acquisition, erasure, stopping, productive contact or effective prefix computation. The proof is repository-derived, with no external novelty claim.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeFunctionalObstruction.finite_coordinate_perturbation`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeFunctionalObstruction.finite_cycle_is_silent`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeFunctionalObstruction.rank_free_obstruction`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeFunctionalObstruction.whole_system_boundary_extension`
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/CompletionPositiveDriftRegion](../CompletionPositiveDriftRegion.md)
