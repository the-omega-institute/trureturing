# Actual Joint Response Cost Core

## Abstract

Actual four-response routing has a finite simultaneous cost core for globally total tree membership strategies.

**Definition 1.1 (Shortlex address order).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ActualJointResponseCostCore.addressOrder`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ActualJointResponseCostCore.addressOrder` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Shorter words precede longer words; at equal length left precedes right.

**Definition 1.2 (Actual response children).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ActualJointResponseCostCore.survivors`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ActualJointResponseCostCore.survivors` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The child keeps exactly those current indices whose full-vector coordinate equals the actual reported reply.

**Definition 1.3 (First shortlex representative).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ActualJointResponseCostCore.representative`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ActualJointResponseCostCore.representative` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each realized complete vector uses its first actual address in shortlex order, with left before right. Replacement preserves every coordinate, including coordinates outside the current survivor set.

**Definition 1.4 (Strict recursive splitting).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ActualJointResponseCostCore.Recipe`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ActualJointResponseCostCore.Recipe` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A non-singleton survivor set selects a realized vector having at least two replies. Only its nonempty response children recurse. A singleton ends routing and chooses its prototype verifier; it does not certify an unknown input.

**Definition 1.5 (Recursive chi gain).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ActualJointResponseCostCore.gain`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ActualJointResponseCostCore.gain` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each strict split adds chi of the retained actual coordinate to its child gain; singleton gain is zero.

**Definition 1.6 (Recursive excess vectors).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ActualJointResponseCostCore.Gamma`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ActualJointResponseCostCore.Gamma` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Gamma(S) contains the coordinate restrictions of every finite splitting recipe's recursively accumulated chi gains. A singleton has zero gain. Every nonempty child is strictly smaller.

**Definition 1.7 (All numerical core vectors).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ActualJointResponseCostCore.core`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ActualJointResponseCostCore.core` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The core contains every vector n+gain(r) on the full index set, including vectors dominated by other recipes. It is defined by splitting choices independently of attained strategy costs.

**Definition 1.8 (Finite phase controller).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ActualJointResponseCostCore.Controller`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ActualJointResponseCostCore.Controller` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A finite query tree either accepts or enters actual acquisition. Unexpected replies enter fallback.

**Definition 1.9 (Own-history phase replay).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ActualJointResponseCostCore.controllerPolicy`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ActualJointResponseCostCore.controllerPolicy` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Routing consumes only its own requested prefix. After entry to a verifier or fallback, only that continuation's independently acquired suffix is presented as its logical history.

**Definition 1.10 (Actual phase outcome).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ActualJointResponseCostCore.controllerOutcome`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ActualJointResponseCostCore.controllerOutcome` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Truthful reports follow actual queries. Fallback outcome is exactly its independently initialized acquisition execution.

**Definition 1.11 (Complete labelled-leaf test).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ActualJointResponseCostCore.verifyController`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ActualJointResponseCostCore.verifyController` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The verifier requests the complete fixed prototype leaf list. Exact matches continue; any mismatch starts fresh acquisition. Acceptance requires every labelled leaf.

**Definition 1.12 (Real representative routing).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ActualJointResponseCostCore.recipeController`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ActualJointResponseCostCore.recipeController` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each recipe split requests its first actual full-vector representative and follows the actual reply. Singleton routing selects a complete verifier.

**Definition 1.13 (Actual prototype route).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ActualJointResponseCostCore.routeTrace`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ActualJointResponseCostCore.routeTrace` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This chronological list contains the truthful requested representative reports, with verifier and fallback reports excluded.

**Definition 1.14 (Actual total realization).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ActualJointResponseCostCore.recipeStrategy`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ActualJointResponseCostCore.recipeStrategy` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The strategy requests actual representatives, then the selected prototype's complete labelled leaves. Unexpected routing replies and any leaf mismatch begin the all-input fallback. Each verifier and fallback receives its own empty logical history; prior truthful reports only answer addresses it actually requests.

**Theorem 1.15 (Arbitrary prototype query lists).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ActualJointResponseCostCore.verifier`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/ActualJointResponseCostCore.verifier` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every prototype, input and finite address list, the verifier accepts exactly when every listed report matches the prototype or the input is a third substitution image.

**Theorem 1.16 (A prototype reproduces its query list).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ActualJointResponseCostCore.matched`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/ActualJointResponseCostCore.matched` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every prototype and finite address list, its own verifier returns precisely the truthful reports at those addresses and accepts.

**Theorem 1.17 (Distinct leaves and exact recipe costs).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ActualJointResponseCostCore.cost_foundation`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/ActualJointResponseCostCore.cost_foundation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every tree has a duplicate-free leaf list, and chi of a report is zero exactly at a leaf address. Every recipe on a positive family reproduces its controller outcome on retained prototypes. Its route has distinct joint response vectors and distinct addresses, with length at most the survivor cardinality minus one. Its gain is both the sum of report charges and the number of route addresses outside the leaf set, so its cost is the leaf-list length plus that gain. Every full-family core coordinate lies between its leaf baseline and that baseline plus the family cardinality minus one.

**Theorem 1.18 (Simultaneous attainment and coordinatewise domination).**

$$\forall m, F, (((1 \leq m) \land \\(\operatorname{Injective}\left(F\right)) \land \\(\forall i, (\operatorname{Positive}\left(\operatorname{P}\left(i\right)\right)))) \implies ((\operatorname{Finite}\left(\operatorname{core}\left(F\right)\right)) \land \\(\operatorname{Nonempty}\left(\operatorname{core}\left(F\right)\right)) \land \\(\forall v, ((v \in \operatorname{core}\left(F\right)) \implies (\exists r, sigma, ((\operatorname{Recipe}\left(F, r\right)) \land \\(\operatorname{Strategy}\left(sigma\right)) \land \\(sigma = \operatorname{recipeStrategy}\left(r\right)) \land \\(\forall i, ((\operatorname{C}\left(sigma, \operatorname{P}\left(i\right)\right) = \operatorname{coordinate}\left(v, i\right)) \land \\(\operatorname{J}\left(sigma, \operatorname{P}\left(i\right)\right) = \operatorname{union}\left(\operatorname{B}\left(r, i\right), \operatorname{L}\left(i\right)\right)) \land \\(\operatorname{Nodup}\left(\operatorname{V}\left(r, i\right)\right)) \land \\(\operatorname{Nodup}\left(\operatorname{A}\left(r, i\right)\right)) \land \\(\operatorname{length}\left(\operatorname{T}\left(r, i\right)\right) \leq m - 1) \land \\(\operatorname{card}\left(\operatorname{difference}\left(\operatorname{B}\left(r, i\right), \operatorname{L}\left(i\right)\right)\right) = \operatorname{E}\left(r, i\right)) \land \\(\operatorname{sum}\left(u \in \operatorname{B}\left(r, i\right), \operatorname{chi}\left(\operatorname{readout}\left(u, \operatorname{P}\left(i\right)\right)\right)\right) = \operatorname{card}\left(\operatorname{difference}\left(\operatorname{B}\left(r, i\right), \operatorname{L}\left(i\right)\right)\right)) \land \\(\operatorname{C}\left(sigma, \operatorname{P}\left(i\right)\right) = \operatorname{n}\left(i\right) + \operatorname{card}\left(\operatorname{difference}\left(\operatorname{B}\left(r, i\right), \operatorname{L}\left(i\right)\right)\right)))))))) \land \\(\forall pi, ((\operatorname{Strategy}\left(pi\right)) \implies (\exists v, ((v \in \operatorname{core}\left(F\right)) \land \\(\forall i, (\operatorname{coordinate}\left(v, i\right) \leq \operatorname{C}\left(pi, \operatorname{P}\left(i\right)\right))))))) \land \\(\forall v, ((v \in \operatorname{core}\left(F\right)) \implies (\forall i, ((\operatorname{n}\left(i\right) \leq \operatorname{coordinate}\left(v, i\right)) \land \\(\operatorname{coordinate}\left(v, i\right) \leq \operatorname{n}\left(i\right) + m - 1)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/ActualJointResponseCostCore.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

All index quantifiers range over Fin(m), and P_i=F(i). Let m be positive and F=(P_i) consist of pairwise distinct actual third-substitution images. Write L_i for the complete leaf-address set, n_i for its cardinality, V for the core, T_r(i) for the truthful representative routing trace and B_r(i) for its distinct-address set. J_sigma(P_i) is the paid set of the canonical terminal execution. In the formula, A_r(i) is the routing address list and V_r(i) its list of complete joint response vectors; E_r(i) is the chronological sum of chi over the truthful routing replies; it also equals the Finset sum over the actual routing address set.

The core is finite and nonempty. Every member is attained simultaneously by one fixed globally correct total strategy. For every original globally correct total strategy, a single core vector is no larger in any prototype coordinate. Each coordinate lies between its complete-leaf baseline and that baseline plus m-1.

Every positive prototype leaf is compulsory: changing its label gives a negative tree of the same shape and preserves every other address report. Deterministic same-history replay therefore prevents a correct accepting execution from omitting that leaf. Matching all labelled leaves forces literal equality of ordered trees.

The fallback requests the root, expands only actual branch reports, and reconstructs each finite input. The measured leaf count bounds a finite enumeration of actual preimages because native substitution never decreases that count. Forward comparison decides membership for positive and negative inputs, including both root leaves. Routing and verification add finite phases before this independently initialized fallback.

On P_i, routing retains i and selects its own complete verifier. The final paid set is exactly B_r(i) union L_i. An earlier full vector is constant on all descendants of its selected response child, so it cannot split there again. Full vectors and their representative addresses are therefore nonrepeating. Strict survivor decrease bounds routing by m-1. A routing leaf address is already in L_i; every other routing address adds exactly one paid address. This gives the exact response-dependent excess and attained cost. The source theorem also carries the literal Finset sum over the actual paid routing set: sum_{u in B_r(i)} chi(readout(u,P_i)) equals the paid routing set outside L_i.

For domination, restrict an original strategy to the finite union of addresses in its actual prototype terminal traces. The restricted selector has exactly those executions. Public passive-policy normalization supplies one pruned protocol, preserving terminal candidate fibers and retaining sublists of those traces. Compulsory leaves and labelled-leaf rigidity make every terminal fiber a singleton. Converting that protocol to a recipe preserves complete vectors and chi. Its retained original nonleaf addresses are distinct members of the same original prototype's paid set outside L_i. Representative substitution transfers no old-address cache entries. The complete verifier restores the leaf baseline, giving simultaneous coordinatewise domination.

Applying the construction to the independently total fallback gives nonemptiness. Bounded coordinates give finiteness. When m=1 the route is empty and the complete leaf verifier remains; no unknown-input promise is introduced. The statement concerns deterministic global strategies and prototype evaluation costs. The original per-source random contracts, their measurable null seed exceptions, extended costs, and and their optimization formulas are separate contracts.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualJointResponseCostCore.Controller`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualJointResponseCostCore.Gamma`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualJointResponseCostCore.Recipe`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualJointResponseCostCore.addressOrder`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualJointResponseCostCore.controllerOutcome`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualJointResponseCostCore.controllerPolicy`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualJointResponseCostCore.core`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualJointResponseCostCore.cost_foundation`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualJointResponseCostCore.gain`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualJointResponseCostCore.matched`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualJointResponseCostCore.recipeController`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualJointResponseCostCore.recipeStrategy`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualJointResponseCostCore.representative`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualJointResponseCostCore.result`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualJointResponseCostCore.routeTrace`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualJointResponseCostCore.survivors`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualJointResponseCostCore.verifier`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualJointResponseCostCore.verifyController`
- Dependency: [D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition](ActualTreeReadoutAcquisition.md)
