# Original Completion Horizon and Literal Support

## Abstract

An original normalized completion has a uniform chronological horizon and finite literal address support on each original leaf-budget class.

Sources are the original nonempty finite ordered full binary trees with Boolean leaf labels. Addresses are literal finite Boolean words, and readout has the four original replies alpha, beta, branch and absent. Coarse histories preserve every address, order and repetition while identifying branch with absent. Fix any natural m, any family F from Fin m to Source, any finite three-response passive route p, any decoder from coarse histories to Option (Fin m), any natural N at least one, and any correct original Strategy pi whose policy is exactly h maps to controllerPolicy (compileRaw F decode p []) (encodeHistory (kappa_hist h)). No bound on a route word or a prototype is assumed.

**Definition 1.1 (Original coarse histories).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualCompletionHorizon.CoarseHistory`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/ActualCompletionHorizon.CoarseHistory` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A coarse history is a finite ordered list of address and Option Bool pairs. It retains each literal address and each repeated request.

**Definition 1.2 (Longest syntactic route).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualCompletionHorizon.routeHorizon`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/ActualCompletionHorizon.routeHorizon` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A stop has horizon zero. A query contributes one plus the maximum of its none, some false and some true child horizons. This counts all occurrences, including repeated requests; it is not the number of distinct addresses.

**Definition 1.3 (Literal route alphabet).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualCompletionHorizon.routeSupport`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/ActualCompletionHorizon.routeSupport` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A stop has empty support. A query contributes its literal word and the supports of all three continuations. An arbitrarily long absent word remains in this finite syntactic union.

**Definition 1.4 (Maximum prototype leaf count).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualCompletionHorizon.prototypeMax`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/ActualCompletionHorizon.prototypeMax` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The maximum is Finset.univ.sup of the original source leaf count (F i).length. The existing duplicate-free leaf-list and leaf-address cardinality identities identify this with (leaves (F i)).length. The empty Fin 0 maximum is zero.

**Definition 1.5 (Complete prototype leaf alphabet).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualCompletionHorizon.prototypeLeaves`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/ActualCompletionHorizon.prototypeLeaves` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Take the union over every i in Fin m of (leaves (F i)).toFinset. There is no prototype size or address-length cutoff. The empty family gives the empty set.

**Definition 1.6 (Original bounded node alphabet).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualCompletionHorizon.qNFinset`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/ActualCompletionHorizon.qNFinset` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Take the image of all ActualObserverFiniteTable.BoundedAddress N under Subtype.val. Membership is exactly address length at most N minus one, hence this finite set realizes the original Q_N. Every node of an Allowed N source belongs to it; the original nodes_length supplies the depth bound.

In the formula, Route is PassiveProtocol Address (fun _ => Option Bool). H(F,p,N) denotes routeHorizon p + prototypeMax F + (2*N-1), and Qstar(F,p,N) denotes qNFinset N union routeSupport p union prototypeLeaves F. normalizedPolicy(F,decode,p) is exactly h maps to controllerPolicy (compileRaw F decode p []) (encodeHistory (kappa_hist h)). outcome(F,decode,p,U) denotes controllerOutcome (compileRaw F decode p []) U, terminal(pi,U) is the original terminal pair, trace(pi,U) its first component, request(a) is Sigma.fst, RawEntry is an address-reply pair, and stateCard(N,pi) is Fintype.card (ExactState (strategyPrefixes N pi)). The exact allowedSources N carrier enumerates the original Allowed N sources.

**Theorem 1.7 (Original completion bound).**

$$\forall m: Nat, (\forall F: \operatorname{Fin}\left(m\right) \to Source, (\forall decode: CoarseHistory \to \operatorname{Option}\left(\operatorname{Fin}\left(m\right)\right), (\forall p: Route, (\forall N: Nat, (\forall pi: Strategy, (((1 \leq N) \land (\operatorname{policy}\left(pi\right) = \operatorname{normalizedPolicy}\left(F, decode, p\right))) \implies ((\forall U: Source, (\operatorname{terminal}\left(pi, U\right) = \operatorname{outcome}\left(F, decode, p, U\right))) \land (\forall U: Source, ((\operatorname{Allowed}\left(N, U\right)) \implies ((\operatorname{length}\left(\operatorname{trace}\left(pi, U\right)\right) \leq \operatorname{H}\left(F, p, N\right)) \land (\forall a: RawEntry, ((a \in \operatorname{trace}\left(pi, U\right)) \implies (\operatorname{request}\left(a\right) \in \operatorname{Qstar}\left(F, p, N\right))))))) \land (\operatorname{stateCard}\left(N, pi\right) \leq 1+\operatorname{card}\left(\operatorname{allowedSources}\left(N\right)\right)\cdot(\operatorname{H}\left(F, p, N\right)+1)\cdot2^{\operatorname{min}\left(\operatorname{card}\left(\operatorname{Qstar}\left(F, p, N\right)\right), \operatorname{H}\left(F, p, N\right)\right)}))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/ActualCompletionHorizon.actual_completion_horizon` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The terminal/outcome equality holds on every original source U, including sources outside Allowed N. Under Allowed N, the full terminal trace has length at most H and every requested literal address belongs to Qstar. The exact compatible-cache carrier has at most 1 + card(allowedSources N)*(H+1)*2 raised to min(card(Qstar),H) states.

The acquisition address list is the original nodes preorder, by trace_addresses. Its list count is 2*U.length-1, including both internal nodes and leaves. Since Allowed N U means U.length at most N, acquisition uses at most 2*N-1 requests. A verifier on a remaining list qs uses at most qs.length plus the complete acquisition length: a late mismatch retains every earlier successful request and its mismatch request before the new acquisition. Its literal support lies in qs union the actual nodes. Induction over the three route branches adds one chronological step and one literal route word at each query. At a selected stop, the complete prototype leaf list is bounded by prototypeMax and belongs to prototypeLeaves; at an unselected stop, acquisition begins immediately.

For exact normalized execution, compare raw and normalized controller actions only on prefixes of the actual outcome. A prototype leaf has alpha or beta reply, so choosing the branch representative for coarse none cannot turn a failed test into a successful leaf test. The verifier induction retains leaf membership for every remaining tail; an arbitrary query list would not justify this comparison. Route control sees only kappa, and the representative preserves kappa. At fallback, acquisition_prefix_representative fixes actual acquisition prefixes. Prefix action agreement transfers the raw execution supplied by phase_foundation to the normalized policy on the same source and with the same full trace and bit. The existing execution uniqueness in source_foundation then identifies that execution with terminal pi U.

The horizon and support inequalities supply the two hypotheses of strategy_state_card_bound at the original N. Each retained coarse prefix has at most H steps and at most card(Qstar) distinct addresses. Only first coarse-none addresses contribute the compatible branch/absent choices. Prefix counting contributes card(allowedSources N)*(H+1), and the absorbing sink contributes one. This state estimate includes nominal ghost cache lifts.

For the source-facing application, positivity of every prototype belongs to completion_contract: it supplies a correct Strategy and exactly the policy equation used above. Positivity is vacuous for m=0. Applying this theorem to that supplied Strategy gives the stated original completion horizon and support; it needs no extra positivity premise after the Strategy and its exact policy equation are fixed. No injectivity, nonempty prototype family, unique route address, successful decoding or allowed prototype assumption is used.

The existing exact-trace compiler, support pruning and phase replay provide the same-source observer, first-occurrence cache and phase conclusions. Here the horizon measures the full logical request trace, including cache hits, and Qstar includes all literal route and prototype words. The estimate supplies neither a competitor minimum nor the full exact-compiler minimum, and it does not price address serialization, physical storage or an external prototype read port.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualCompletionHorizon.CoarseHistory`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualCompletionHorizon.actual_completion_horizon`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualCompletionHorizon.prototypeLeaves`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualCompletionHorizon.prototypeMax`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualCompletionHorizon.qNFinset`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualCompletionHorizon.routeHorizon`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualCompletionHorizon.routeSupport`
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/ActualExactTraceCompiler](ActualExactTraceCompiler.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/ActualObserverFiniteTable](ActualObserverFiniteTable.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/ActualPureAcquisitionCompiler](ActualPureAcquisitionCompiler.md)
