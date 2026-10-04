# Actual Strict History Capacity and Native Recipe Continuations

## Abstract

Strict actual leaf growth bounds the capacity of positive same-size families, through exact native recipe continuations.

Source is the original finite ordered alpha/beta tree. An address is a finite left/right word, including the empty root. An event carries one address and its original four-valued reply. F is any family indexed by Fin(m), S is a finite index set, and r is one Recipe(F,S) from ActualJointResponseCostCore. The continuation theorem requires neither positivity nor injectivity nor a common leaf size.

route(r,i) is that recipe's existing actual routeTrace. queue(F,S,H) retains exactly the indices in S whose actual trees match every addressed report in H, including branch and absent reports. A history is live when it is a prefix of route(r,i) for some i in S. res(r,H) starts with r; each event must use the current split's one full-vector representative and a nonempty survivor fiber. It then selects exactly next(y,hy). A singleton has no transition. A residual R stores its finite queue Q(R) and its native recipe q(R).

child(R,e) is false at a singleton. At a split with actual vector a on queue T, it means that e's address equals representative(F,a) and the fiber {i in T : a(i)=reply(e)} is nonempty. Thus the live children are precisely the nonempty fibers of the original alpha, beta, branch and absent reports; all use the same representative. Concatenation is denoted cat, and prefix is ordinary list prefix.

**Theorem 1.1 (Exact selected continuation and terminal prefix antichain).**

$$\forall m: \operatorname{Nat}\left(\right), (\forall F: \operatorname{Family}\left(m\right), (\forall S: \operatorname{Finset}\left(\operatorname{Fin}\left(m\right)\right), (\forall r: \operatorname{Recipe}\left(F, S\right), ((\forall H: \operatorname{Hist}\left(\right), ((\exists i: \operatorname{Fin}\left(m\right), ((i \in S) \land (\operatorname{prefix}\left(H, \operatorname{route}\left(r, i\right)\right)))) \implies (\exists R: \operatorname{Residual}\left(F\right), ((\operatorname{res}\left(r, H\right) = \operatorname{some}\left(R\right)) \land (\operatorname{Q}\left(R\right) = \operatorname{queue}\left(F, S, H\right)) \land (\forall i: \operatorname{Fin}\left(m\right), ((i \in S) \implies ((\operatorname{prefix}\left(H, \operatorname{route}\left(r, i\right)\right)) \iff (i \in \operatorname{Q}\left(R\right))))) \land (\forall i: \operatorname{Fin}\left(m\right), ((i \in \operatorname{Q}\left(R\right)) \implies (\operatorname{route}\left(r, i\right) = \operatorname{cat}\left(H, \operatorname{route}\left(\operatorname{q}\left(R\right), i\right)\right)))) \land (\forall K: \operatorname{Hist}\left(\right), (\operatorname{res}\left(r, \operatorname{cat}\left(H, K\right)\right) = \operatorname{res}\left(\operatorname{q}\left(R\right), K\right))) \land (\forall Rp: \operatorname{Residual}\left(F\right), ((\operatorname{res}\left(r, H\right) = \operatorname{some}\left(Rp\right)) \implies (Rp = R))) \land (\forall e: \operatorname{Event}\left(\right), ((\exists i: \operatorname{Fin}\left(m\right), ((i \in S) \land (\operatorname{prefix}\left(\operatorname{cat}\left(H, \operatorname{one}\left(e\right)\right), \operatorname{route}\left(r, i\right)\right)))) \iff (\operatorname{child}\left(R, e\right)))))))) \land (\forall i: \operatorname{Fin}\left(m\right), (\forall j: \operatorname{Fin}\left(m\right), (((i \in S) \land (j \in S) \land (\operatorname{prefix}\left(\operatorname{route}\left(r, i\right), \operatorname{route}\left(r, j\right)\right))) \implies (i = j))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/ActualStrictHistoryCapacity.reached_prefix` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Induction runs on the original Recipe with a motive universal over reached histories. At a split, a nonempty prefix's first event identifies its representative and original reply fiber. Every prototype matching that event enters the same selected next(y,hy). The child induction hypothesis transports its exact all-report queue, prefix membership and suffix identity back to the parent.

Appending any further history after H is exactly descent from q(R); the option-valued selection makes the continuation unique among continuations selected by r. This asserts no uniqueness of arbitrary recipes on a finite set. The immediate-extension equivalence identifies every live addressed child. At a singleton it forbids every live extension and the suffix identity makes H the terminal route itself.

If one terminal route prefixes another, the selected residual of the first has an empty route for its surviving index. A split cannot have an empty route on a member of its queue. Hence that residual is a singleton, and both indices are the same. This supplies terminal injection and a prefix antichain without an assumed route encoding.

The continuation theorem carries the actual survivor history into the strict-growth and resource-budget arguments of the capacity theorem below.

**Theorem 1.2 (Complete source31.7 capacity bound).**

$$\forall m: \operatorname{Nat}\left(\right), (\forall F: \operatorname{Family}\left(m\right), (\forall n: \operatorname{Nat}\left(\right), (\forall t: \operatorname{Nat}\left(\right), (((\operatorname{positiveIndex}\left(m\right)) \land (\operatorname{positiveFamily}\left(F\right)) \land (\operatorname{injective}\left(F\right)) \land (\operatorname{sameLeafSize}\left(F, n\right)) \land (\operatorname{K}\left(F\right) = \operatorname{Kcircle}\left(m\right)) \land ((\operatorname{D}\left(F\right) \leq n + t) \lor (\operatorname{W}\left(F\right) \leq n + t) \lor (\operatorname{Wu}\left(F\right) \leq n + t))) \implies (m \leq \operatorname{M}\left(\operatorname{s}\left(F\right) - 1, t\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/ActualStrictHistoryCapacity.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix any natural m greater than zero and an injective actual family F:Fin(m)->Source, with every tree positive and native leaf count n. K(F) consists of index subsets on which one full-domain Strategy attains each tree's individual leaf baseline. Kcircle(m) contains exactly the empty and singleton subsets. The output-alpha maximum s(F) is max_i card(alphaLeaves(F(i))). The integer count is exactly source30.11: M(0,t)=M(r,0)=1 and M(r+1,t+1)=M(r,t+1)+2*M(r+1,t). Its first native representation supplies no separate mathematical content.

A conflicting shared alpha/beta leaf would yield a native two-prototype Recipe with zero response gain, and hence one strategy jointly attaining both individual baselines. This contradicts K=Kcircle. Thus the original complex equality supplies non-conflict internally, without an eleven-leaf restriction or an added target premise. The finite nonempty actual cost core attains its minimum; the chosen strategy is exactly recipeStrategy for the minimizing strict Recipe.

At every reached history, f and c count distinct acquired leaf and nonleaf addresses. Geometry is applied to that same history and actual survivor source. For a new decoded A block use its LR alpha anchor; for a C use its RR alpha anchor. If the anchor were covered, old compatibility and the five forcing rows would fix the new block and its report on all old survivors, contradicting strictness. The finite alpha union therefore grows at every strict leaf child, giving g>=f. When f>=s-1, at most one alpha remains uncovered. Complete same-size history rigidity makes the queue a singleton.

Non-conflict allows at most one leaf-report child and at most the branch and absent children. Strictness supplies a nonleaf successor. Every prototype terminal has c<=t, so an internal queue must have c<t as well as f<s-1. The budget B(H) is M(s-1-f(H),t-c(H)) exactly on prefixes of actual terminal traces and zero elsewhere. For every history and every finite selection of addressed children, singleton queues have no live extension; strict queues have the one-leaf/two-nonleaf partition and positive remaining budgets. The original recurrence proves the required local child sum. FinitePrefixAntichainBudget then bounds the actual terminal antichain, whose cardinality equals m by native terminal index injection. This includes s=1, t=0 and every feasible small n.

Only actually acquired addresses, whether leaf or nonleaf, enter the cache; inferred leaves do not. On a prototype, nonleafPaid(route) is exactly paid(route) minus its actual leaf set, and the terminal cost is n+c. The existing controller still verifies all n labelled leaves, paying f+c+(n-f)=n+c; inferred block leaves are not cache entries. Its independently initialized acquisition fallback retains the real outer cache and processes every finite unknown Source. Positivity, size and family membership restrict evaluation prototypes only.

The W and Wu substitutions retain the original ALL-Source wrong-return and divergence contract. Source countability follows from existing finite composition fibers. One common good seed gives a globally correct total Strategy; execution uniqueness identifies independently chosen terminal runs. Integral monotonicity keeps the same law and the maximum inside the integral. Constant controllers use PUnit at the arbitrary seed universe and the actual completed unit interval, including endpoints. No expectation/maximum exchange or R/Ru assertion enters the theorem.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualStrictHistoryCapacity.reached_prefix`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualStrictHistoryCapacity.result`
- Dependency: [D5/S0/History/FinitePrefixAntichainBudget](../../../S0/History/FinitePrefixAntichainBudget.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/ActualHistorySingleHoleRecovery](ActualHistorySingleHoleRecovery.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/ActualJointResponseCostCore](ActualJointResponseCostCore.md)
