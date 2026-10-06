# Passive Query Memoization

## Abstract

Memoizing a passive dependent protocol charges each actual address once and preserves completed-history equality.

**Theorem 1.1 (Uniform memoization of the original dependent tree).**

$$\begin{aligned}\forall x, \operatorname{Sublist}\left(\operatorname{m}\left(x\right), \operatorname{h}\left(x\right)\right)\land\operatorname{Nodup}\left(\operatorname{addr}\left(\operatorname{m}\left(x\right)\right)\right),\\\operatorname{support}\left(\operatorname{addr}\left(\operatorname{m}\left(x\right)\right)\right)=\operatorname{support}\left(\operatorname{addr}\left(\operatorname{h}\left(x\right)\right)\right),\\\operatorname{length}\left(\operatorname{m}\left(x\right)\right)=\operatorname{card}\left(\operatorname{support}\left(\operatorname{addr}\left(\operatorname{h}\left(x\right)\right)\right)\right),\\\forall x,y, \operatorname{m}\left(x\right)=\operatorname{m}\left(y\right)\Leftrightarrow \operatorname{h}\left(x\right)=\operatorname{h}\left(y\right).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Experiment/PassiveQueryMemoization.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let Q and W be arbitrary types, let Y(q) be a dependent response family, and fix read(q): W to Y(q). The original PassiveProtocol T is a well-founded dependent tree, executed by runPassiveProtocol on the same source throughout.

A cache K is a dependent partial function assigning an optional response to each q. The structural transform memo(T,K) leaves stop unchanged. A hit follows the original continuation at the cached response without querying. A miss retains the original query and updates K with each possible response inside that response continuation. The empty-cache tree M(T) is selected from T alone, before W, read, or the source.

Write h(x) for the original completed history and m(x) for the actual history of M(T). Let addr project each dependent query-response pair to its query. Then m(x) is a Sublist of h(x), addr(m(x)) has no repetitions, and their address supports are equal. Thus the length of m(x) equals the cardinality of the finite address support of h(x). For all x and y, m(x)=m(y) if and only if h(x)=h(y).

The proof follows the original response-selected continuation with an arbitrary cache coherent with the source. Its strengthened induction keeps the paid suffix inside the old suffix, makes its addresses distinct and absent from the initial cache, and covers every old address by the initial cache or the paid suffix. Actual pair consistency and exact address support then allow the original execution-transfer and monotonicity results to establish both directions of completed-history equality.

There is no finite or inhabited carrier premise, response equality test, common fuel bound, or replacement oracle. Empty types and infinite response families remain in scope; different responses can lead to arbitrarily long finite branches. A fresh query with a constant response is retained. The result concerns passive fixed readouts and provides no arithmetic support bound, optimality theorem, or bound for active actions.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Experiment/PassiveQueryMemoization.result`
- Dependency: [D5/S3/ConceptDynamics/Experiment/PassivePolicyNormalization](PassivePolicyNormalization.md)
