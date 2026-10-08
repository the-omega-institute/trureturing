# Joint Optimization over History Processes and Prefix Codes

## Abstract

An extreme iid law and one infinite greedy code attain the history-class joint maximum.

Let A have d at least two letters. Fix a letter called base and a real lower bound delta with 0 < delta and d times delta at most one. Admissible(delta,q) means that every finite history h has a row q(h,a) whose coordinates are at least delta and sum to one. There is no stationarity, finite-memory, mixing or computability hypothesis. A word mass is the product of the rows encountered along its actual path.

Write p for the extreme row: its base coordinate is 1 - (d-1)delta and every other coordinate is delta. For arbitrary natural depth budgets b and fixed tie orders, G is the canonical infinite iid greedy code for p. Legal(b,F), its levels, the iid truncatedMass(p,F,N), and the countable iid codeMass(p,F) are the existing prefix-code constructions. The history versions replace iid products with actual conditional path products. J is the set of all historyCodeMass(q,F) with q admissible and F legal. Countable masses and their supremum lie in the extended nonnegative reals and are at most one. The formula uses d for the alphabet cardinality and toReal for the real value of an extended nonnegative mass. Event mass is represented by the sum of path masses over a prefix code. No measure on infinite paths is constructed here, and equality with the measure of the union of cylinders is not formalized.

**Theorem 1.1 (The same iid process and code attain the joint optimum).**

$$\forall delta, base, b, tie, p, G, J, c, 2 \le d \land 0 < delta \land d delta \le 1 \Rightarrow (p = \operatorname{extremeRow}\left(delta, base\right) \land G = \operatorname{greedyCode}\left((N \mapsto \operatorname{priority}\left(p, \operatorname{tie}\left(N\right)\right)), b\right) \land J = \{x \mid \exists q, \operatorname{Admissible}\left(delta, q\right) \land \exists F, \operatorname{Legal}\left(b, F\right) \land x = \operatorname{historyCodeMass}\left(q, F\right)\} \land c = 1 - d delta) \Rightarrow \operatorname{Legal}\left(b, G\right) \land \operatorname{Admissible}\left(delta, (h \mapsto p)\right) \land (\forall q, \operatorname{Admissible}\left(delta, q\right) \Rightarrow \forall F, \operatorname{Legal}\left(b, F\right) \Rightarrow \forall N, \operatorname{historyTruncatedMass}\left(q, F, N\right) \le \operatorname{truncatedMass}\left(p, G, N\right)) \land \operatorname{IsGreatest}\left(J, \operatorname{codeMass}\left(p, G\right)\right) \land \operatorname{sSup}\left(J\right) = \operatorname{codeMass}\left(p, G\right) \land \operatorname{codeMass}\left(p, G\right) \le 1 \land 1 - \operatorname{sSup}\left(J\right) = 1 - \operatorname{codeMass}\left(p, G\right) \land 1 - \operatorname{toReal}\left(\operatorname{sSup}\left(J\right)\right) = 1 - \operatorname{toReal}\left(\operatorname{codeMass}\left(p, G\right)\right) \land \operatorname{historyCodeMass}\left((h \mapsto p), G\right) = \operatorname{codeMass}\left(p, G\right) \land (delta < 1/d \Rightarrow \forall q, \operatorname{Admissible}\left(delta, q\right) \Rightarrow \forall h, (\forall a, 0 \le (\operatorname{q}\left(h, a\right) - delta)/c) \land \sum_a (\operatorname{q}\left(h, a\right) - delta)/c = 1 \land (\forall a, \operatorname{q}\left(h, a\right) = \sum_{heavy} ((\operatorname{q}\left(h, heavy\right) - delta)/c) \operatorname{extremeRow}\left(delta, heavy, a\right))) \land (delta = 1/d \Rightarrow (\forall a, \operatorname{p}\left(a\right) = delta) \land \forall q, \operatorname{Admissible}\left(delta, q\right) \Rightarrow \forall h, a, \operatorname{q}\left(h, a\right) = delta).$$

*Proof.* Machine-checked in Lean as `D5/S0/Computability/Coding/HistoryBudgetJointOptimality.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Finite path sums satisfy a backward recursion with an indicator reward at selected nodes. After reserving delta in every coordinate, the remaining row mass is placed on a child of maximum continuation value. Backward induction bounds every process. Choosing the remaining horizon from each node's depth defines one process on all histories and attains all relevant backward values simultaneously.

Swap the maximizing child at each original history with base. The resulting tree bijection preserves prefix freedom, word lengths and each depth budget, and turns the optimizing path masses into iid masses for p. The iid greedy maximum therefore bounds every finite history truncation. Suprema of the nonnegative finite sums give the infinite bound. Its actual attainment uses the fixed iid process p and the same G; the auxiliary finite optimizers need not agree across horizons. The root budget theorem for finite prefix antichains bounds every finite selection of codewords; the supremum of these sums is at most one.

Both the extended nonnegative complement and the real complement are one minus the corresponding optimum, hence one minus the corresponding value of codeMass(p,G). At delta = 1/d every admissible row is uniform and p is uniform. Depth zero, empty codes, zero budgets, skipped depths and frontier exhaustion remain included. Constraints depending on letter labels would require an additional invariance hypothesis and are outside this budget class.

When delta < 1/d, put c = 1 - d times delta. Every admissible row is the convex combination of the extreme rows indexed by their heavy letter, with weights (q(h,a)-delta)/c. These weights are nonnegative, sum to one and reconstruct every coordinate of the original row.

A method precedent is the finite dice model and finite-event Bellman recursion in Beigi-Etesami-Gohari, Deterministic Randomness Extraction from Generalized and Distributed Santha-Vazirani Sources, arXiv:1412.6641v1, Definition 1 and Theorem 6, as cited in source Section 6.99. Its finite-event result supplies a method precedent for the recursion, while the infinite budget conclusion follows from the path-sum argument here.

## References

- Truth anchor: `D5/S0/Computability/Coding/HistoryBudgetJointOptimality.result`
- Dependency: [D5/S0/Computability/Coding/DepthBudgetIidGreedyOptimality](DepthBudgetIidGreedyOptimality.md)
- Dependency: [D5/S0/Computability/Coding/HistoryTreeRelabeling](HistoryTreeRelabeling.md)
- Dependency: [D5/S0/History/FinitePrefixAntichainBudget](../../History/FinitePrefixAntichainBudget.md)
