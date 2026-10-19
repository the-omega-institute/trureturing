# Fixed lower graphs and common actual margins

## Abstract

A finite lower graph determines one positive error margin for every canonical actual factor completion, before any factor is chosen.

**Definition 1.1 (graphGapValues).**

$$\forall n \in Nat, K \in Nat, d \in Real,\; \operatorname{graphGapValues}\left(n, K, d\right) = \operatorname{image}\left(\operatorname{filter}\left(\operatorname{univ}\left(\operatorname{MemoryVertex}\left(n\right)\right), (v : \operatorname{MemoryVertex}\left(n\right) \mapsto \operatorname{MemoryEdge}\left(lower, K, d, v, c, \operatorname{memoryShift}\left(v, c\right)\right) \land \operatorname{memoryRun}\left(v, c, K\right))\right), (v : \operatorname{MemoryVertex}\left(n\right) \mapsto \operatorname{subtract}\left(\operatorname{memoryValue}\left(v, 0\right), \operatorname{multiply}\left(\operatorname{power}\left(chi, \operatorname{subtract}\left(K, 1\right)\right), d\right)\right))\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/FixedGraphMargin.graphGapValues` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

MemoryVertex(n) is the original n-letter past, indexed from the most recent letter. graphGapValues includes every allowed high edge of the ambient lower graph, even if that edge is not retained on a bilateral path. Since an edge has target memoryShift(v,c), recording its source vertex records the entire high edge. Its gap is memoryValue(v,0)-chi^(K-1)*d. The edge's strict guard makes each gap positive. These are real comparisons defining an exact finite mathematical object; no effective decision procedure for arbitrary real budgets is asserted.

**Definition 1.2 (graphMargin).**

$$\forall n \in Nat, K \in Nat, d \in Real,\; \operatorname{graphMargin}\left(n, K, d\right) = \operatorname{if}\left(\operatorname{Nonempty}\left(\operatorname{graphGapValues}\left(n, K, d\right)\right), \operatorname{finiteMinimum}\left(\operatorname{graphGapValues}\left(n, K, d\right)\right), 0\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/FixedGraphMargin.graphMargin` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

When graphGapValues is nonempty, graphMargin is its attained finite minimum. finiteMinimum denotes Finset.min' with the nonempty proof supplied by that branch. The zero in the other branch is a placeholder; it is never used as a positive graph margin.

**Theorem 1.3 (graph gap minimum).**

$$\forall n \in Nat, K \in Nat, d \in Real,\; \operatorname{Nonempty}\left(\operatorname{graphGapValues}\left(n, K, d\right)\right) \Rightarrow \left(\operatorname{lt}\left(0, \operatorname{graphMargin}\left(n, K, d\right)\right) \land \operatorname{IsLeast}\left(\operatorname{toSet}\left(\operatorname{graphGapValues}\left(n, K, d\right)\right), \operatorname{graphMargin}\left(n, K, d\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/FixedGraphMargin.graph_gap_minimum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The allowed high-edge set is finite, and every lower-edge gap is strictly positive. Its attained minimum is therefore positive and is exactly epsilon_graph. IsLeast includes membership in the gap set and comparison with every other member; an arbitrary smaller bound is not substituted for the minimum.

**Theorem 1.4 (lower graph high gap).**

$$\forall n \in Nat, K \in Nat, d \in Real,\; \forall omega \in Int \to CuLetter, i \in Int,\; \left(\operatorname{lt}\left(0, K\right) \land \left(\operatorname{le}\left(K, n\right) \land \left(\operatorname{member}\left(omega, \operatorname{MemoryLanguage}\left(lower, n, K, d\right)\right) \land \left(\forall k \in \operatorname{Fin}\left(K\right),\; \operatorname{apply}\left(omega, \operatorname{subtract}\left(i, \operatorname{toInt}\left(k\right)\right)\right) = c\right)\right)\right)\right) \Rightarrow \left(\operatorname{Nonempty}\left(\operatorname{graphGapValues}\left(n, K, d\right)\right) \land \operatorname{le}\left(\operatorname{graphMargin}\left(n, K, d\right), \operatorname{subtract}\left(\operatorname{pastState}\left(omega, i\right), \operatorname{multiply}\left(\operatorname{power}\left(chi, \operatorname{subtract}\left(K, 1\right)\right), d\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/FixedGraphMargin.lower_graph_high_gap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For n at least K and positive K, the unique actual memory path reconstructs the original past word. At a high letter its memoryRun is the original K-letter c-run, so its allowed lower edge contributes to graphGapValues. The zero-seed memory value is at most the bilateral state at that same position. Thus every original high guard is at least tau+epsilon_graph. In particular a graph with no allowed high edge has no high position in any of its bilateral paths.

**Definition 1.5 (resetFloor).**

$$\forall R \in Return,\; \operatorname{resetFloor}\left(R\right) = \operatorname{subtract}\left(\operatorname{hSide}\left(high\right), \operatorname{multiply}\left(\operatorname{power}\left(rho, \operatorname{m}\left(R\right)\right), \operatorname{subtract}\left(\operatorname{hSide}\left(high\right), \operatorname{multiply}\left(chi, \operatorname{aSide}\left(high\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/FixedGraphMargin.resetFloor` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

R=(m(R),1) is the low reset, with paid length 20+6m(R). Its floor B is attained at the auxiliary input A_H. Every actual complete initial state exceeds A_H, and the merged leading u run can only increase the reset output.

**Definition 1.6 (fixedGraphActualMargin).**

$$\forall n \in Nat, K \in Nat, b \in Real, R \in Return,\; \operatorname{fixedGraphActualMargin}\left(n, K, b, R\right) = \operatorname{if}\left(\operatorname{Nonempty}\left(\operatorname{graphGapValues}\left(n, K, \operatorname{divide}\left(\operatorname{divide}\left(\operatorname{subtract}\left(lam, b\right), \operatorname{power}\left(g, 2\right)\right), \operatorname{power}\left(chi, K\right)\right)\right)\right), \operatorname{divide}\left(\operatorname{min}\left(\operatorname{min}\left(\operatorname{subtract}\left(b, \operatorname{actualAutomaticCost}\left(K\right)\right), \operatorname{multiply}\left(\operatorname{multiply}\left(\operatorname{power}\left(g, 2\right), \operatorname{power}\left(chi, K\right)\right), \operatorname{subtract}\left(\operatorname{resetFloor}\left(R\right), \operatorname{divide}\left(\operatorname{divide}\left(\operatorname{subtract}\left(lam, b\right), \operatorname{power}\left(g, 2\right)\right), \operatorname{power}\left(chi, K\right)\right)\right)\right)\right), \operatorname{multiply}\left(\operatorname{multiply}\left(\operatorname{power}\left(g, 2\right), chi\right), \operatorname{graphMargin}\left(n, K, \operatorname{divide}\left(\operatorname{divide}\left(\operatorname{subtract}\left(lam, b\right), \operatorname{power}\left(g, 2\right)\right), \operatorname{power}\left(chi, K\right)\right)\right)\right)\right), 2\right), \operatorname{divide}\left(\operatorname{min}\left(\operatorname{subtract}\left(b, \operatorname{actualAutomaticCost}\left(K\right)\right), \operatorname{multiply}\left(\operatorname{multiply}\left(\operatorname{power}\left(g, 2\right), \operatorname{power}\left(chi, K\right)\right), \operatorname{subtract}\left(\operatorname{resetFloor}\left(R\right), \operatorname{divide}\left(\operatorname{divide}\left(\operatorname{subtract}\left(lam, b\right), \operatorname{power}\left(g, 2\right)\right), \operatorname{power}\left(chi, K\right)\right)\right)\right)\right), 2\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/FixedGraphMargin.fixedGraphActualMargin` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Here d=(lam-b)/g^2/chi^K and tau=chi^(K-1)*d. The three entries are b-C_auto, g^2*chi^K*(B-d), and g^2*chi*epsilon_graph. Taking half their minimum leaves strict room to move every nearest target into its actual color-cell interior, independently of all five ownership flags. If no allowed high edge exists, the graph term is omitted, while the positive reset term is retained as a conservative bound.

**Definition 1.7 (CanonicalFactorCompletion).**

$$\forall R \in Return, w \in \operatorname{List}\left(CuLetter\right), xs \in \operatorname{List}\left(Return\right),\; \operatorname{CanonicalFactorCompletion}\left(R, w, xs\right) = \operatorname{if}\left(\operatorname{member}\left(c, w\right), \exists a \in Nat, first \in Return, rest \in \operatorname{List}\left(Return\right),\; \operatorname{if}\left(\operatorname{getLastOption}\left(w\right) = \operatorname{some}\left(c\right), \operatorname{append}\left(w, \operatorname{singleton}\left(u\right)\right), w\right) = \operatorname{append}\left(\operatorname{replicate}\left(a, u\right), \operatorname{executionWord}\left(\operatorname{cons}\left(first, rest\right)\right)\right) \land xs = \operatorname{cons}\left(\operatorname{Return}\left(\operatorname{add}\left(\operatorname{m}\left(R\right), a\right), 1\right), \operatorname{cons}\left(\operatorname{Return}\left(\operatorname{add}\left(\operatorname{m}\left(first\right), 1\right), \operatorname{r}\left(first\right)\right), rest\right)\right), w = \operatorname{replicate}\left(\operatorname{length}\left(w\right), u\right) \land xs = \operatorname{singleton}\left(\operatorname{Return}\left(\operatorname{add}\left(\operatorname{m}\left(R\right), \operatorname{length}\left(w\right)\right), 1\right)\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/FixedGraphMargin.CanonicalFactorCompletion` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

If w contains c, fill its last return with one terminal u exactly when it ends in c. Parse its leading u run and its positive first and rest returns. Merge the leading run into the reset; add one u immediately after the first visible c-run's return, even if it is low. The construction does not move the extra u to the first high return. An all-u word, including the empty factor, merely extends the reset's u run. Return(m,r) denotes the original positive-exponent constructor. The predicate uses literal runs and no supply or margin conclusion.

**Theorem 1.8 (canonical factor completion unique).**

$$\forall R \in Return, w \in \operatorname{List}\left(CuLetter\right), xs \in \operatorname{List}\left(Return\right), ys \in \operatorname{List}\left(Return\right),\; \left(\operatorname{CanonicalFactorCompletion}\left(R, w, xs\right) \land \operatorname{CanonicalFactorCompletion}\left(R, w, ys\right)\right) \Rightarrow xs = ys$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/FixedGraphMargin.canonical_factor_completion_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The unique leading-run and complete-return decomposition determines the literal completion. Uniqueness is independent of errors, scalar state choices and actual supply.

**Theorem 1.9 (fixed lower graph actual margin).**

$$\forall n \in Nat, K \in Nat, b \in Real,\; \left(\operatorname{le}\left(2, K\right) \land \left(\operatorname{le}\left(K, n\right) \land \left(\operatorname{lt}\left(\operatorname{subtract}\left(lam, \operatorname{multiply}\left(\operatorname{multiply}\left(\operatorname{power}\left(g, 2\right), \operatorname{power}\left(chi, K\right)\right), \operatorname{hSide}\left(high\right)\right)\right), b\right) \land \operatorname{lt}\left(b, \operatorname{subtract}\left(lam, \operatorname{multiply}\left(\operatorname{multiply}\left(\operatorname{power}\left(g, 2\right), \operatorname{power}\left(chi, K\right)\right), \operatorname{divide}\left(\operatorname{aSide}\left(high\right), \operatorname{subtract}\left(1, \operatorname{multiply}\left(rho, \operatorname{power}\left(chi, K\right)\right)\right)\right)\right)\right)\right)\right)\right)\right) \Rightarrow \left(\exists R \in Return,\; \operatorname{r}\left(R\right) = 1 \land \left(\operatorname{lt}\left(\operatorname{max}\left(\operatorname{max}\left(\operatorname{xSide}\left(high\right), \operatorname{ySide}\left(high\right)\right), \operatorname{divide}\left(\operatorname{divide}\left(\operatorname{subtract}\left(lam, b\right), \operatorname{power}\left(g, 2\right)\right), \operatorname{power}\left(chi, K\right)\right)\right), \operatorname{resetFloor}\left(R\right)\right) \land \left(\operatorname{lt}\left(0, \operatorname{fixedGraphActualMargin}\left(n, K, b, R\right)\right) \land \left(\left(\operatorname{Nonempty}\left(\operatorname{graphGapValues}\left(n, K, \operatorname{divide}\left(\operatorname{divide}\left(\operatorname{subtract}\left(lam, b\right), \operatorname{power}\left(g, 2\right)\right), \operatorname{power}\left(chi, K\right)\right)\right)\right) \Rightarrow \left(\operatorname{lt}\left(0, \operatorname{graphMargin}\left(n, K, \operatorname{divide}\left(\operatorname{divide}\left(\operatorname{subtract}\left(lam, b\right), \operatorname{power}\left(g, 2\right)\right), \operatorname{power}\left(chi, K\right)\right)\right)\right) \land \operatorname{IsLeast}\left(\operatorname{toSet}\left(\operatorname{graphGapValues}\left(n, K, \operatorname{divide}\left(\operatorname{divide}\left(\operatorname{subtract}\left(lam, b\right), \operatorname{power}\left(g, 2\right)\right), \operatorname{power}\left(chi, K\right)\right)\right)\right), \operatorname{graphMargin}\left(n, K, \operatorname{divide}\left(\operatorname{divide}\left(\operatorname{subtract}\left(lam, b\right), \operatorname{power}\left(g, 2\right)\right), \operatorname{power}\left(chi, K\right)\right)\right)\right)\right)\right) \land \left(\forall model \in Model, o \in Ownership, w \in \operatorname{List}\left(CuLetter\right),\; \left(\exists omega \in Int \to CuLetter,\; \operatorname{member}\left(omega, \operatorname{MemoryLanguage}\left(lower, n, K, \operatorname{divide}\left(\operatorname{divide}\left(\operatorname{subtract}\left(lam, b\right), \operatorname{power}\left(g, 2\right)\right), \operatorname{power}\left(chi, K\right)\right)\right)\right) \land \operatorname{Occurs}\left(omega, w\right)\right) \Rightarrow \left(\exists xs \in \operatorname{List}\left(Return\right),\; \left(\operatorname{CanonicalFactorCompletion}\left(R, w, xs\right) \land \left(\operatorname{ActualPairSupply}\left(model, o, \operatorname{subtract}\left(b, \operatorname{fixedGraphActualMargin}\left(n, K, b, R\right)\right), strict, xs\right) \land \operatorname{listWeight}\left(xs\right) = \operatorname{add}\left(\operatorname{add}\left(\operatorname{wordWeight}\left(w\right), \operatorname{add}\left(20, \operatorname{multiply}\left(6, \operatorname{m}\left(R\right)\right)\right)\right), \operatorname{if}\left(\operatorname{member}\left(c, w\right), \operatorname{if}\left(\operatorname{getLastOption}\left(w\right) = \operatorname{some}\left(c\right), 12, 6\right), 0\right)\right)\right)\right) \land \left(\forall ys \in \operatorname{List}\left(Return\right),\; \left(\operatorname{CanonicalFactorCompletion}\left(R, w, ys\right) \land \left(\operatorname{ActualPairSupply}\left(model, o, \operatorname{subtract}\left(b, \operatorname{fixedGraphActualMargin}\left(n, K, b, R\right)\right), strict, ys\right) \land \operatorname{listWeight}\left(ys\right) = \operatorname{add}\left(\operatorname{add}\left(\operatorname{wordWeight}\left(w\right), \operatorname{add}\left(20, \operatorname{multiply}\left(6, \operatorname{m}\left(R\right)\right)\right)\right), \operatorname{if}\left(\operatorname{member}\left(c, w\right), \operatorname{if}\left(\operatorname{getLastOption}\left(w\right) = \operatorname{some}\left(c\right), 12, 6\right), 0\right)\right)\right)\right) \Rightarrow ys = xs\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/FixedGraphMargin.fixed_lower_graph_actual_margin` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix K at least two, b in the original transition interval, and n at least K. One finite low reset and one positive epsilon_actual are chosen before all factors, either actual model and every ownership assignment. Each graph factor has exactly its canonical completed list, the displayed weight overhead and strict actual errors below b-epsilon_actual. There is no bound on original or completed length, return exponent m, depth or total weight. The empty and all-u cases have overhead 20+6m(R); c-containing factors add six or twelve according to their original last letter.

The reset protects only the first visible return. If that return is high, its actual input exceeds B, so its active cost is at most b-g^2*chi^K*(B-d); if low, it passes by C_auto. The extra u then makes its completed output dominate the original auxiliary output. Later high returns inherit the graph guard, including the first high return after a low first return. The invariant along their live recurrence is min(B,d+epsilon_graph/chi^(K-1)); multiplying its gap by g^2*chi^K gives exactly the minimum of the reset and graph cost gains. It does not rely on a positive infimum of per-factor strict gaps. With no allowed high edge the auxiliary guard is vacuous, so the reset-only half minimum suffices.

ActualPairSupply uses the same completed execution list on both original literal sources. It reads every departure of the stem, paid anchor when present, and all repeated blocks. Beyond the history length the error is zero, and the full future is the zero-error readout of each original literal tail. The auxiliary bilateral sequence is used only for the occurrence and its quantitative guard. It is not an actual eventually-empty source. A fixed graph's margin may shrink as n changes; this theorem does not supply a common margin over all memory graphs or identify a global decoder optimum.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/FixedGraphMargin.CanonicalFactorCompletion`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/FixedGraphMargin.canonical_factor_completion_unique`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/FixedGraphMargin.fixedGraphActualMargin`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/FixedGraphMargin.fixed_lower_graph_actual_margin`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/FixedGraphMargin.graphGapValues`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/FixedGraphMargin.graphMargin`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/FixedGraphMargin.graph_gap_minimum`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/FixedGraphMargin.lower_graph_high_gap`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/FixedGraphMargin.resetFloor`
- Dependency: [D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/Completion](Completion.md)
- Dependency: [D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/InteriorRoot](InteriorRoot.md)
