# Finite History Stability

## Abstract

Finite observation histories stabilize and their class growth is bounded by the finite carrier.

**Theorem 1.1 (Finite history stability).**

$$\begin{gathered}\forall X, Q, {}[\operatorname{Fintype}(X)], \tau: X \to X, q: X \to Q,\\{}c_{m} = \lvert X / R_{m} \rvert, m_{*} = \operatorname{sInf} \{m \in \mathbb{N} \mid R_{m} = R_{m+1}\},\\{}\forall m, (x, y) \in R_{m+1} \Rightarrow (x, y) \in R_{m} \land \\{}\forall m, c_{m} \leq c_{m+1} \land \\{}R_{m_{*}} = R_{\infty} \land \\{}\forall n, m_{*} \leq n \Rightarrow R_{n} = R_{\infty} \land \\{}m_{*} \leq c_{m_{*}} - c_{0} \land \\{}c_{m_{*}} - c_{0} \leq \lvert X \rvert - c_{0}.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Separation/FiniteHistoryStability.finite_history_stability` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a finite state carrier X, update tau, and readout q, let R_m relate states whose observations agree from time zero through time m, and let R_infinity require agreement at every finite future time. The quotient class count at depth m is c_m.

The finite relations decrease with depth, while their quotient class counts increase. A finite stability depth m_star reaches the infinite-future relation, and every later depth has that same relation.

Each strict refinement before m_star consumes a new quotient class. Consequently m_star is bounded by c_m_star minus c_0, and that increase is at most the carrier cardinality minus c_0. The proof handles the empty finite carrier directly and uses a private range corestriction only to apply the existing surjective-readout bound.

The source's qualitative remark that the depth may depend on the whole system has no in-scope quantitative predicate and is therefore not asserted as a universal formal clause.

## References

- Truth anchor: `D5/S3/Observer/Separation/FiniteHistoryStability.finite_history_stability`
