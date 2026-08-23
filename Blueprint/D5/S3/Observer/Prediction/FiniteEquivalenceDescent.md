# Finite Equivalence Descent

## Abstract

Finite equivalence refinement stabilizes within its quotient-class budget.

**Theorem 1.1 (Finite descent and general stability bound).**

$$\begin{gathered}\forall Y, [\operatorname{Fintype}(Y)], R: \operatorname{Setoid}(Y), \tau: Y \to Y,\\{}R_{0} = R \land \\{}(\forall m, R_{m+1} = \{(x, y) \mid R(x, y) \land R_{m}(\tau(x), \tau(y))\}) \land \\{}(\forall m, R_{m} = \{(x, y) \mid \forall k, k \leq m \Rightarrow R(\tau^{k}(x), \tau^{k}(y))\}) \land \\{}C_{\tau}(R) = \{(x, y) \mid \forall k, R(\tau^{k}(x), \tau^{k}(y))\} \land \\{}m_{R} = \operatorname{sInf} \{m \in \mathbb{N} \mid R_{m} = R_{m+1}\} \land R_{m_{R}} = R_{m_{R}+1} \land \\{}(\forall n, R_{n} = R_{n+1} \Rightarrow m_{R} \leq n) \land \\{}(\forall n, m_{R} \leq n \Rightarrow R_{n} = C_{\tau}(R)) \land \\{}m_{R} \leq \lvert Y/C_{\tau}(R) \rvert - \lvert Y/R \rvert \leq \lvert Y \rvert - \lvert Y/R \rvert.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Prediction/FiniteEquivalenceDescent.finite_equivalence_descent_and_stability_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let Y be a finite carrier, R an equivalence relation, and tau its deterministic update. The canonical readout sends each state to its R-class. Equality of finite readout words then constructs the source sequence directly from R and iterates of tau.

The zero and successor clauses identify this sequence with repeated intersection by the one-step pullback. The finite-intersection formula states equivalently that two states remain related at every iterate from zero through the chosen depth.

The displayed depth is the least index where consecutive finite relations agree. At that depth and every later one, the relation is the canonical all-future core.

The terminal quotient can gain at most one unit of stability depth per new class. This gives the sharp difference between terminal and initial quotient counts, followed by the carrier bound. The empty finite carrier is included and handled directly.

## References

- Truth anchor: `D5/S3/Observer/Prediction/FiniteEquivalenceDescent.finite_equivalence_descent_and_stability_bound`
- Dependency: [D5/S3/Observer/Prediction/StableDepthCardinalityBounds](StableDepthCardinalityBounds.md)
