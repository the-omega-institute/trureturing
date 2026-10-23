# Polynomial preprocessing before a total verifier

## Abstract

Polynomial preprocessing before a total verifier.

A true-halting polynomial transducer first writes its exact output. The unchanged verifier then executes on that output with either Boolean result. Counted same-model simulations prove total polynomial time; determinism gives an equivalence of acceptance on every raw word. This theorem does not infer decision transport from the transducer-only composition interface.

**Theorem 1.1 (preprocess).**

$$\forall f \in \mathit{WordFunction},\; \operatorname{PolyTime}\left(f\right) \Rightarrow \left(\forall M \in \mathit{Machine},\; \operatorname{PolynomialTimeMachine}\left(M\right) \Rightarrow \left(\exists N \in \mathit{Machine},\; \operatorname{PolynomialTimeMachine}\left(N\right) \land \left(\forall x \in \mathit{Word},\; \operatorname{Accepts}\left(N, x\right) \Leftrightarrow \operatorname{Accepts}\left(M, \operatorname{f}\left(x\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Computability/BinaryMachine/DecisionComposition.preprocess` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* RBarish-UTokyo (2026). *NPCompleteness-Lean4 finite binary machine and composition source*. URL: <https://github.com/RBarish-UTokyo/NPCompleteness-Lean4/tree/3e603e795b44fedcf7d6dd65b7d1e30547ead925>.

*Commentary.*

A true-halting polynomial transducer first writes its exact output. The unchanged verifier then executes on that output with either Boolean result. Counted same-model simulations prove total polynomial time; determinism gives an equivalence of acceptance on every raw word. This theorem does not infer decision transport from the transducer-only composition interface.

## References

- Truth anchor: `D5/S0/Computability/BinaryMachine/DecisionComposition.preprocess`
- Dependency: [D5/S0/Computability/BinaryMachine/DecisionSimulation](DecisionSimulation.md)
