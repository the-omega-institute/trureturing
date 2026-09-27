# Residual Tail Contraction for General Instruments

## Abstract

The residual above the maximal fixed survival effect contracts geometrically, has a summable tail, and determines a unique dominated solution of the residual Poisson equation.

**Theorem 1.1 (Geometric contraction and the residual Poisson solution).**

$$\forall d: \mathbb{N}, \alpha: \operatorname{Type}, \iota: \operatorname{Type}, [\operatorname{Fintype}(\alpha)], [\operatorname{Fintype}(\iota)],\\{}Q: {\alpha} \to \operatorname{Matrix}(\operatorname{Fin}(d), \operatorname{Fin}(d), \mathbb{C}), L: {\iota} \to \operatorname{Matrix}(\operatorname{Fin}(d), \operatorname{Fin}(d), \mathbb{C}), F: \operatorname{Matrix}(\operatorname{Fin}(d), \operatorname{Fin}(d), \mathbb{C}),\\{}\sum_{a \in \alpha} Q_{a}^{*} Q_{a} + \sum_{i \in \iota} L_{i}^{*} L_{i} = I \Rightarrow \lim_{n \to \infty} S_{n} = F \Rightarrow\\{}\forall n \in \mathbb{N}, S_{n} - F = {\mathcal{A}}^{n}(I - F) \land 0 \leq S_{n} - F \leq I - F \land\\{}I - F \neq 0 \Rightarrow \exists M \in \mathbb{N}, 1 \leq M \land \exists q \in \mathbb{R}, 0 < q < 1 \land\\{}S_{M} - F \leq q {I - F} \land \forall n \in \mathbb{N}, S_{n} - F \leq q^{\lfloor\frac{n}{M}\rfloor} {I - F} \land \operatorname{Summable}(n \mapsto S_{n} - F) \land\\{}T = \sum_{n=0}^{\infty} S_{n} - F, 0 \leq T \land T \leq \frac{M}{{1 - q}} {I - F} \land T - \mathcal{A}(T) = I - F \land\\{}\forall k \in \mathbb{N}, 0 \leq T - \sum_{n < k M} S_{n} - F \land T - \sum_{n < k M} S_{n} - F \leq \frac{M q^{k}}{{1 - q}} {I - F} \land \forall X: \operatorname{Matrix}(\operatorname{Fin}(d), \operatorname{Fin}(d), \mathbb{C}), c: \mathbb{R}, X - \mathcal{A}(X) = I - F \Rightarrow 0 \leq X \Rightarrow X \leq c {I - F} \Rightarrow X = T.$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/GeneralInstrumentResidualTailContraction.residual_tail_contraction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let A be the dual no-click map, let S_n be its n-fold action on the identity, and let F be the limiting survival effect. Write R = I - F and R_n = S_n - F. The residuals are positive, decrease in the Loewner order, and equal A^n(R).

When R is nonzero, finite-dimensional spectral comparison gives a block length M for which R_M is at most one strict scalar multiple of R. Positivity and monotonicity propagate this estimate to every residual, so the residual series is summable and its block tails obey a geometric bound.

The sum T of the residuals is positive, is bounded by the corresponding geometric majorant, and satisfies T - A(T) = R. Iterating the same equation shows that any positive solution dominated by a scalar multiple of R has a remainder tending to zero, and therefore equals T.

## References

- Truth anchor: `D5/S3/Quantum/Measurement/GeneralInstrumentResidualTailContraction.residual_tail_contraction`
- Dependency: [D5/S3/Quantum/Measurement/GeneralInstrumentSurvivalLimit](GeneralInstrumentSurvivalLimit.md)
