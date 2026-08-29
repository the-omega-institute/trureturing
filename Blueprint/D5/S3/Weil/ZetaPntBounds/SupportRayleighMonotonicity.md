# Support Rayleigh Monotonicity

## Abstract

A support-window enlargement expands the normalized Weil test class and cannot increase the lowest Rayleigh value of a window-invariant quadratic cost.

**Theorem 1.1 (The lowest Rayleigh value is antitone under support enlargement).**

$$\begin{aligned}\forall q: \mathbb{R} \to \mathcal{W} \to \mathbb{R}, L_{1}, L_{2}\in \mathbb{R},\\\operatorname{let} R_{1} = \{\operatorname{q}\left(L_{1}, f\right) \mid f \in \mathcal{W}, \operatorname{tsupport}\left(f\right) \subseteq \operatorname{Ioo}\left(-L_{1}, L_{1}\right) \land \operatorname{l2Mass}\left(f\right) = 1\},\\R_{2} = \{\operatorname{q}\left(L_{2}, f\right) \mid f \in \mathcal{W}, \operatorname{tsupport}\left(f\right) \subseteq \operatorname{Ioo}\left(-L_{2}, L_{2}\right) \land \operatorname{l2Mass}\left(f\right) = 1\},\\L_{1} < L_{2} \land {\forall f\in \mathcal{W}, \operatorname{tsupport}\left(f\right) \subseteq \operatorname{Ioo}\left(-L_{1}, L_{1}\right) \Rightarrow \operatorname{q}\left(L_{2}, f\right) = \operatorname{q}\left(L_{1}, f\right)} \land \operatorname{BddBelow}\left(R_{2}\right) \land \operatorname{Nonempty}\left(R_{1}\right) \Rightarrow \operatorname{sInf}\left(R_{2}\right) \leq \operatorname{sInf}\left(R_{1}\right).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaPntBounds/SupportRayleighMonotonicity.support_rayleigh_monotonicity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

W is the canonical carrier of even smooth compactly supported complex tests, and l2Mass is its canonical squared real-line mass. The two displayed sets are the attained quadratic-cost values on unit-mass tests in the respective open windows.

The window-invariance premise is the source clause that the explicit formula value does not change when a smaller-supported test is viewed in a larger external window. Set inclusion and the conditional-complete-lattice infimum lemma yield the result.

## References

- Truth anchor: `D5/S3/Weil/ZetaPntBounds/SupportRayleighMonotonicity.support_rayleigh_monotonicity`
- Dependency: [D5/S3/Weil/ZetaGamma/ArchimedeanJumpDecomposition](../ZetaGamma/ArchimedeanJumpDecomposition.md)
