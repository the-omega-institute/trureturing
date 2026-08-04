# Hidden Fiber Compactness

## Abstract

The hidden fiber is closed, compact, and sequentially compact coordinatewise.

**Theorem 1.1 (The hidden fiber is compact in every equivalent sense).**

$$\Sigma=\left\{\theta:\mathbb{N}_{>0}\to\mathbb{R}/\mathbb{Z}\ \middle|\ \forall m,n\in\mathbb{N}_{>0},\ n\theta_{mn}=\theta_m\right\},\quad \pi(\theta)=\theta_1,\quad K_{\infty}=\ker\pi=\{\theta\in\Sigma\mid\theta_1=0\}:\quad K_{\infty}\ \text{is closed}\ \land\ K_{\infty}\ \text{is compact}\ \land\ \forall (x_j)_{j\in\mathbb{N}}\subseteq K_{\infty},\ \exists x\in K_{\infty},\ \exists \phi:\mathbb{N}\to\mathbb{N},\ \phi\ \text{strictly increasing}\ \land\ \forall m\in\mathbb{N}_{>0},\ x_{\phi(j),m}\longrightarrow x_m.$$

*Proof.* Machine-checked in Lean as `D5/S1/Solenoid/HiddenFiberCompact.hiddenFiber_closed_compact_seqCompact` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Continuity of the visible projection makes its zero fiber closed. The ambient solenoid is compact, so the fiber is compact. Its countable product topology is first countable, hence compactness gives a convergent subsequence; the formal coordinatewise convergence equivalence identifies this with the diagonal, layer-by-layer limit.
