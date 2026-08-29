# Finite-Window Haar-Floor Interval

## Abstract

An operator-norm certificate for windowed Toeplitz moments gives a rigorous two-sided interval for the finite Haar floor.

**Theorem 1.1 (Windowed Toeplitz data bounds the exact Haar floor).**

$$\begin{aligned}\forall N: \mathbb{N}, c,chat: \mathbb{Z} \to \mathbb{C}, tau: \mathbb{N} \to \mathbb{R},\\\forall r \in \mathbb{Z},\; \overline{c\left(r\right)} = c\left(-r\right) \land \forall r \in \mathbb{Z},\; \overline{chat\left(r\right)} = chat\left(-r\right),\\\operatorname{let} T = \operatorname{Matrix}((j,k\in\operatorname{Fin}(N+1) \mapsto c\left(j-k\right))), \operatorname{let} That = \operatorname{Matrix}((j,k\in\operatorname{Fin}(N+1) \mapsto chat\left(j-k\right))),\\\operatorname{let} Delta = 2 \cdot \sum_{k=1}^{N} tau\left(k\right), \operatorname{opNorm}(T-That) \leq Delta \Rightarrow\\\operatorname{lambdaMin}(That) - Delta \leq \operatorname{lambdaMin}(T) \land \operatorname{lambdaMin}(T) \leq \operatorname{lambdaMin}(That) + Delta.\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Budget/FiniteWindowHaarFloorInterval.finite_window_haar_floor_interval` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The two integer-indexed moment functions construct the true and windowed Toeplitz matrices entry by entry. Their displayed conjugate symmetries make both matrices Hermitian.

The error radius is exactly twice the finite sum of the supplied tail bounds. If it dominates the matrix operator-norm error, the true smallest eigenvalue lies within that radius of the windowed smallest eigenvalue.

The Lean proof identifies each smallest Hermitian eigenvalue with the infimum of its Rayleigh quotient and applies the operator norm bound in both directions.

## References

- Truth anchor: `D5/S3/Weil/Budget/FiniteWindowHaarFloorInterval.finite_window_haar_floor_interval`
