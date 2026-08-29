# Exponential Finite-Moment Transfer

## Abstract

Exponentially bounded Cayley coefficients give a certified finite-moment tail.

**Theorem 1.1 (Cayley moment truncation has an exponential tail bound).**

$$\begin{gathered}\forall n, M: \mathbb{N},\\{}r, rho, R: \mathbb{R},\\{}m, c: \mathbb{N} \to \mathbb{C},b: \mathbb{C},\\{}(1 < rho < \left|r\right|^{-1}) \land\\{}(\forall k: \mathbb{N}, \left\lVert m_{k} \right\rVert \leq R) \land\\{}(\forall k: \mathbb{N}, \left\lVert c_{k} \right\rVert \leq \frac{(1 + \left|r\right|)^{2} rho (rho + \left|r\right|)^{n - 1}}{(1 - \left|r\right| rho)^{n + 1}} rho^{-k}) \land\\{}\operatorname{HasSum}(k \mapsto c_{k} m_{k}, b) \Rightarrow\\{}\left\lVert b - \sum_{k=0}^{M} c_{k} m_{k} \right\rVert \leq \frac{R \frac{(1 + \left|r\right|)^{2} rho (rho + \left|r\right|)^{n - 1}}{(1 - \left|r\right| rho)^{n + 1}} rho^{-(M + 1)}}{1 - rho^{-1}}.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Budget/ExponentialFiniteMomentTransfer.exponential_finite_moment_transfer` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The source and target moments are complex, while the scale, radius, and Cauchy envelope are real. The public statement retains the complete moment-transfer sum, the uniform moment bound, and the coefficient estimate at the chosen radius.

The scale inequalities make the reciprocal radius a geometric ratio strictly between zero and one. Splitting the convergent transfer series after depth M and summing its norm majorant gives exactly the displayed remainder.

Repository and pinned-library searches found no exact combined transfer theorem. The proof uses the library's natural-index tail split, norm-of-sum bound, and closed form for a real geometric series.

## References

- Truth anchor: `D5/S3/Weil/Budget/ExponentialFiniteMomentTransfer.exponential_finite_moment_transfer`
