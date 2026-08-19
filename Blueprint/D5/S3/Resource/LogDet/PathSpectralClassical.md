# Path and Spectral Forms of the Log-Determinant Divergence

## Abstract

The log-determinant divergence has matching path, spectral, geometric-kernel, and classical forms.

**Theorem 1.1 (The log-det divergence has path, spectral, kernel, and classical forms).**

$$\begin{gathered}n \in \mathbb{N},\quad\rho, \sigma \in M_{n}(\mathbb{C}), \operatorname{PosDef}(\rho) \land \operatorname{PosDef}(\sigma) \longrightarrow \\ (\operatorname{logDetDivergence}(\rho, \sigma) = \int_{0}^{1}(1-s) \Re{\operatorname{tr}((m_{s}^{-1} \Delta)^{2})} ds, m_{s} = (1-s)\sigma + s\rho, \Delta = \rho - \sigma) \land \\ (\operatorname{logDetDivergence}(\rho, \sigma) = \sum_{i} h(\Lambda_{i}), (\Lambda_{i})_{i} = \operatorname{spec}(\sigma^{-\frac{1}{2}} \rho \sigma^{-\frac{1}{2}}), h(t) = t - \operatorname{log}(t) - 1) \land \\ (\forall a, b > 0,\quad\frac{1}{ab} = (\frac{k_{G}(a, b)}{2})^{2}, k_{G}(a, b) = \frac{2}{\sqrt{ab}}) \land \\ (\forall p, q \in \mathbb{R}^{n},\quad(\forall i, 0 < p_{i} \land 0 < q_{i}) \longrightarrow \operatorname{logDetDivergence}(\operatorname{diag}(p), \operatorname{diag}(q)) = \sum_{i}(\frac{p_{i}}{q_{i}} - \operatorname{log}(\frac{p_{i}}{q_{i}}) - 1)) \end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Resource/LogDet/PathSpectralClassical.log_det_path_spectral_classical` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive-definite complex matrices, the divergence is the weighted trace energy along their affine segment. Congruence by the inverse positive square root of sigma gives a positive-definite relative matrix whose eigenvalues yield the same divergence through the profile h(t) = t - log(t) - 1.

For positive scalar arguments, the reciprocal-product kernel is exactly the square of half the geometric kernel. Restricting the matrices to positive real diagonals gives the coordinatewise Itakura-Saito sum.

The proof derives the scalar integral by an explicit antiderivative, uses Hermitian functional calculus for the matrix path, and applies the trace and determinant eigenvalue formulas for the spectral form.

## References

- Truth anchor: `D5/S3/Resource/LogDet/PathSpectralClassical.log_det_path_spectral_classical`
