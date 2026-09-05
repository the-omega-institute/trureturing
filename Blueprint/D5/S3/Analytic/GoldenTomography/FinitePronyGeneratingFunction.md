# Finite Prony Generating Function

## Abstract

A finite Prony moment sequence has a rational generating function on its common convergence disk.

**Theorem 1.1 (Finite exponential moments have the expected partial-fraction generating function).**

$$\operatorname{Summable}(c_{n}\cdot z^{n}) \land \operatorname{G}(z) = \sum_{j} \frac{w_{j}}{1-x_{j}\cdot z}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GoldenTomography/FinitePronyGeneratingFunction.finite_prony_rational_generating_function` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a finite family of nodes and weights, assume each product of a node with the generating-function variable has norm below one. The moment power series is then summable and equals the finite sum of weights multiplied by the reciprocals of one minus the corresponding node-variable products.

The proof applies the geometric-series theorem to each mode and commutes only a finite mode sum with the convergent time series. It supplies the exact rational-transfer layer used by Prony and finite Koopman methods. It asserts no meromorphic continuation, infinite-mode interchange, or noisy reconstruction bound.

## References

- Truth anchor: `D5/S3/Analytic/GoldenTomography/FinitePronyGeneratingFunction.finite_prony_rational_generating_function`
- Dependency: [D5/S3/Analytic/GoldenTomography/FinitePronyHankelReconstruction](FinitePronyHankelReconstruction.md)
