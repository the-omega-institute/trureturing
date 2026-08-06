# Fibonacci Substitution Spectrum

## Abstract

The Fibonacci substitution has two golden eigenpairs and an exact contracting error.

**Theorem 1.1 (Golden eigenpairs and contracting error).**

$$\forall n \in \mathbb{N},\ \operatorname{expandingEigenvector}\neq 0 \land \operatorname{fibonacciSubstitution}\operatorname{expandingEigenvector}=\varphi\operatorname{expandingEigenvector} \land \operatorname{contractingEigenvector}\neq 0 \land \operatorname{fibonacciSubstitution}\operatorname{contractingEigenvector}=\operatorname{contractingEigenvalue}\operatorname{contractingEigenvector} \land (F_{n}\varphi-F_{n+1})=-\operatorname{contractingEigenvalue}^{n}$$

*Proof.* Machine-checked in Lean as `D5/S1/Scale/FibonacciEigen.fibonacci_substitution_spec` (`✓ std3`). ∎

*Citation.* Thomas Koshy (2001). *Fibonacci and Lucas Numbers with Applications*. DOI: [10.1002/9781118033067](https://doi.org/10.1002/9781118033067).

*Commentary.*

The explicit substitution matrix has nonzero expanding and contracting eigenvectors, and the same theorem gives the exact signed Fibonacci error for every natural index.

## References

- Dependency: [D5/S0/Carrier/GoldenRatio](../../S0/Carrier/GoldenRatio.md)
