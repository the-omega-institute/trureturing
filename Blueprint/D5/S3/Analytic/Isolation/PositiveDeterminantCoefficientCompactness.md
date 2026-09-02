# Positive Determinant Coefficient Compactness

## Abstract

Coefficientwise limits of positive finite matrix determinants converge locally uniformly and retain their zero locus.

**Theorem 1.1 (Positive determinant coefficients determine the compact limit).**

$$\forall r: \mathbb{N} \to \mathbb{N}, \\{}A: {N: \mathbb{N}} \to Matrix\left(Fin\left(r\left(N\right)\right), Fin\left(r\left(N\right)\right), \mathbb{C}\right), \\{}Q: \mathbb{C} \to \mathbb{C}, \\{}{{\forall N\in \mathbb{N}, PosSemidef\left(A\left(N\right)\right)} \land {Differentiable\left(\mathbb{C}, Q\right)} \land {Q\left(0\right) = 1} \land {\forall m\in \mathbb{N}, Tendsto\left((N) \mapsto coefficient\left(m, (w \mapsto det\left(1 + w \cdot A\left(N\right)\right))\right), atTop, inv\left((m!)\right) \cdot iteratedDeriv\left(m, Q, 0\right)\right)}} \Rightarrow \\{}{{TendstoLocallyUniformly\left((N, w) \mapsto det\left(1 + w \cdot A\left(N\right)\right), Q, atTop\right)} \land {\forall w\in \mathbb{C}, Q\left(w\right) = 0 \Rightarrow {Im\left(w\right) = 0 \land Re\left(w\right) \le 0}}}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Isolation/PositiveDeterminantCoefficientCompactness.positive_determinant_coefficient_compactness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each index, the source positive finite-rank operator is represented on its finite range by a positive semidefinite complex matrix. The coefficient premise is displayed for the determinant polynomial itself, with the target coefficient given by the corresponding Taylor derivative of the entire function.

The first coefficient bounds the traces eventually. Positivity and the spectral factorization then bound every determinant on each circle by one exponential constant. Cauchy estimates and dominated convergence of the Taylor series yield locally uniform convergence.

The public conclusion retains both clauses: locally uniform convergence of the determinant family and the nonpositive real location of every zero of the normalized limit.

## References

- Truth anchor: `D5/S3/Analytic/Isolation/PositiveDeterminantCoefficientCompactness.positive_determinant_coefficient_compactness`
- Dependency: [D5/S3/Analytic/Isolation/PositiveFredholmLimitZeros](PositiveFredholmLimitZeros.md)
