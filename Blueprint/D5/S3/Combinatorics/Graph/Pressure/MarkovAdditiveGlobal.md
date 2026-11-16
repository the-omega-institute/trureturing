# Global Markov pressure and exact Doob rebasing

## Abstract

Global Markov pressure and exact Doob rebasing

**Theorem 1.1 (Positive normalized actual Perron data).**

Lean statement: `D5/S3/Combinatorics/Graph/Pressure/MarkovAdditiveGlobal.perronVector_spec`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Pressure/MarkovAdditiveGlobal.perronVector_spec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each real tilt, the globally chosen Perron vector is strictly positive, has pi average one, and solves the tilted eigenrelation with the actual positive complex spectral radius. These same normalized data determine the global Doob kernel and, for the two-state source, the amplitude coordinate and exact activity identity.

**Theorem 1.2 (Exact Perron rebase).**

Lean statement: `D5/S3/Combinatorics/Graph/Pressure/MarkovAdditiveGlobal.eigenvalue_rebase`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Pressure/MarkovAdditiveGlobal.eigenvalue_rebase` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite nonempty state type with decidable equality, irreducible nonnegative transition matrix P with a positive normalized stationary row pi, and arbitrary real directed edge reward g, construct positive Perron data for every actual tilt T_a(i,j)=P(i,j)exp(a g(i,j)). Normalize its right vector r_a by the fixed row pi. The kernel Q_a(i,j)=T_a(i,j)r_a(j)/(lambda(a)r_a(i)) is row stochastic, irreducible and has exactly the positive support of P. For all real a and s, diagonal similarity transports the positive Perron vector of Q_a exp(s g) to one for T_(a+s). Identification with the actual complex spectral radius gives lambda(a+s)=lambda(a)lambda_Qa(s), hence p(a+s)=p(a)+p_Qa(s).

**Theorem 1.3 (Globally twice continuously differentiable pressure).**

Lean statement: `D5/S3/Combinatorics/Graph/Pressure/MarkovAdditiveGlobal.pressure_contDiff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Pressure/MarkovAdditiveGlobal.pressure_contDiff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At each real a, apply the constructed local implicit eigenbranch at the actual stochastic Q_a and translate its parameter by a. The exact rebase identity proves that p is globally C2. This uses neither a preassigned smooth Perron branch nor a mixing series.

**Theorem 1.4 (Curvature at every real tilt).**

Lean statement: `D5/S3/Combinatorics/Graph/Pressure/MarkovAdditiveGlobal.pressure_second_derivative`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Pressure/MarkovAdditiveGlobal.pressure_second_derivative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real a, construct the positive stationary row of Q_a and its centered Poisson corrector for the same reward g. Then p second(a) is the stationary Q_a average of the squared corrected increment g-m_a+h_a(next)-h_a(source). Every real parameter is included. The proof permits periodicity, unsupported edges, directed nonreversible support, singleton states and zero variance. A reward is a supported constant plus a directed vertex difference exactly when its variance rate vanishes. Otherwise the variance at every actual rebased kernel is positive, since the support is unchanged. In the coboundary case g=c+f(source)-f(target), the positive vector exp(t f) has eigenvalue exp(t c); harmonic uniqueness identifies the normalized Perron vector and proves p(t)=ct and Q_t=P globally.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Pressure/MarkovAdditiveGlobal.eigenvalue_rebase`
- Truth anchor: `D5/S3/Combinatorics/Graph/Pressure/MarkovAdditiveGlobal.perronVector_spec`
- Truth anchor: `D5/S3/Combinatorics/Graph/Pressure/MarkovAdditiveGlobal.pressure_contDiff`
- Truth anchor: `D5/S3/Combinatorics/Graph/Pressure/MarkovAdditiveGlobal.pressure_second_derivative`
- Dependency: [D5/S3/Combinatorics/Graph/Pressure/MarkovAdditiveCurvature](MarkovAdditiveCurvature.md)
