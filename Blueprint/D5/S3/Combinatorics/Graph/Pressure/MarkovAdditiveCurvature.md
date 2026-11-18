# Normalized Markov Poisson inverse and local pressure curvature

## Abstract

Normalized Markov Poisson inverse and local pressure curvature

**Theorem 1.1 (Centered Poisson inverse).**

Lean statement: `D5/S3/Combinatorics/Graph/Pressure/MarkovAdditiveCurvature.poisson_spec`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Pressure/MarkovAdditiveCurvature.poisson_spec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite nonempty state type V with decidable equality, every irreducible row-stochastic real matrix P, and every strictly positive normalized stationary row pi, every b with pi dot b=0 has the constructed centered solution h to h-P h=b. The solution comes from the explicit square map L(v,c)=((P-I)v-c1,pi dot v). Harmonic maxima propagate along supported paths, proving injectivity; finite dimensionality supplies its continuous inverse. The same inverse constructs the second corrector u with u-Pu=h.

**Theorem 1.2 (Derived normalized positive eigenbranch).**

Lean statement: `D5/S3/Combinatorics/Graph/Pressure/MarkovAdditiveCurvature.local_perron_branch`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Pressure/MarkovAdditiveCurvature.local_perron_branch` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Stationary pi is available by normalizing the existing transpose-Perron positive eigenvector; summing its coordinates forces eigenvalue one. For arbitrary real edge reward g, the tilt is T_t(i,j)=P(i,j)exp(t g(i,j)). The actual implicit-function theorem produces a C2 germ psi(t)=(r(t),lambda(t)) at zero with psi(0)=(1,1), pi dot r(t)=1, positive coordinates, and T_t r(t)=lambda(t)r(t). The total derivative is computed and its vector-scalar partial derivative is the same L. The branch is identified with the actual complex spectral radius through the existing Collatz-Wielandt bounds. Other peripheral eigenvalues are permitted.

**Theorem 1.3 (Pressure Hessian equals corrected variance).**

Lean statement: `D5/S3/Combinatorics/Graph/Pressure/MarkovAdditiveCurvature.pressure_second_derivative_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Pressure/MarkovAdditiveCurvature.pressure_second_derivative_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let m=sum_ij pi_i P_ij g_ij, b_i=sum_j P_ij(g_ij-m), h=Poisson(b), and xi_ij=g_ij-m+h_j-h_i. Actual pressure is the logarithm of the real value of the complex spectral radius of T_t. The proof derives r prime at zero=h, lambda prime at zero=m, and p prime at zero=m. Twice differentiate the normalized eigenrelation, sum against pi, cancel the unknown second right-vector derivative by stationarity, and expand the square using the Poisson equation. This proves p second at zero=sum_ij pi_i P_ij xi_ij squared.

**Theorem 1.4 (Supported zero-variance obstruction).**

Lean statement: `D5/S3/Combinatorics/Graph/Pressure/MarkovAdditiveCurvature.varianceRate_eq_zero_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Pressure/MarkovAdditiveCurvature.varianceRate_eq_zero_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The corrected-square variance is zero exactly when g_ij=m+h_i-h_j for every edge with P_ij>0. Positive pi and positive support weights make each supported square zero. No condition is imposed on unsupported rewards. The statement includes periodic and nonreversible chains and singleton state spaces. The global strict-curvature and closed-walk converses are separate proof obligations, not consequences asserted here.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Pressure/MarkovAdditiveCurvature.local_perron_branch`
- Truth anchor: `D5/S3/Combinatorics/Graph/Pressure/MarkovAdditiveCurvature.poisson_spec`
- Truth anchor: `D5/S3/Combinatorics/Graph/Pressure/MarkovAdditiveCurvature.pressure_second_derivative_zero`
- Truth anchor: `D5/S3/Combinatorics/Graph/Pressure/MarkovAdditiveCurvature.varianceRate_eq_zero_iff`
- Dependency: [D5/S3/Combinatorics/Graph/Pressure/WeightedWalks](WeightedWalks.md)
