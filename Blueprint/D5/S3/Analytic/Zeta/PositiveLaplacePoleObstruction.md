# Positive Laplace transforms and zeta poles

## Abstract

Positivity bounds the zeta residues of a continued Laplace transform.

**Theorem 1.1 (Convergence throughout the regular real ray).**

Lean statement: `D5/S3/Analytic/Zeta/PositiveLaplacePoleObstruction.laplace_integrable`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Zeta/PositiveLaplacePoleObstruction.laplace_integrable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let mu be a positive measure supported on nonnegative reals, with Laplace integral L(s) converging for every real part greater than B. Let x0>1 and let R be holomorphic for Re(s)>a. Suppose in the initial overlap L(s)=e*P(s)+R(s)+k*x0^(-s)/s, where P(s) is minus one half the logarithmic derivative of (z-1)*zeta(z), evaluated at z=s+1/2. Then the defining integral converges for every real sigma>max(a,0). Multiplication by s times the normalized zeta factor propagates the initial identity on the connected convergence domain. The normalized factor has no positive real zeros. The nonnegative Laplace boundary theorem therefore excludes a convergence boundary on the available real ray.

**Theorem 1.2 (Exclusion of a positive translated zero).**

Lean statement: `D5/S3/Analytic/Zeta/PositiveLaplacePoleObstruction.no_positive_pole`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Zeta/PositiveLaplacePoleObstruction.no_positive_pole` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the preceding hypotheses, assume |e|=1. Every nontrivial zeta zero rho satisfies Re(rho)-1/2<=max(a,0). Otherwise its translated pole lies in the interior of actual Laplace convergence. The actual transform is analytic there, whereas its continued expression has nonzero residue -e*m/2 for the positive zero multiplicity m. Multiplication by the distance from the pole gives incompatible limits.

**Theorem 1.3 (The one-half budget at an imaginary-axis pole).**

Lean statement: `D5/S3/Analytic/Zeta/PositiveLaplacePoleObstruction.critical_pole_budget`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Zeta/PositiveLaplacePoleObstruction.critical_pole_budget` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the same hypotheses, assume a<0, |e|=1, and let rho be a nontrivial zero with Re(rho)=1/2. Then k>=1/2. For sigma tending to zero from above, sigma*L(sigma) tends to k, while sigma*L(sigma+i*Im(rho)) tends to -e*m/2. The triangle inequality for the same positive integral bounds the modulus of the second expression by the first real expression. Taking limits gives m/2<=k, and m>=1 proves the assertion.

## References

- Truth anchor: `D5/S3/Analytic/Zeta/PositiveLaplacePoleObstruction.critical_pole_budget`
- Truth anchor: `D5/S3/Analytic/Zeta/PositiveLaplacePoleObstruction.laplace_integrable`
- Truth anchor: `D5/S3/Analytic/Zeta/PositiveLaplacePoleObstruction.no_positive_pole`
- Dependency: [D5/S3/Analytic/Laplace/NonnegativeBoundary](../Laplace/NonnegativeBoundary.md)
- Dependency: [D5/S3/Analytic/Zeta/ZetaLogDerivativeRegularity](ZetaLogDerivativeRegularity.md)
