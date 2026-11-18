# Actual finite Markov paths and classical Fisher information

## Abstract

Actual finite Markov paths and classical Fisher information

**Theorem 1.1 (Exact corrected finite-path moment).**

Lean statement: `D5/S3/Combinatorics/Graph/Pressure/MarkovAdditivePaths.corrected_second_moment`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Pressure/MarkovAdditivePaths.corrected_second_moment` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A path consists of an initial state i and n future states w:Fin n to V. Its probability is pi_i times the product of its n actual transition weights. A finite PMF is constructed from this product and its normalization. For every row-centered edge increment a, recursion proves its path sum has mean zero for each fixed initial state, and its stationary second moment is n times sum_ij pi_i P_ij a_ij squared. The corrected increment xi from the Poisson inverse is row-centered, so its sum M_n satisfies E M_n squared=n v, including n=0.

**Theorem 1.2 (Exact endpoint correction).**

Lean statement: `D5/S3/Combinatorics/Graph/Pressure/MarkovAdditivePaths.additive_decomposition`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Pressure/MarkovAdditivePaths.additive_decomposition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On every actual path, S_n-n m=M_n+h(X_0)-h(X_n). The identity uses n transitions. It retains both endpoints and does not identify arrival counts with departure counts on finite paths.

**Theorem 1.3 (Periodic-safe second-Poisson identity).**

Lean statement: `D5/S3/Combinatorics/Graph/Pressure/MarkovAdditivePaths.second_poisson_endpoint_covariance`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Pressure/MarkovAdditivePaths.second_poisson_endpoint_covariance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let u be the second centered corrector satisfying u-Pu=h. Finite path recursion proves E_pi[M_n h(X_n)]=sum_ij pi_i P_ij xi_ij (u-P^n u)_j. The conditional future contribution after transition k uses n-1-k transitions. The finite telescoping identity uses no spectral gap, mixing assumption, summability, or division by v. Applying weighted Cauchy-Schwarz bounds this covariance by U sqrt(v), where U is the oscillation of u. The endpoint square is bounded by D squared, where D is the oscillation of h. Expansion therefore gives the uniform finite-path variance error D squared plus 2 U sqrt(v), without dividing by v.

**Theorem 1.4 (Uniform finite-path variance error).**

Lean statement: `D5/S3/Combinatorics/Graph/Pressure/MarkovAdditivePaths.variance_uniform_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Pressure/MarkovAdditivePaths.variance_uniform_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite nonempty state type V with decidable equality, irreducible row-stochastic real matrix P, positive normalized stationary row pi, arbitrary real reward g and natural transition length n, the actual stationary path variance satisfies absolute value of Var(S_n)-n v at most D squared plus 2 U sqrt(v). Here D=max h-min h and U=max u-min u for the two constructed centered Poisson solutions, and v=sum pi_i P_ij xi_ij squared. The proof uses the exact finite second-Poisson endpoint covariance, weighted Cauchy-Schwarz, zero conditional mean of M_n, and the endpoint square bound. No aperiodicity or division by v is used. Normalizing by n gives the stated O(1/n) error for n at least one and convergence to v.

**Theorem 1.5 (Actual Doob finite-path Fisher).**

Lean statement: `D5/S3/Combinatorics/Graph/Pressure/MarkovAdditivePaths.pathFisher_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Pressure/MarkovAdditivePaths.pathFisher_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The locally constructed Doob transition is Q_t(i,j)=T_t(i,j)r_t(j)/(lambda(t)r_t(i)); it is stochastic and preserves exactly the original positive support near zero. Its supported transition log derivative is xi. The initial pi is fixed independently of t. Differentiating the product path mass gives the supported path log derivative M_n. The actual finite PMF weights then give classical Fisher I_n(0)=E_pi[M_n squared]=n v. Unsupported paths have zero mass. This is complete-path classical Fisher information; it makes no quantum Fisher claim and no assertion for a varying stationary initial law, raw tilted Gibbs endpoints, or fixed-exterior block conditioning.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Pressure/MarkovAdditivePaths.additive_decomposition`
- Truth anchor: `D5/S3/Combinatorics/Graph/Pressure/MarkovAdditivePaths.corrected_second_moment`
- Truth anchor: `D5/S3/Combinatorics/Graph/Pressure/MarkovAdditivePaths.pathFisher_eq`
- Truth anchor: `D5/S3/Combinatorics/Graph/Pressure/MarkovAdditivePaths.second_poisson_endpoint_covariance`
- Truth anchor: `D5/S3/Combinatorics/Graph/Pressure/MarkovAdditivePaths.variance_uniform_bound`
- Dependency: [D5/S3/Combinatorics/Graph/Pressure/MarkovAdditiveCurvature](MarkovAdditiveCurvature.md)
