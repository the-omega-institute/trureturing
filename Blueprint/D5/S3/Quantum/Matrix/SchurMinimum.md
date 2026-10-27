# Attained Schur Minimum

## Abstract

The Schur quadratic form is the attained minimum over the internal block.

**Theorem 1.1 (Boundary quadratic minimum).**

$$\operatorname{IsLeast}(\{\begin{pmatrix}x\\y\end{pmatrix}^{*}\begin{pmatrix}A&B\\B^{*}&C\end{pmatrix}\begin{pmatrix}x\\y\end{pmatrix} \mid y \in \mathbb{C}^{n}\}, x^{*}(A-BC^{-1}B^{*})x)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/SchurMinimum.schur_quadratic_is_least` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a finite Hermitian block matrix with positive definite internal block C, the set of energies at a fixed boundary vector has the stated least element. It is attained at the negative inverse-block response. The proof applies Mathlib's Schur decomposition and positive-semidefinite quadratic inequality. This is a repository API wrapper of those upstream results.

Real quadratic energy and Gaussian free energy.

Let x and z range over real Euclidean spaces of positive finite dimensions p and r, with their standard Lebesgue volumes. Suppose the symmetric block matrix L = [A B; Bᵀ C] is positive definite, and set U(x,z) = xᵀAx/2 + xᵀBz + zᵀCz/2 and S = A − BC⁻¹Bᵀ. The principal block C is positive definite. Testing the full quadratic form on (x, −C⁻¹Bᵀx) also gives strict positive definiteness of S.

The real specialization of Matrix.schur_complement_eq₂₂ gives U(x,z) = xᵀSx/2 + vᵀCv/2, where v = z + C⁻¹Bᵀx. Consequently, over all real hidden vectors z the minimum is attained uniquely at z = −C⁻¹Bᵀx, and its value is xᵀSx/2. This includes x = 0, arbitrary rectangular B, and noncommuting square blocks.

For every real temperature τ > 0 the actual Lebesgue integrand exp(−U(x,z)/τ) is integrable, and its integral over the entire hidden space is exp(−xᵀSx/(2τ)) (2πτ)^(r/2) (det C)^(−1/2). Both exponents are real numbers. To obtain the normalization, use the positive matrix square root D of the same C: the standard Euclidean squared norm of Dv is vᵀCv and det D = sqrt(det C) > 0. Measure.map_linearMap_addHaar_eq_smul_addHaar supplies the actual volume factor 1/sqrt(det C), and GaussianFourier.integral_rexp_neg_mul_sq_norm supplies the radial Gaussian integral. Translation invariance removes the hidden shift.

Taking the real logarithm of this positive integral gives exactly −τ log ∫ exp(−U(x,z)/τ) dz = xᵀSx/2 + (τ/2) log det C − (rτ/2) log(2πτ). Thus the minimum of the actual energy and the free energy of the actual integral are both differentiable in x, with Euclidean gradient Sx; their derivative sends h to the Euclidean inner product of Sx and h. This follows from the derivative of the inner product, symmetry of S, and the displayed equality of functions.

Here C is fixed independently of x. If the hidden stiffness varies with x, the logarithmic determinant correction generally has a nonzero derivative. Positive definiteness and τ > 0 are required for this full-space normalization; a singular hidden block or a replacement measure does not have the stated meaning.

Projected gradient flow and memory.

For the same real blocks and Euclidean energy, write y₀ = (x₀,z₀). The full gradient trajectory is y(t) = exp(−tL)y₀ for every real t. Its observed and hidden coordinates satisfy x(0) = x₀, z(0) = z₀, x′ = −Ax − Bz and z′ = −Bᵀx − Cz. Symmetry of L identifies Ly with the Euclidean gradient of U. Mathlib's hasDerivAt_exp_smul_const′ and HasDerivAt.clm_apply give the actual trajectory derivative; ODE_solution_unique_univ gives uniqueness because the linear vector field is Lipschitz. The full state space is the Euclidean direct sum, and operators use its induced norm.

For a fixed real endpoint t, differentiate exp((s−t)C)z(s). The two terms containing C cancel, leaving −exp((s−t)C)Bᵀx(s). The oriented interval fundamental theorem of calculus gives z(t) = exp(−tC)z₀ − ∫₀ᵗ exp(−(t−s)C)Bᵀx(s) ds. Substitution in the observed differential equation yields x′(t) = −Ax(t) − B exp(−tC)z₀ + ∫₀ᵗ B exp(−(t−s)C)Bᵀx(s) ds. The suppliers are hasDerivAt_exp_smul_const, HasDerivAt.clm_apply, intervalIntegral.integral_eq_sub_of_hasDerivAt and ContinuousLinearMap.intervalIntegral_comp_comm. Continuity supplies integrability on each oriented interval. These identities include t = 0, negative time, zero initial data and B = 0, with no rank condition on rectangular B.

There exists one function F from the observed Euclidean space to itself such that x′(t) = F(x(t)) for every full initial state and every real time if and only if B = 0. No linearity or regularity of F is assumed. At time zero, the initial states (x,z) and (x,0) must both have derivative F(x), so their difference gives Bz = 0 for every hidden vector z. Conversely, B = 0 gives the common field F(x) = −Ax. This identifies the zero hidden-to-visible block in the existing VisibleAutonomyCriterion.visible_autonomy_criterion and LinearDescentCriterion.linear_descent_criterion with the arbitrary-field assertion for these actual trajectories; the time-zero argument supplies that correspondence.

A positive energy already gives a counterexample to exact Schur-gradient dynamics. Take A = C = 2, B = 1, x₀ = 1 and z₀ = −1/2. Then U(x,z) = x² + xz + z² = 3x²/4 + (z + x/2)², so z = −x/2 is the unique conditional minimizer and S = 3/2. The full matrix [2 1; 1 2] is positive definite and has characteristic polynomial (λ−1)(λ−3), giving eigenvalues 1 and 3. The actual coupled solution is x(t) = exp(−3t)/4 + 3 exp(−t)/4, z(t) = exp(−3t)/4 − 3 exp(−t)/4. The Schur-gradient solution with the same observed initial value is x̄(t) = exp(−3t/2). Direct differentiation verifies both differential equations and all three initial values. It gives x′(0) = x̄′(0) = −3/2, while x″(0) = 3 and x̄″(0) = 9/4. Hence the trajectories cannot agree on any initial neighborhood, even though the hidden initial value minimizes U.

The discrepancy is strict at every nonzero real time: with a = exp(−t/2), x(t) − x̄(t) = a²(a−1)²(a²+2a+3)/4 > 0. Here a > 0 and a ≠ 1 whenever t ≠ 0. This also rules out equality on any nontrivial forward interval. The memory identity is the classical linear elimination formula: Gouasmi, Parish and Duraisamy, A priori estimation of memory effects in coarse-grained nonlinear systems using the Mori-Zwanzig formalism (arXiv:1611.06277v2, §2.1, equations (2.1)–(2.3)), with (A¹¹,A¹²,A²¹,A²²) = (−A,−B,−Bᵀ,−C). Exact energy minimization therefore does not imply exact projected trajectory closure.

## References

- Truth anchor: `D5/S3/Quantum/Matrix/SchurMinimum.schur_quadratic_is_least`
