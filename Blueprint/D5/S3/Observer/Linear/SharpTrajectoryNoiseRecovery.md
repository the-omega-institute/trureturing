# Exact deterministic recovery from Hilbert trajectories

## Abstract

Exact deterministic recovery from Hilbert trajectories

Throughout, K is the real or complex field, E is a nonzero complete Hilbert space over K, and F is a complete Hilbert space over K. All observation operators are bounded and linear. No dimension, separability, compactness or surjectivity assumption is imposed.

For A:E→F define m(A)=inf{‖Ax‖²:‖x‖=1}. For an arbitrary total function Q:F→E and a real budget δ≥0, define e(A,δ,Q)=sup{ofReal(‖Q(Ax+η)−x‖):x∈E, η∈F, ‖η‖≤δ}. The supremum and infimum of risks are in ENNReal; a reconstruction may have infinite worst-case risk. The lower modulus is a genuine real infimum and need not be attained.

**Theorem 1.1 (A total least-squares inverse attains the sharp minimax risk).**

$$\forall K, E, F Hilbert\left(K, E, F\right), E\neq0, \forall A:BoundedLinear\left(E, F\right), 0<m\left(A\right)\Rightarrow\\{}\exists R:BoundedLinear\left(F, E\right), (\forall x, R\left(A\left(x\right)\right)=x) \land (\forall y, x, \langle A\left(x\right),y-A\left(R\left(y\right)\right)\rangle=0) \land (\forall y, \Vert R\left(y\right)\Vert\le\frac{\Vert y\Vert}{\sqrt{m\left(A\right)}}) \land\\{}\forall \delta\in\mathbb{R}, 0\le\delta\Rightarrow e\left(A, \delta, R\right)=ofReal\left(\frac{\delta}{\sqrt{m\left(A\right)}}\right) \land inf_{Q:F\to E}e\left(A, \delta, Q\right)=ofReal\left(\frac{\delta}{\sqrt{m\left(A\right)}}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/SharpTrajectoryNoiseRecovery.sharp_hilbert_noise_recovery` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every bounded A with m(A)>0 there is one bounded linear R:F→E satisfying all the displayed properties simultaneously for every finite real δ≥0. The infimum ranges over every total reconstruction function, including nonlinear and discontinuous functions. In particular the exact risk at δ=0 is zero.

The positive modulus makes A injective with closed range. Let P be the orthogonal projection onto that range and let R=(A restricted to its range)⁻¹ P. Thus R is defined on all of F. Its residual y−ARy is orthogonal to every Ax, so it is the Moore–Penrose least-squares left inverse. Projection contraction and the lower modulus give the stated norm estimate and risk upper bound.

For the lower bound, opposite states z and −z with noises −Az and Az produce the same zero datum whenever ‖Az‖≤δ. The triangle inequality forces at least one error to be at least ‖z‖. Scaling every unit direction and taking the defining infimum yields δ/sqrt(m(A)); no minimizing direction or continuity of the reconstruction is used. Infinite risk is handled directly in ENNReal.

For bounded B:E→E and C:E→F and T>0, put H_T=L²(F,volume restricted to (0,T]), with the ordinary unnormalized Lebesgue measure. Define E_T(x)=∫₀ᵀ‖C exp(tB)x‖²dt and a(T)=inf{E_T(x):‖x‖=1}. Equality of representatives below is almost everywhere for this restricted measure.

**Theorem 1.2 (The actual Lebesgue L² trajectory has the exact noise constant).**

$$\forall K, E, F Hilbert\left(K, E, F\right), E\neq0, \forall B:BoundedLinear\left(E, E\right), C:BoundedLinear\left(E, F\right), T\in\mathbb{R}, 0<T \land 0<a\left(T\right)\Rightarrow\\{}\exists A:BoundedLinear\left(E, H_{T}\right), \exists R:BoundedLinear\left(H_{T}, E\right),\\{}(\forall x, A\left(x\right)=_{ae}(s\mapsto C\left(exp\left(sB\right)\left(x\right)\right))) \land (\forall x, \Vert A\left(x\right)\Vert^{2}=E_{T}\left(x\right)) \land m\left(A\right)=a\left(T\right) \land\\{}(\forall x, R\left(A\left(x\right)\right)=x) \land (\forall y, x, \langle A\left(x\right),y-A\left(R\left(y\right)\right)\rangle=0) \land (\forall y, \Vert R\left(y\right)\Vert\le\frac{\Vert y\Vert}{\sqrt{a\left(T\right)}}) \land\\{}\forall \delta\in\mathbb{R}, 0\le\delta\Rightarrow e\left(A, \delta, R\right)=ofReal\left(\frac{\delta}{\sqrt{a\left(T\right)}}\right) \land inf_{Q:H_{T}\to E}e\left(A, \delta, Q\right)=ofReal\left(\frac{\delta}{\sqrt{a\left(T\right)}}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/SharpTrajectoryNoiseRecovery.sharp_trajectory_noise_recovery` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume a(T)>0. The theorem constructs the actual bounded trajectory operator A:E→H_T, proves its almost-everywhere representative and the exact identity ‖Ax‖²=E_T(x), and identifies m(A)=a(T). It then constructs a total bounded linear R:H_T→E with left-inverse, normal-equation and norm-bound properties. The same R attains both exact risk identities for every finite real δ≥0.

Continuity of the operator-valued exponential on the compact window provides a uniform operator-norm bound, which constructs the L² operator. The Hilbert L² inner-product formula gives the unnormalized integral identity. The general sharp recovery theorem then applies with the exact trajectory floor. A positive certified lower bound 0<α≤a(T) gives an upper estimate δ/sqrt(α), but does not replace a(T) in the sharp equality.

These are classical Hilbert-space consequences assembled with the trajectory and unrestricted risk models. The theorem makes no claim for a(T)=0 or T=0. Window equivalence, matching short-window powers and moment clauses are separate statements.

## References

- Truth anchor: `D5/S3/Observer/Linear/SharpTrajectoryNoiseRecovery.sharp_hilbert_noise_recovery`
- Truth anchor: `D5/S3/Observer/Linear/SharpTrajectoryNoiseRecovery.sharp_trajectory_noise_recovery`
- Dependency: [D5/S3/Observer/Linear/PositiveWindowObservationBound](PositiveWindowObservationBound.md)
- Dependency: [D5/S3/Observer/MeasureSeparation/RobustMinimaxKernelBound](../MeasureSeparation/RobustMinimaxKernelBound.md)
