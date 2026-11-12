# Hamiltonian displacement and centered energy fluctuation

## Abstract

A self-adjoint Hamiltonian bounds the angle traversed by its actual exponential evolution.

**Theorem 1.1 (The Mandelstam–Tamm bound for every real time).**

$$(\forall E: \operatorname{Type}\left(\right), [\operatorname{NormedAddCommGroup}\left(E\right)] [\operatorname{InnerProductSpace}\left(\operatorname{Complex}\left(\right), E\right)] [\operatorname{FiniteDimensional}\left(\operatorname{Complex}\left(\right), E\right)] (\forall A: \operatorname{ContinuousLinearMap}\left(\operatorname{Complex}\left(\right), E, E\right), (\forall psi: E, (\forall hbar: \operatorname{Real}\left(\right), (\forall t: \operatorname{Real}\left(\right), (((\operatorname{IsSelfAdjoint}\left(A\right) \land (\operatorname{norm}\left(psi\right) = 1)) \land (0 < hbar)) \implies (\operatorname{fsAngle}\left(psi, \operatorname{apply}\left(\operatorname{exp}\left(\operatorname{scale}\left(\operatorname{divide}\left(\operatorname{multiply}\left(\operatorname{negative}\left(\operatorname{I}\left(\right)\right), \operatorname{ofReal}\left(t\right)\right), \operatorname{ofReal}\left(hbar\right)\right), A\right)\right), psi\right)\right) \le \operatorname{divide}\left(\operatorname{multiply}\left(\operatorname{abs}\left(t\right), \operatorname{norm}\left(\operatorname{subtract}\left(\operatorname{apply}\left(A, psi\right), \operatorname{scale}\left(\operatorname{ofReal}\left(\operatorname{Re}\left(\operatorname{inner}\left(\operatorname{Complex}\left(\right), psi, \operatorname{apply}\left(A, psi\right)\right)\right)\right), psi\right)\right)\right)\right), hbar\right))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumBounds/HamiltonianDisplacement.hamiltonian_displacement` (`✓ std3`). ∎

*Citation.* Sebastian Deffner; Steve Campbell (2017). *Quantum speed limits: from Heisenberg's uncertainty principle to optimal quantum control*. DOI: [10.1088/1751-8121/aa86c6](https://doi.org/10.1088/1751-8121/aa86c6). URL: <https://arxiv.org/abs/1705.08023v2>.

*Commentary.*

Let E be a finite-dimensional complex inner product space, A a continuous complex linear endomorphism that is self-adjoint, and psi a unit vector. The real calibration hbar is strictly positive. Define mu as the real part of inner(psi,A psi) and Delta as norm(A psi-mu psi). The theorem bounds the existing Fubini–Study angle fsAngle(psi,exp((-i t/hbar) A)psi) by abs(t) Delta/hbar for every real t. The inner product is conjugate-linear in its first argument and linear in its second. The displayed exponential is the normed-algebra exponential of the given operator.

The angle is arccos of the overlap modulus, measured in radians, with no factor of two. In physical units A, mu, and Delta are energies, t is a time, and hbar is an energy times a time. The exponential argument and abs(t) Delta/hbar are dimensionless. The mathematical statement treats these as operator, vector, and real parameters; assigning physical units does not add an empirical realization claim.

Center A at mu and put B=A-mu I and G=(-i/hbar)B. The exponential U(s)=exp(sG) is unitary. Its vector orbit v(s)=U(s)psi has derivative w(s)=U(s)(G psi), with norm(v(s))=1 and norm(w(s))=Delta/hbar. Self-adjointness makes inner(psi,A psi) real, so inner(psi,G psi)=0. Unitary invariance of the inner product gives inner(v(s),w(s))=0 at every real s.

Regard E as a real inner product space and write r(s)=Re inner(psi,v(s)). Projection onto the real tangent plane gives norm(psi-r(s)v(s)) squared = 1-r(s) squared. Cauchy–Schwarz therefore bounds abs(r'(s)) by (Delta/hbar) sqrt(1-r(s) squared). For 0<=q<1, differentiate arccos(q r(s)). Its denominator is positive, and q sqrt(1-r(s) squared)<=sqrt(1-q squared r(s) squared) bounds the absolute derivative by Delta/hbar. The mean-value inequality on the whole real line bounds arccos(q r(t)) by arccos(q)+abs(t) Delta/hbar. Continuity as q tends to one proves the bound for arccos(r(t)), including the singular endpoints of arccos.

The commuting scalar identity term gives v(t)=exp(i t mu/hbar) exp((-i t/hbar)A)psi. This scalar phase has norm one and preserves the overlap modulus. Since the real part of a complex number is at most its modulus and arccos is decreasing, the bound for the real overlap implies the stated angle bound. No overlap modulus or energy fluctuation is divided by, so zero fluctuation, zero time, negative time, and overlaps of modulus zero or one are all retained.

This supplies an actual Hamiltonian evolution satisfying the displacement premise used by record_time_lower_bound in FubiniStudyRecordTime. For a positive resource parameter energy that bounds Delta, evaluation at a nonnegative contact duration gives that premise; two endpoint preparations still require their own Hamiltonians and fluctuation bounds in the same model. The record theorem and its sequential duration budget remain separate assumptions. No bound for open-system dynamics, arbitrary measurement protocols, unbounded operators, or a universal clock tick follows.

The displacement inequality is the classical Mandelstam–Tamm result. The cited review, Section 2.5, equation (23) and equations (29)–(33), describes the pure-state overlap angle and the energy-variance speed bound. The centered fluctuation here is the norm of (A-mu I)psi. The finite-dimensional autonomous model makes this speed constant. The projection and regularization argument is a proof of that classical result, without a claim of research novelty.

## References

- Truth anchor: `D5/S3/QuantumBounds/HamiltonianDisplacement.hamiltonian_displacement`
- Dependency: [D5/S3/QuantumBounds/FubiniStudyRecordTime](FubiniStudyRecordTime.md)
