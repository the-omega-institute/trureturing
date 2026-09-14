# Energy eigenstates have no changing density record

## Abstract

An energy eigenvector acquires only an overall phase under time evolution. Its density matrix is constant and its energy variance is zero.

**Theorem 1.1 (Exponential action on an eigenvector).**

$$Av = muv \Rightarrow \operatorname{exp}\left(A\right)v = \operatorname{exp}\left(mu\right)v$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/EnergyEigenstateStationarity.exp_mulVec_of_eigenvector` (`✓ std3`). ∎

*Citation.* Nicholas J. Higham (2006). *Functions of Matrices*. URL: <https://eprints.maths.manchester.ac.uk/310/>.

*Commentary.*

Let A be any complex matrix on a finite index type. If Av = mu v, then each power acts by the corresponding power of mu. Continuous linear evaluation on v carries the convergent matrix exponential series to the scalar exponential series. The vector may be zero; neither Hermiticity nor diagonalizability is required.

**Definition 1.2 (The normalized pure density state).**

$$rho = vv^{*}$$

*Formalization.* `D5/S3/Quantum/Dynamics/EnergyEigenstateStationarity.pureDensityState` (`✓ std3`).

*Citation.* Nicholas J. Higham (2006). *Functions of Matrices*. URL: <https://eprints.maths.manchester.ac.uk/310/>.

*Commentary.*

For v with conjugate inner product equal to one, its rank-one outer product is positive semidefinite and has trace one. This is the density state used in both the time evolution and the variance.

**Theorem 1.3 (All real times preserve the density matrix).**

$$U^{*}U = 1 \land UU^{*} = 1 \land UrhoU^{*} = rho$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/EnergyEigenstateStationarity.energy_eigenstate_stationary` (`✓ std3`). ∎

*Citation.* Wikipedia contributors (2026). *Stationary state*. URL: <https://en.wikipedia.org/wiki/Stationary_state>.

*Commentary.*

Assume H is Hermitian, v is normalized, and Hv = Ev with E real. Use units in which hbar equals one and put U = exp(-itH), for any real t. This matrix is unitary. The exponential action theorem gives Uv = exp(-itE)v; multiplying the phase by its conjugate gives one, so U rho U* = rho. Arbitrarily rapid overall phase rotation therefore supplies no changing density record of this isolated state.

**Theorem 1.4 (Zero energy variance).**

$$\operatorname{Var}\left(rho, H\right) = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/EnergyEigenstateStationarity.energy_eigenstate_variance_zero` (`✓ std3`). ∎

*Citation.* Nicholas J. Higham (2006). *Functions of Matrices*. URL: <https://eprints.maths.manchester.ac.uk/310/>.

*Commentary.*

For the same normalized vector satisfying Hv = Ev, the density-state expectations of H and H squared are E and E squared. Thus the variance, defined as the second moment minus the squared mean, vanishes. The scalar time parameter can absorb any nonzero choice of hbar. These statements concern a single energy eigenstate; relative phases between distinct energies are not asserted to be constant.

## References

- Truth anchor: `D5/S3/Quantum/Dynamics/EnergyEigenstateStationarity.energy_eigenstate_stationary`
- Truth anchor: `D5/S3/Quantum/Dynamics/EnergyEigenstateStationarity.energy_eigenstate_variance_zero`
- Truth anchor: `D5/S3/Quantum/Dynamics/EnergyEigenstateStationarity.exp_mulVec_of_eigenvector`
- Truth anchor: `D5/S3/Quantum/Dynamics/EnergyEigenstateStationarity.pureDensityState`
- Dependency: [D5/S3/Quantum/Information/CovarianceSumBound](../Information/CovarianceSumBound.md)
- Dependency: [D5/S3/Quantum/PureState/PureStateHandshake](../PureState/PureStateHandshake.md)
