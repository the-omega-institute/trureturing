# The actual finite-atom Fourier density is finite

## Abstract

The actual finite-atom Fourier density is finite

**Theorem 1.1 (The original prefix and its zero extension).**

Lean statement: `D5/S3/Weil/Mertens/IntegratedExplicit/OriginalActualFourier.prefix_eq_zero_extension`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/OriginalActualFourier.prefix_eq_zero_extension` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite atom type, complex coefficients with zero total mass, and nodes in the closed window [0,D], the original prefix equals its closed-window zero extension pointwise. The finite closed-step expansion retains the endpoint nodes; the common tail cancels by zero mass.

**Theorem 1.2 (Integrable prefix and square energy).**

Lean statement: `D5/S3/Weil/Mertens/IntegratedExplicit/OriginalActualFourier.prefix_L1_L2`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/OriginalActualFourier.prefix_L1_L2` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The original prefix is Lebesgue integrable and its squared norm is integrable. L1 follows from the finite closed-step expansion. L2 reuses AtomicPrefixEnergy.shifted_hinge_prefix_energy. Empty atom types, repeated nodes and cancelling coefficients remain allowed.

**Theorem 1.3 (Every frequency, including zero).**

Lean statement: `D5/S3/Weil/Mertens/IntegratedExplicit/OriginalActualFourier.frequency_mul_Ahat`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/OriginalActualFourier.frequency_mul_Ahat` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Ahat(A,w) is literally the Lebesgue integral of A(u)*exp(-I*w*u). For the original prefix, (I*w)*Ahat(A,w)=sum_i a_i*exp(-I*w*x_i) at every real w. The nonzero-frequency proof integrates each finite closed step; zero mass proves the frequency-zero case.

**Theorem 1.4 (An integrable square envelope).**

Lean statement: `D5/S3/Weil/Mertens/IntegratedExplicit/OriginalActualFourier.normSq_Ahat_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/OriginalActualFourier.normSq_Ahat_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Put C0=integral norm(A) and M=sum_i norm(a_i). The triangle inequality gives norm(Ahat)<=C0, while the finite Fourier identity gives abs(w)*norm(Ahat)<=M. Adding their squared bounds yields norm(Ahat)^2<=(C0^2+M^2)/(1+w^2) for every real frequency.

**Theorem 1.5 (Finiteness of the literal spectral measure).**

Lean statement: `D5/S3/Weil/Mertens/IntegratedExplicit/OriginalActualFourier.actual_rho_finite`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/OriginalActualFourier.actual_rho_finite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The density is literally norm(Ahat(A,w))^2/(2*pi), and rho is volume.withDensity(ofReal(density)). Continuity of the L1 Fourier integral gives measurable density. The square envelope is integrable, so the withDensity measure is finite without a finite-measure premise.

## References

- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/OriginalActualFourier.actual_rho_finite`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/OriginalActualFourier.frequency_mul_Ahat`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/OriginalActualFourier.normSq_Ahat_bound`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/OriginalActualFourier.prefix_L1_L2`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/OriginalActualFourier.prefix_eq_zero_extension`
- Dependency: [D5/S3/Analytic/Interpolation/AtomicPrefixEnergy](../../../Analytic/Interpolation/AtomicPrefixEnergy.md)
