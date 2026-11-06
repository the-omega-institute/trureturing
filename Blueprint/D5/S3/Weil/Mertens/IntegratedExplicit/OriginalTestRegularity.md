# Regularity of the original correlation and spectral test

## Abstract

Regularity of the original correlation and spectral test

The prefix correlation is reused from D5/S3/Analytic/Interpolation/AtomicPrefixEnergy. Absolute-continuity, Lipschitz and parametric-integral suppliers are imported from the pinned Apache-2.0 Mathlib. The uniform resolvent estimates and their assembly are repository derivations.

**Theorem 1.1 (The actual finite-prefix correlation).**

Lean statement: `D5/S3/Weil/Mertens/IntegratedExplicit/OriginalTestRegularity.c_eq_hinges`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/OriginalTestRegularity.c_eq_hinges` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any finite atom type, real nodes x and complex coefficients a of total mass zero, c(t)=Re(integral_u conj(prefix(u+t))*prefix(u)) equals -sum_{i,j} Re(conj(a_i)*a_j)*max(x_i-x_j-t,0). The existing AtomicPrefixEnergy.shifted_hinge_prefix_energy supplies the actual integral identity, including empty, repeated and cancelling atoms.

**Theorem 1.2 (Absolute continuity of correlation).**

Lean statement: `D5/S3/Weil/Mertens/IntegratedExplicit/OriginalTestRegularity.c_ac`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/OriginalTestRegularity.c_ac` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each ramp max(b-t,0) is 1-Lipschitz and hence absolutely continuous. Finite linear combination proves absolute continuity of c on every finite interval, with no positivity or distinctness assumptions.

**Theorem 1.3 (The closed-window correlation endpoint).**

Lean statement: `D5/S3/Weil/Mertens/IntegratedExplicit/OriginalTestRegularity.c_at_D`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/OriginalTestRegularity.c_at_D` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If every node lies in [0,D], all ramps vanish at t=D. Thus c(D)=0, including the zero-length and empty cases.

**Theorem 1.4 (Absolute continuity of the spectral resolvent).**

Lean statement: `D5/S3/Weil/Mertens/IntegratedExplicit/OriginalTestRegularity.spectralS_ac`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/OriginalTestRegularity.spectralS_ac` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The cosine-difference estimate gives a globally Lipschitz spectralS under a finite measure and hence absolute continuity on every finite interval. OriginalActualFourier proves finiteness for the literal Fourier density; OriginalActualSpectralEndpoint combines this with c_ac to obtain the actual test f=c-S and its a.e. derivative.

## References

- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/OriginalTestRegularity.c_ac`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/OriginalTestRegularity.c_at_D`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/OriginalTestRegularity.c_eq_hinges`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/OriginalTestRegularity.spectralS_ac`
- Dependency: [D5/S3/Analytic/Interpolation/AtomicPrefixEnergy](../../../Analytic/Interpolation/AtomicPrefixEnergy.md)
