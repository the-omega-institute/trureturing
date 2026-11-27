# Critical zeta collisions under a Cauchy energy cap

## Abstract

A Cauchy energy cap ensures the Gaussian zeta collision limit at critical resolution.

**Theorem 1.1 (Harmonic collision limit on the critical scale).**

Lean statement: `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHCriticalCauchyThreshold.harmonic_zeta_critical_collision_limit_of_cauchy_cap`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHCriticalCauchyThreshold.harmonic_zeta_critical_collision_limit_of_cauchy_cap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume RH. Write c = 1/(2 pi) and G_Y(t) for the unnormalized Montgomery sum on the inclusive positive-ordinate cutoff with analytic multiplicities. For one fixed kappa < 2 pi c^2, assume G_Y(t) <= kappa Y log(Y)^2 on every fixed band log(Y) <= |t| <= A log(Y), uniformly in t for sufficiently large Y depending on A > 1.

Take T_n tending to infinity with log(T_n)^2/n tending to zero. Let s_n be sqrt(n P_2(T_n)/2) for the second normalized harmonic pair moment P_2. For eta_n/s_n tending to zero and eta_n log(T_n) eventually bounded below by a positive constant, the inclusive hard collision mass multiplied by s_n and divided by eta_n times the total harmonic mass to power 2n tends to 1/sqrt(pi).

The Cauchy-smoothed phase sum gives a fixed fractional deficit in the multiplicity-weighted cutoff before harmonic reweighting. The harmonic transfer gives the required logarithmic-band deficit for the collision theorem. The upper bound on the actual zeta pair sum is an arithmetic hypothesis.

## References

- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHCriticalCauchyThreshold.harmonic_zeta_critical_collision_limit_of_cauchy_cap`
- Dependency: [D5/S3/Analytic/Oscillation/MontgomeryCauchyDeficit](../../../../../Analytic/Oscillation/MontgomeryCauchyDeficit.md)
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHCriticalPairSumThreshold](RHCriticalPairSumThreshold.md)
