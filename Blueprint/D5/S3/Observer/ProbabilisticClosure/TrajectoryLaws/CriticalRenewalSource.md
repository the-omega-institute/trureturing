# Critical renewal source and common scalar bounds

## Abstract

Polynomial exponential gap laws and their equilibrium forward waits.

**Theorem 1.1 (Exact gap and equilibrium laws).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/CriticalRenewalSource.source_laws`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/CriticalRenewalSource.source_laws` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix a natural r at least one, a positive real c, and s>0. The two shapes at every positive integer k are k^(2r-1) and k^(2r-1)+c k^(r-1). Their weights multiply these shapes by exp(-s k); both weights and densities are exactly zero at k=0. The normalizer is the sum over positive k. Every normalizer and positive-index density is strictly positive, both densities sum to one, and every fixed polynomial moment is finite.

The density moments define mu=1+E K and beta=(E K^2+E K)/(2 mu). The tail S(u) sums the density over k>=u. Both S(0) and S(1) equal one, the sum of all tails is mu, and the equilibrium forward-wait mass is S(u)/mu for every natural u, including zero. This mass sums to one, its first moment is finite, and its mean is beta. The definitions gapLaw and waitLaw give the corresponding probability mass functions. The theorem also proves integrability and the actual measure integrals for every gap moment and for the equilibrium wait.

For the equilibrium identities, a mass at gap k occurs once at each forward wait 0 through k. Summing these contributions gives (k+1) times its mass. Weighting each occurrence by its wait gives k(k+1)/2 times that same mass. Absolute summability follows from the polynomial geometric moments before interchanging the sums.

Writing R_m(s) for the positive-index polynomial exponential sum and g=R_(r-1)/R_(2r-1), the exact pair identity is Z_1=(1+c g)Z_0. At every k>=1 the signed density difference is c[k^(r-1)-g k^(2r-1)] exp(-s k)/Z_1. The subtracted normalizer correction remains in this identity.

**Theorem 1.2 (One neighborhood for both source labels).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/CriticalRenewalSource.common_scalar_neighborhood`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/CriticalRenewalSource.common_scalar_neighborhood` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each fixed r>=1 and c>0 there are sStar in (0,1) and positive zMinus,zPlus,G,Cmu,Cbeta such that, whenever 0<s<sStar, both normalizers lie between zMinus/s^(2r) and zPlus/s^(2r), both cycle means are at most Cmu/s, and both 1+beta values are at most Cbeta/s. On the same neighborhood g<=G s^r. These constants are chosen before s and before every later phase cap.

The polynomial geometric sum formula expresses the full natural-index sum using Stirling numbers of the second kind. Its zero-index term is removed explicitly, including when the exponent is zero. Clearing the denominator (1-exp(-s))^(m+1) leaves a finite polynomial whose value at exp(-s)=1 is m!. The derivative of 1-exp(-s) at zero is one, so s^(m+1)R_m(s) tends to m! from the positive side.

For both shapes, every scaled raw moment has the same factorial limit as its leading monomial: the added term has a factor s^r and tends to zero. The source mean, equilibrium mean and g are ratios of these scaled quantities with positive limiting denominators. The finite collection of strict bounds for both labels has a common positive neighborhood. No moment estimate is an additional source assumption.

## References

- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/CriticalRenewalSource.common_scalar_neighborhood`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/CriticalRenewalSource.source_laws`
