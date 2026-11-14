# Crossings from endpoint limits

## Abstract

Strict crossings of continuous families from endpoint limits and dense logarithmic differences.

**Theorem 1.1 (Arbitrarily late crossings inside an open interval).**

Lean statement: `D5/S3/Arith/Robin/Analytic/LcmPowerCollisionCrossing.collision_of_scaled_limits`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/LcmPowerCollisionCrossing.collision_of_scaled_limits` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The families f and g take a real parameter and a natural index. At the two endpoints alpha<beta, multiplying f by P^n and g by Q^n gives four positive limits. The bases P and Q are positive. The logarithm of the ratio of the f-limit to the g-limit is strictly smaller at alpha than at beta. Every open interval contains a difference i*log(P)-j*log(Q) with both natural indices beyond any prescribed bound. For every pair of positive indices, the difference f(kappa,i)-g(kappa,j) is continuous on [alpha,beta].

For every natural M there are indices i,j at least M and at least one, and a parameter strictly between alpha and beta, at which f(kappa,i) equals g(kappa,j). Only the two endpoint limits are needed; no estimate uniform in kappa is assumed.

Let A and B denote the endpoint logarithmic ratios and put epsilon=(B-A)/12. The four scaled logarithms are within epsilon of their limits for all sufficiently large indices. Choose i*log(P)-j*log(Q) in (A+3*epsilon,B-3*epsilon). The original values then satisfy f(alpha,i)<g(alpha,j) and g(beta,j)<f(beta,i). The strict intermediate value theorem places the equality in the open parameter interval.

## References

- Truth anchor: `D5/S3/Arith/Robin/Analytic/LcmPowerCollisionCrossing.collision_of_scaled_limits`
