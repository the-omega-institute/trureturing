# Collision parameters in every open interval

## Abstract

Real collision parameters of the LCM power thresholds are dense above one.

**Theorem 1.1 (Density with arbitrarily large exponents).**

Lean statement: `D5/S3/Arith/Robin/Analytic/LcmPowerCollisionDensity.collision_parameters_dense`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/LcmPowerCollisionDensity.collision_parameters_dense` (`✓ std3`). ∎

*Resolves.* `Problems/fan-kobayashi-molnar-2026-collision-density` (proved) by `D5/S3/Arith/Robin/Analytic/LcmPowerCollisionDensity.collision_parameters_dense`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"fan-kobayashi-molnar-2026-collision-density","declaration_gid":"D5/S3/Arith/Robin/Analytic/LcmPowerCollisionDensity.collision_parameters_dense","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Steve Fan, Mits Kobayashi, Grant Molnar (2025). *A family of analogues to the Robin criterion*. DOI: [10.1007/s11139-026-01408-3](https://doi.org/10.1007/s11139-026-01408-3). URL: <https://arxiv.org/abs/2511.02106v1>.

*Commentary.*

For distinct natural primes p and q, real endpoints 1<alpha<beta, and every natural M, there are a real kappa strictly between alpha and beta and natural i,j both at least M and at least one such that lcmPowerF(kappa,p,i)=lcmPowerF(kappa,q,j). The function is exactly the existing function of Fan, Kobayashi and Molnar, Definition 4.2.

Order the two primes. The logarithmic ratio of their positive leading coefficients strictly increases in kappa. The logarithms of distinct primes have irrational ratio, and their differences with two natural indices remain dense after any prescribed index cutoff. Choose such a difference strictly inside the two endpoint coefficient ratios. The fixed-parameter scaled limits force opposite strict signs at alpha and beta for sufficiently large indices. Continuity in kappa and the strict intermediate value theorem give the equality.

This answers the real-parameter existence question in Section 8 and also yields collisions at arbitrarily large parameters. Countability and the integer-parameter conclusions are separate statements.

## References

- Truth anchor: `D5/S3/Arith/Robin/Analytic/LcmPowerCollisionDensity.collision_parameters_dense`
- Dependency: [D5/S3/Arith/Robin/Analytic/LcmPowerCollisionCrossing](LcmPowerCollisionCrossing.md)
- Dependency: [D5/S3/Arith/Robin/Analytic/LcmPowerLeadingTerm](LcmPowerLeadingTerm.md)
- Dependency: [D5/S3/Arith/Robin/Analytic/LcmPowerLogLattice](LcmPowerLogLattice.md)
