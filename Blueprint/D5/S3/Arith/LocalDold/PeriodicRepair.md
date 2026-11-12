# Exact zero and half-residue repairs

## Abstract

Exact zero and half-residue repairs

The periodic integer samples are actual functions of the index. The baseline and spike transforms are proved by Mobius inversion; exact divisor classification identifies the least positive Dold multiplier, while explicit finite permutations supply all positive-time fixed counts. The complete local-block-to-affine-sample valuation bridge is still required. The scalar unit-mismatch necessity follows the earlier Ma-Zhang method; the exact multipliers and signed orbit conclusions follow the supplied revised manuscript. The general scalar sufficiency/repair bound outside these residue families remains open. Registration is unfinished under issue 29392.

**Theorem 1.1 (zero_transform).**

Lean statement: `D5/S3/Arith/LocalDold/PeriodicRepair.zero_transform`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/LocalDold/PeriodicRepair.zero_transform` (`✓ std3`). ∎

*Citation.* Chatchawan Panraksa; Sawian Jaidee; Sompong Chuysurichay; Thomas Ward (2026). *Local Dold Congruences, Realizability, and Prime Densities for Linear Recurrence Sequences (supplied revised manuscript)*. URL: <https://github.com/the-omega-institute/trureturing/issues/29392>.

*Commentary.*

For R>0, any integer C and n>0, the transform of 1+C times the indicator R divides n equals the unit-index baseline plus C at index R. At R=1 both contributions are added, rather than treated as distinct indices.

**Theorem 1.2 (zero_dold_iff).**

Lean statement: `D5/S3/Arith/LocalDold/PeriodicRepair.zero_dold_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/LocalDold/PeriodicRepair.zero_dold_iff` (`✓ std3`). ∎

*Citation.* Chatchawan Panraksa; Sawian Jaidee; Sompong Chuysurichay; Thomas Ward (2026). *Local Dold Congruences, Realizability, and Prime Densities for Linear Recurrence Sequences (supplied revised manuscript)*. URL: <https://github.com/the-omega-institute/trureturing/issues/29392>.

*Commentary.*

For R>0 and natural C,c, c times the zero-residue sample is Dold exactly when R divides c*C. The statement includes C=0 and c=0; almost-Dold use requires c>0.

**Theorem 1.3 (half_transform).**

Lean statement: `D5/S3/Arith/LocalDold/PeriodicRepair.half_transform`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/LocalDold/PeriodicRepair.half_transform` (`✓ std3`). ∎

*Citation.* Chatchawan Panraksa; Sawian Jaidee; Sompong Chuysurichay; Thomas Ward (2026). *Local Dold Congruences, Realizability, and Prime Densities for Linear Recurrence Sequences (supplied revised manuscript)*. URL: <https://github.com/the-omega-institute/trureturing/issues/29392>.

*Commentary.*

For D>0, any integer C and n>0, the transform of the half sample equals the baseline at one plus C at D minus C at 2D. The half sample is first defined by the difference of its two divisibility indicators; half_residue proves its exact residue correspondence.

**Theorem 1.4 (half_negative).**

Lean statement: `D5/S3/Arith/LocalDold/PeriodicRepair.half_negative`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/LocalDold/PeriodicRepair.half_negative` (`✓ std3`). ∎

*Citation.* Chatchawan Panraksa; Sawian Jaidee; Sompong Chuysurichay; Thomas Ward (2026). *Local Dold Congruences, Realizability, and Prime Densities for Linear Recurrence Sequences (supplied revised manuscript)*. URL: <https://github.com/the-omega-institute/trureturing/issues/29392>.

*Commentary.*

For D,C,c positive, the transform of c times the half sample at 2D is strictly negative. A positive multiplier preserves the negative orbit obstruction; no positivity conclusion is inferred from Dold divisibility.

**Theorem 1.5 (zero_repair_iff).**

Lean statement: `D5/S3/Arith/LocalDold/PeriodicRepair.zero_repair_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/LocalDold/PeriodicRepair.zero_repair_iff` (`✓ std3`). ∎

*Citation.* Chatchawan Panraksa; Sawian Jaidee; Sompong Chuysurichay; Thomas Ward (2026). *Local Dold Congruences, Realizability, and Prime Densities for Linear Recurrence Sequences (supplied revised manuscript)*. URL: <https://github.com/the-omega-institute/trureturing/issues/29392>.

*Commentary.*

For R>0 and natural C,c, the zero-residue sample multiplied by c is Dold if and only if R/gcd(R,C) divides c. The divisor is positive, is itself a repair and divides every positive repair, giving the least multiplier. In the manuscript C=P-1.

**Theorem 1.6 (half_repair_iff).**

Lean statement: `D5/S3/Arith/LocalDold/PeriodicRepair.half_repair_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/LocalDold/PeriodicRepair.half_repair_iff` (`✓ std3`). ∎

*Citation.* Chatchawan Panraksa; Sawian Jaidee; Sompong Chuysurichay; Thomas Ward (2026). *Local Dold Congruences, Realizability, and Prime Densities for Linear Recurrence Sequences (supplied revised manuscript)*. URL: <https://github.com/the-omega-institute/trureturing/issues/29392>.

*Commentary.*

For D>0 and natural C,c, the half-residue sample multiplied by c is Dold if and only if 2D/gcd(2D,C) divides c. Its Dold repair remains finite despite its negative orbit quotient.

**Theorem 1.7 (zero_finite_model).**

Lean statement: `D5/S3/Arith/LocalDold/PeriodicRepair.zero_finite_model`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/LocalDold/PeriodicRepair.zero_finite_model` (`✓ std3`). ∎

*Citation.* Chatchawan Panraksa; Sawian Jaidee; Sompong Chuysurichay; Thomas Ward (2026). *Local Dold Congruences, Realizability, and Prime Densities for Linear Recurrence Sequences (supplied revised manuscript)*. URL: <https://github.com/the-omega-institute/trureturing/issues/29392>.

*Commentary.*

If R>0 and R divides M*C, there is one actual finite carrier and rotation whose fixed-point count at every positive n is M times the zero-residue sample. It has M fixed points and M*C/R cycles of length R, combining at R=1.

**Theorem 1.8 (half_finite_signed_model).**

Lean statement: `D5/S3/Arith/LocalDold/PeriodicRepair.half_finite_signed_model`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/LocalDold/PeriodicRepair.half_finite_signed_model` (`✓ std3`). ∎

*Citation.* Chatchawan Panraksa; Sawian Jaidee; Sompong Chuysurichay; Thomas Ward (2026). *Local Dold Congruences, Realizability, and Prime Densities for Linear Recurrence Sequences (supplied revised manuscript)*. URL: <https://github.com/the-omega-institute/trureturing/issues/29392>.

*Commentary.*

If D>0 and 2D divides M*C, two actual finite carriers and permutations have fixed-count difference M times the half sample at every positive n. The plus model has M fixed points and M*C/D cycles of length D; the minus model has M*C/(2D) cycles of length 2D.

**Theorem 1.9 (half_residue).**

Lean statement: `D5/S3/Arith/LocalDold/PeriodicRepair.half_residue`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/LocalDold/PeriodicRepair.half_residue` (`✓ std3`). ∎

*Citation.* Chatchawan Panraksa; Sawian Jaidee; Sompong Chuysurichay; Thomas Ward (2026). *Local Dold Congruences, Realizability, and Prime Densities for Linear Recurrence Sequences (supplied revised manuscript)*. URL: <https://github.com/the-omega-institute/trureturing/issues/29392>.

*Commentary.*

For D>0 and every integer C and natural n, the signed indicator definition of the half sample is exactly 1+C times the indicator n modulo 2D equals D.

**Theorem 1.10 (periodic_unit_invariance).**

Lean statement: `D5/S3/Arith/LocalDold/PeriodicRepair.periodic_unit_invariance`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/LocalDold/PeriodicRepair.periodic_unit_invariance` (`✓ std3`). ∎

*Citation.* Chatchawan Panraksa; Sawian Jaidee; Sompong Chuysurichay; Thomas Ward (2026). *Local Dold Congruences, Realizability, and Prime Densities for Linear Recurrence Sequences (supplied revised manuscript)*. URL: <https://github.com/the-omega-institute/trureturing/issues/29392>.

*Commentary.*

For any periodic integer sequence u of positive period R, a positive integer c satisfying all Dold congruences for c*u forces u(m*r)=u(m) for every positive m,r with r coprime to R. Dirichlet provides arbitrarily large primes in the fixed unit class; a nonzero fixed integer difference cannot be divisible by those primes. This is a scalar necessity theorem, not the withdrawn vector assertion.

**Theorem 1.11 (residue_repair_necessary).**

Lean statement: `D5/S3/Arith/LocalDold/PeriodicRepair.residue_repair_necessary`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/LocalDold/PeriodicRepair.residue_repair_necessary` (`✓ std3`). ∎

*Citation.* Chatchawan Panraksa; Sawian Jaidee; Sompong Chuysurichay; Thomas Ward (2026). *Local Dold Congruences, Realizability, and Prime Densities for Linear Recurrence Sequences (supplied revised manuscript)*. URL: <https://github.com/the-omega-institute/trureturing/issues/29392>.

*Commentary.*

For R>0, 0<=z<R and C,c positive, Dold divisibility for c times 1+C times the single residue indicator modulo R implies R divides 2z. The minus-one unit yields precisely the zero-or-half restriction. No assumption of this desired conclusion is placed in the hypotheses.

**Theorem 1.12 (residue_dold_iff).**

Lean statement: `D5/S3/Arith/LocalDold/PeriodicRepair.residue_dold_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/LocalDold/PeriodicRepair.residue_dold_iff` (`✓ std3`). ∎

*Citation.* Chatchawan Panraksa; Sawian Jaidee; Sompong Chuysurichay; Thomas Ward (2026). *Local Dold Congruences, Realizability, and Prime Densities for Linear Recurrence Sequences (supplied revised manuscript)*. URL: <https://github.com/the-omega-institute/trureturing/issues/29392>.

*Commentary.*

For R>0, z<R and C,c positive, c times the actual single-residue sample is Dold exactly when R divides 2z and R/gcd(R,C) divides c. Necessity uses unit invariance and the minus-one unit; sufficiency reduces to the proved zero or half transforms. Thus every positive multiplier is classified, including the exact least one, without assuming the desired zero-or-half conclusion.

**Theorem 1.13 (half_no_model).**

Lean statement: `D5/S3/Arith/LocalDold/PeriodicRepair.half_no_model`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/LocalDold/PeriodicRepair.half_no_model` (`✓ std3`). ∎

*Citation.* Chatchawan Panraksa; Sawian Jaidee; Sompong Chuysurichay; Thomas Ward (2026). *Local Dold Congruences, Realizability, and Prime Densities for Linear Recurrence Sequences (supplied revised manuscript)*. URL: <https://github.com/the-omega-institute/trureturing/issues/29392>.

*Commentary.*

For positive D,C,c, no map with finite positive-time fixed sets realizes c times the half-residue sample. This uses the actual fixed-cardinality Mobius nonnegativity theorem and the strictly negative transform at 2D. It applies even to a noninjective map on an uncountable space.

**Theorem 1.14 (residue_almost_realizable_iff).**

Lean statement: `D5/S3/Arith/LocalDold/PeriodicRepair.residue_almost_realizable_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/LocalDold/PeriodicRepair.residue_almost_realizable_iff` (`✓ std3`). ∎

*Citation.* Chatchawan Panraksa; Sawian Jaidee; Sompong Chuysurichay; Thomas Ward (2026). *Local Dold Congruences, Realizability, and Prime Densities for Linear Recurrence Sequences (supplied revised manuscript)*. URL: <https://github.com/the-omega-institute/trureturing/issues/29392>.

*Commentary.*

For R>0, z<R and C>0, the single-residue sample has a positive multiplier realized at every positive time by a map with finite fixed sets exactly when z=0. The zero case constructs one actual finite permutation using the least Dold repair. The negative case excludes arbitrary maps. The actual bounded-affine recurrence-to-residue valuation bridge is still open.

## References

- Truth anchor: `D5/S3/Arith/LocalDold/PeriodicRepair.half_finite_signed_model`
- Truth anchor: `D5/S3/Arith/LocalDold/PeriodicRepair.half_negative`
- Truth anchor: `D5/S3/Arith/LocalDold/PeriodicRepair.half_no_model`
- Truth anchor: `D5/S3/Arith/LocalDold/PeriodicRepair.half_repair_iff`
- Truth anchor: `D5/S3/Arith/LocalDold/PeriodicRepair.half_residue`
- Truth anchor: `D5/S3/Arith/LocalDold/PeriodicRepair.half_transform`
- Truth anchor: `D5/S3/Arith/LocalDold/PeriodicRepair.periodic_unit_invariance`
- Truth anchor: `D5/S3/Arith/LocalDold/PeriodicRepair.residue_almost_realizable_iff`
- Truth anchor: `D5/S3/Arith/LocalDold/PeriodicRepair.residue_dold_iff`
- Truth anchor: `D5/S3/Arith/LocalDold/PeriodicRepair.residue_repair_necessary`
- Truth anchor: `D5/S3/Arith/LocalDold/PeriodicRepair.zero_dold_iff`
- Truth anchor: `D5/S3/Arith/LocalDold/PeriodicRepair.zero_finite_model`
- Truth anchor: `D5/S3/Arith/LocalDold/PeriodicRepair.zero_repair_iff`
- Truth anchor: `D5/S3/Arith/LocalDold/PeriodicRepair.zero_transform`
- Dependency: [D5/S1/Dynamics/PeriodicOrbits/CountableRealization](../../../S1/Dynamics/PeriodicOrbits/CountableRealization.md)
- Dependency: [D5/S3/Arith/LocalDold/BackwardZero](BackwardZero.md)
