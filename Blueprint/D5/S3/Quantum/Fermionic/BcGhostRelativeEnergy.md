# Relative energy on the original bc ghost carrier

## Abstract

The existing bc ghost Virasoro zero mode is diagonal on the original finite occupation Fock space. Its integer site energy is obtained by weighting the locally finite normal ordered sum before the mode/site bijection. The literal kernel of `b 0` removes occupations containing site `3`; the shifted operator `N = L 0 + id` has nonnegative integral relative levels and a unique relative ground line. Each fixed level is supported in an explicitly finite set of occupations and therefore has a finite ket spanning set.

The carrier and all operators remain the original `CountableOccupationFock`, `BcGhostFock`, `BcGhostCharge`, and `BcGhostVirasoro` definitions. No replacement stress operator, assumed eigenbasis, PBW presentation, or BRST/no ghost conclusion is introduced.

## Formal statements

* `D5/S3/Quantum/Fermionic/BcGhostRelativeEnergy.siteEnergy` and `energy` define the integer site weights and occupation energy.
* `D5/S3/Quantum/Fermionic/BcGhostRelativeEnergy.L_zero_ket` and `L_zero_coefficient` prove diagonal action of the actual `BcGhostVirasoro.L 0`.
* `b_zero_kernel_iff` characterizes the literal kernel of `BcGhostFock.b 0 = annihilate 3` coefficientwise.
* `relativeEnergy_split`, `relativeEnergy_nonneg`, and `level_cast` derive the shifted nonnegative integral grading.
* `relative_level_coeff_iff` gives the exact coefficient characterization at every natural level, and `relative_ground_line` proves the unique level-zero line.
* `relative_level_support`, `levelOccupationSets`, and `relative_level_expansion` give the finite occupation support and explicit finite ket expansion. `relative_level_finite_dimensional` transfers the finite span to the actual relative level submodule.

All claims are on the original algebraic carrier. Signed negative-mode PBW actions, total BRST nilpotence, no-ghost, string, and AdS/CFT statements remain separate later consumers.

## References

- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostRelativeEnergy.L_zero_ket`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostRelativeEnergy.L_zero_coefficient`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostRelativeEnergy.b_zero_kernel_iff`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostRelativeEnergy.relative_level_coeff_iff`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostRelativeEnergy.relative_ground_line`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostRelativeEnergy.relative_level_finite_dimensional`
- Dependency: [D5/S3/Quantum/Fermionic/BcGhostVirasoro](BcGhostVirasoro.md)
- Dependency: [D5/S3/Quantum/Fermionic/BcGhostCharge](BcGhostCharge.md)
