# Actual Odd Covers Force Physical Charge

## Abstract

Every ordinary finite distinct odd covering system induces an actual unrestricted distortion chain whose charge is at least one and whose base caps are determined by exact residual-prefix probabilities.

**Theorem 1.1 (Ordinary coverage survives the arithmetic and probability interfaces).**

Lean statement: `D5/S3/Arith/Congruence/ActualCylinderChain.ordinary_cover_forces_charge_and_caps`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Congruence/ActualCylinderChain.ordinary_cover_forces_charge_and_caps` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The input is an ordinary finite covering system: natural-number residues, distinct odd moduli greater than one, and coverage of every natural number. The finite prime support, all prime-power heights and the actual prefix cylinders come from the licensed arithmetic interface. No bound is placed on the number of prime factors of a modulus. Each coordinate has an arbitrary rational distortion threshold between zero inclusive and one exclusive.

At each prime and positive depth, the unique supplied pure class determines its forbidden prefix, with a default prefix where that class is absent. The exact residual-law theorem gives a normalized rational law on all full words, assigning zero weight to every forbidden-prefix hit. The base law is the product of these single-coordinate laws. Each mixed cylinder is assigned to its last positive-depth coordinate, retaining its entire original label and all previous requirements.

The new support induction works under the one final history-dependent probability law. Distortion cannot put mass on an event of zero base mass, and normalized future kernels preserve the previous support conditions. Hence all processed diagonal coordinates avoid their pure forbidden prefixes with probability one. Actual coverage then supplies a mixed cylinder and forces the physical covered event. The imported covered-event bound proves that the accumulated charge is at least one.

The same theorem supplies BaseCaps whenever each explicit residual-cylinder probability is at most one minus the coordinate threshold, multiplied by the requested comparison survival probability. These expressions retain the actual forbidden ancestor and descendant geometry. The existing kernels_have_caps theorem can then be applied directly. A numerical or symbolic total-charge bound below one remains necessary to conclude noncoverage; this interface alone does not settle the unrestricted odd covering problem.

## References

- Truth anchor: `D5/S3/Arith/Congruence/ActualCylinderChain.ordinary_cover_forces_charge_and_caps`
- Dependency: [D5/S3/Arith/Congruence/PurePrefixResidualLaw](PurePrefixResidualLaw.md)
