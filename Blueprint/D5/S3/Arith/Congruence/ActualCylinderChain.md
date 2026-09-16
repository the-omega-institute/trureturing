# Actual Odd Covers Force Average Charge after a Correlated Head

## Abstract

Every ordinary finite distinct odd covering system and any full correlated head law supported on head-safe points induce tail distortion chains whose average charge is at least one and whose base caps are determined by exact residual-prefix probabilities.

**Theorem 1.1 (Ordinary coverage survives the arithmetic and probability interfaces).**

Lean statement: `D5/S3/Arith/Congruence/ActualCylinderChain.ordinary_cover_forces_charge_and_caps`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Congruence/ActualCylinderChain.ordinary_cover_forces_charge_and_caps` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The input is an ordinary finite covering system: natural-number residues, distinct odd moduli greater than one, and coverage of every natural number. The finite prime support, all prime-power heights and the actual prefix cylinders come from the licensed arithmetic interface. No bound is placed on the number of prime factors of a modulus. A cut b selects the first b prime coordinates. The head law mu is any rational finite law on their complete prime-power words, with arbitrary correlations. Its headSafe event must have probability one: every original cylinder supported entirely in the head, including mixed cylinders, must fail its headMatch condition.

At each prime and positive depth, the unique supplied pure class determines its forbidden prefix, with a default prefix where that class is absent. The exact residual-law theorem gives a normalized rational law on all full words, assigning zero weight to every forbidden-prefix hit. The base law is the product of these single-coordinate laws. For each fixed head, tail stage i processes coordinate b+i with an arbitrary rational threshold between zero inclusive and one exclusive. A mixed cylinder matching that head is assigned to its last positive-depth tail coordinate. The chain retains the original labels, headMatch and the entire previous tail history; distinct original moduli need not have distinct tail cofactors.

The support induction works under each head's final history-dependent tail law. Distortion cannot put mass on an event of zero base mass, and normalized future kernels preserve the previous support conditions. Hence all processed tail diagonal coordinates avoid their pure forbidden prefixes with probability one. Gluing the head and tail into the actual CRT point lets ordinary coverage supply a mixed cylinder ending in the tail and forces the physical covered event. The proof integrates coverage and the imported covered-event bound under the same joint law mu.joint of the head and its tail kernels. Thus the mu-expectation of totalCharge is at least one.

The same theorem supplies BaseCaps for every head whenever each positive-depth tail cylinder's explicit residual probability is at most one minus the coordinate threshold, multiplied by the requested comparison survival probability. These expressions retain the actual forbidden ancestor and descendant geometry. The existing kernels_have_caps theorem can then be applied directly. Applying the theorem to a law given only modulo 315 requires a distribution on the complete selected prime-power words satisfying headSafe; the theorem does not construct such a lift. A numerical or symbolic bound below one on the average total charge remains necessary to conclude noncoverage. The unrestricted odd covering problem remains open.

## References

- Truth anchor: `D5/S3/Arith/Congruence/ActualCylinderChain.ordinary_cover_forces_charge_and_caps`
- Dependency: [D5/S3/Arith/Congruence/PurePrefixResidualLaw](PurePrefixResidualLaw.md)
