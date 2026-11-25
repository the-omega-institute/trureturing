# Critical sign masks at the sharp score cutoff

## Abstract

At the proposed sharp cutoff every compatible sign mask of the ten Born rows has five entries and belongs to the critical pair-product class.

**Definition 1.1 (Compatible sign choices, including ties).**

Lean statement: `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/CriticalSign.SignCompatible`

*Formalization.* `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/CriticalSign.SignCompatible` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For outcome tables p and q a compatible mask contains only rows with q ≤ p, and its complement contains only rows with p ≤ q. Either choice is admissible at a tied row.

**Theorem 1.2 (Baseline and complementary-row harmonic mass).**

Lean statement: `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/CriticalSign.harmonicOverlap_ge_sign_mask`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/CriticalSign.harmonicOverlap_ge_sign_mask` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For nonnegative tables with first-law total mass two, the harmonic overlap is at least half the sum of the minima. If a complementary set of rows satisfies 0.09(p+q) ≤ q−p and p+q > 0, the overlap is at least (2 − maskMass p s + maskMass q s)/2 plus 0.045 times the first-law mass on that set. The baseline estimate includes a common zero row.

**Definition 1.3 (The critical pair-product class).**

Lean statement: `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/CriticalSign.CriticalPairProduct`

*Formalization.* `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/CriticalSign.CriticalPairProduct` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A pair of two-element masks in the two bases belongs to this class if the product of their ordered differences in the residue field modulo five is 1 or −1.

**Definition 1.4 (Critical masks of size five).**

Lean statement: `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/CriticalSign.CriticalFiveMask`

*Formalization.* `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/CriticalSign.CriticalFiveMask` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Either the computational pair and the omitted Fourier pair are critical, or the omitted computational pair and the Fourier pair are critical.

**Theorem 1.5 (Strict harmonic deficit on the four-row tails).**

Lean statement: `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/CriticalSign.rankFour_overlap_gt_sharpD`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/CriticalSign.rankFour_overlap_gt_sharpD` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If the sign-mask mass difference is at most 1 + σ and on a complementary tail the first-law square-root mass exceeds 0.228, each first-law amplitude is below 0.305, and the second amplitude exceeds the first by 0.029, the harmonic overlap strictly exceeds (3 − √5)/10. Squaring the amplitude comparison gives the required relative difference 0.09. The exact rational bounds budget both spectral deficits jointly in the critical rank-four application.

**Theorem 1.6 (Every compatible sign mask is critical at the cutoff).**

Lean statement: `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/CriticalSign.critical_sign_mask_at_cutoff`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/CriticalSign.critical_sign_mask_at_cutoff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Any pair of complex unit vectors with combined score at least (14 + 2√5)/5 has a sign-mask mass difference at least 2c², where c = √((7 + √5)/10). A noncritical mask of size at most four has mass difference at most 1 + √(3/5), and a noncritical five-row mask has mass difference at most 2√(4/5). Both are strictly below 2c². The critical rank-four mask is excluded by the harmonic tail estimate. Complement and simultaneous exchange of the two states reduces larger masks to the smaller side, proving the claim for every tie assignment.

**Theorem 1.7 (No tied row at the closed cutoff).**

Lean statement: `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/CriticalSign.fiveLaw_ne_at_cutoff`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/CriticalSign.fiveLaw_ne_at_cutoff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In the cutoff regime the two Born probabilities are unequal in every computational and Fourier row. Inserting a tied row into the strict positive sign mask would give a second compatible mask of different cardinality, contradicting the requirement that both have five entries.

## References

- Truth anchor: `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/CriticalSign.CriticalFiveMask`
- Truth anchor: `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/CriticalSign.CriticalPairProduct`
- Truth anchor: `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/CriticalSign.SignCompatible`
- Truth anchor: `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/CriticalSign.critical_sign_mask_at_cutoff`
- Truth anchor: `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/CriticalSign.fiveLaw_ne_at_cutoff`
- Truth anchor: `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/CriticalSign.harmonicOverlap_ge_sign_mask`
- Truth anchor: `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/CriticalSign.rankFour_overlap_gt_sharpD`
- Dependency: [D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/RankFourReference](RankFourReference.md)
