# The actual zero-section return system

## Abstract

The actual zero-section return system of the bilateral Parry source.

**Theorem 1.1 (The native section, induced probability and occupation law).**

Lean statement: `D5/S3/TotalVariation/ParryFirstReturn.actual_first_return_system`

*Proof.* Machine-checked in Lean as `D5/S3/TotalVariation/ParryFirstReturn.actual_first_return_system` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let k >= 2 and retain one coding e and one probability mu from ParryBilateralLaw.bilateral_parry_law, or from its simultaneous ParryBilateralMixing.bilateral_parry_mixing extension. The hypotheses used here are exactly the preceding-run characterization of the suffix, stationarity of mu under relationShift, and the supplied suffix-cylinder formula. The signed path law nu and the product pushforward of fairAnchor times mu can therefore be retained from that same simultaneous choice.

Set A = {r : r(-1) = false}. The section is exactly {J_0 = 0}, where J_t is the suffix coordinate of e(false,r) at time t. Its mass is a = 1 / normalizer(k) > 0. The actual return time tau(r) is one plus the least natural n with r(n) = false. Thus 1 <= tau(r) <= k, S(r) = relationShift iterated tau(r) times belongs to A, and no positive smaller shift iterate belongs to A. On A this is the actual induced map. The measure mu_A is literally (mu(A))^(-1) times mu restricted to A, represented on the ambient relation space. It is a probability and S preserves it.

For each i in Fin k, the image under relationShift iterated i times of {r in A : i < tau(r)} is exactly {J_0 = i}. To reconstruct its base, translate the complete bilateral relation path backwards by i; the preceding-run characterization gives membership in A and forbids an earlier return. These disjoint suffix cylinders cover the entire relation space. Consequently the original source probability is exactly a times the sum, over i in Fin k, of the pushforward of mu_A restricted to {i < tau} under the i-th shift iterate. This is the occupation law of the actual bounded return tower.

Induced preservation follows by partitioning a section event according to its least positive return time. Each branch is a shift iterate and has unchanged measure. The images are disjoint, and translating to the nearest preceding zero supplies their cover of the section. The section mass uses the length-one suffix cylinder and the identity that the zero-suffix weight is one.

The first-return framework is classical. The entropy transfer for a sweeping section is the Abramov formula; a finite-partition proof is in Downarowicz, Kwietniak and Lacka, Uniform continuity of entropy rate with respect to the f-bar-pseudometric, Propositions 3.1-3.2 and Theorem 5.1, DOI 10.1109/TIT.2021.3111831. The statement here identifies the native section and occupation measure; it makes no entropy assertion.

**Theorem 1.2 (Joint law of consecutive return times).**

Lean statement: `D5/S3/TotalVariation/ParryFirstReturn.return_time_cylinder_probability`

*Proof.* Machine-checked in Lean as `D5/S3/TotalVariation/ParryFirstReturn.return_time_cylinder_probability` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Use the same bilateral Parry coding and probability. Write p for parryParameter(k). For a list of durations d_0, ..., d_(m-1) in {1, ..., k}, the normalized section probability of observing these first m successive return times is the product of p raised to each duration. The Lean list stores each duration minus one in Fin k. The empty list has conditional probability one.

A return of duration d has suffix coordinates 0, 1, ..., d-1, 0. These statements hold on each actual path in the section. The nearest zero determines the next increment or reset, and the terminal zero starts the next block at the same path shifted by the first return. Concatenating these blocks with their common zeros identified gives one exact suffix cylinder on the original path space.

On an allowed transition from suffix i to suffix j, the kernel is p times the ratio of the positive suffix weights at j and i. The initial and terminal suffixes of the cylinder are zero, so the weight ratios telescope. The one-coordinate initial mass cancels with the section normalization. The remaining power of p splits into one factor per duration.

**Theorem 1.3 (Probability of a legal raw window).**

Lean statement: `D5/S3/TotalVariation/ParryFirstReturn.zero_section_raw_window`

*Proof.* Machine-checked in Lean as `D5/S3/TotalVariation/ParryFirstReturn.zero_section_raw_window` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Start in the zero section of the bilateral Parry source and condition the same source probability on that section. Take a legal suffix path of m transitions starting at zero. Read each successive destination as a zero on a reset and a one on an increment. The probability of the resulting raw bit window is p^m times the weight of the final suffix.

The first suffix is known. At each step the raw bit determines which transition to take, hence determines the next suffix. Thus the raw window on the section is exactly one suffix cylinder. The product of transition weights telescopes and leaves the final suffix weight. That weight is one when the last bit is a reset.

## References

- Truth anchor: `D5/S3/TotalVariation/ParryFirstReturn.actual_first_return_system`
- Truth anchor: `D5/S3/TotalVariation/ParryFirstReturn.return_time_cylinder_probability`
- Truth anchor: `D5/S3/TotalVariation/ParryFirstReturn.zero_section_raw_window`
- Dependency: [D5/S3/TotalVariation/ParryBilateralLaw](ParryBilateralLaw.md)
