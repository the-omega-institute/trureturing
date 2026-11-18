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

## References

- Truth anchor: `D5/S3/TotalVariation/ParryFirstReturn.actual_first_return_system`
- Dependency: [D5/S3/TotalVariation/ParryBilateralLaw](ParryBilateralLaw.md)
