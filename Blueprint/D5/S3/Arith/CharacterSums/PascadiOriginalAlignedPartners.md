# Aligned baselines and all zero-reduction partners

## Abstract

All actual coefficientwise zero-reduction partners have uniformly subpower cardinality, with no nonalignment restriction on the retained original baseline.

Keep the actual prime-cube word, oriented middle congruence basis, anchor physical(B,q)=(-w,-t), original units and retained baseline. Alignment means exact integer determinants det(q,base1)=det(q,base2)=0. The endpoint universe S is a finite set of actual ordered integer coordinate pairs, not a freely chosen coefficient set. The prime-p condition is coefficientwise P_e mod p=0, and includes both identically zero integer pencils and nonzero pencils whose coefficients are all divisible by p.

**Theorem 1.1 (Aligned original baselines force integer-zero pencils).**

Lean statement: `D5/S3/Arith/CharacterSums/PascadiOriginalAlignedPartners.actual_aligned_zero_reduction_partners_subpower`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/PascadiOriginalAlignedPartners.actual_aligned_zero_reduction_partners_subpower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Alexandru Pascadi (2026). *Non-abelian amplification and bilinear forms with Kloosterman sums*. DOI: [10.1007/s00039-026-00746-0](https://doi.org/10.1007/s00039-026-00746-0). URL: <https://arxiv.org/abs/2511.08445v2>.

*Commentary.*

For every epsilon>0, one positive C counts all actual zero-reduction partners of any aligned retained baseline by card(S)<=C*p^epsilon. The anchor, baseline and endpoints obey the J1,J2 coordinate bounds, every partner satisfies the original word and literal physical box, 2X<p^3 and 2Y<p^3, and 1<=J2<=J1. Retain the original basis, anchor, baseline and shifted-expression units. Require (J1*J2)^5<=M^5*p^3 and (24*(8*18)^4)^5*M^40<p. No rational-fiber weight is charged.

Over the prime field the aligned baseline vectors are scalar multiples u*q and v*q. The actual baseline units imply u+v-1, uv and uv-(u+v-1) are nonzero. The zero-reduction pencil completes to a nonzero scalar multiple of the square of l_q. Comparing its genuine homogeneous quadratic coefficients forces both endpoint determinants with q to vanish, including horizontal and vertical q. The original cutoffs yield 8J1J2<p, so the actual integer determinants vanish as well. A primitive integer direction expresses q and all four endpoints by scalar multiples of height at most J1. The integer pencil becomes E*l_v^3 with |E|<=6J1^3<p^3. The original prime-cube root and the unit l_v(beta) force E=0. Thus every actual partner has identically zero integer pencil, and the verified integer-zero divisor theorem supplies the count.

**Theorem 1.2 (The complete coefficientwise zero-reduction count).**

Lean statement: `D5/S3/Arith/CharacterSums/PascadiOriginalAlignedPartners.actual_zero_reduction_partners_subpower`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/PascadiOriginalAlignedPartners.actual_zero_reduction_partners_subpower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Alexandru Pascadi (2026). *Non-abelian amplification and bilinear forms with Kloosterman sums*. DOI: [10.1007/s00039-026-00746-0](https://doi.org/10.1007/s00039-026-00746-0). URL: <https://arxiv.org/abs/2511.08445v2>.

*Commentary.*

Under the same original units, word, coordinate, literal-box, cap and cutoff hypotheses, card(S)<=C*p^epsilon for every actual coefficientwise zero-reduction partner set S. The retained baseline may be aligned or nonaligned; it is never replaced by an assumed convenient baseline.

For an aligned baseline use the preceding theorem. Otherwise form the actual finite coordinate universe from the first and second projections of S together with both baseline coordinates. Map the original endpoint identity modulo p to construct ActualPair for every member of S. Its actual injection into modularZeroPartners allows direct consumption of original_modular_zero_partner_subpower, whose nonalignment premise is now satisfied in this branch. A single constant chosen before all data covers both branches.

The source problem is due to Pascadi. This completes the actual zero-reduction exceptional layer, including nonzero content-p pencils and integer-zero pencils. It does not by itself bound all original six-variable solutions or assert completion of the full conjecture.

## References

- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiOriginalAlignedPartners.actual_aligned_zero_reduction_partners_subpower`
- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiOriginalAlignedPartners.actual_zero_reduction_partners_subpower`
- Dependency: [D5/S3/Arith/CharacterSums/PascadiOriginalExceptionalPartners](PascadiOriginalExceptionalPartners.md)
- Dependency: [D5/S3/Arith/CharacterSums/PascadiOriginalModularPartners](PascadiOriginalModularPartners.md)
