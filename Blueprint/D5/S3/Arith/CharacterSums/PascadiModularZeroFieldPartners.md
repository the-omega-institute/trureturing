# Field geometry of nondividing modular-zero partners

## Abstract

The formal cubic pencil identity has at most six ordered field-coordinate partners when both direction determinants are nonzero. This field classification is consumed by the actual bounded integer partner count; it does not by itself count original six-tuples.

For the identity L_d L_z L_v=(L_z+L_v-L_q)L_a L_b with d=a+b-q, assume det(a,d) and det(d,b) are nonzero. Zero endpoints give only (0,q) and (q,0). Otherwise perpendicular evaluation and formal cancellation put the two endpoints on the a-line and b-line, in one of the two orientations. Writing z=ka and v=lb gives (kl-1)d=(k-1)a+(l-1)b. Determinants force either k=l=1 or the displayed nondividingLambda and nondividingMu. The argument retains proportional a,b and characteristic two.

The determinant and its scalar-collinearity lemma are also used by the regular dividing branch. The two explicit candidate scalars are shared with the finite field-pair set in PascadiModularZeroPartners. The passage from six field-coordinate pairs to at most six actual integer pairs uses full coordinate reduction on the bounded box in that importing module; no injectivity of a single shifted linear observation is asserted.

**Definition 1.1 (fieldDet).**

Lean statement: `D5/S3/Arith/CharacterSums/PascadiModularZeroFieldPartners.fieldDet`

*Formalization.* `D5/S3/Arith/CharacterSums/PascadiModularZeroFieldPartners.fieldDet` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Alexandru Pascadi (2026). *Non-abelian amplification and bilinear forms with Kloosterman sums*. DOI: [10.1007/s00039-026-00746-0](https://doi.org/10.1007/s00039-026-00746-0). URL: <https://arxiv.org/abs/2511.08445v2>.

*Commentary.*

The homogeneous determinant over a commutative coefficient ring.

**Theorem 1.2 (Collinearity gives a scalar).**

Lean statement: `D5/S3/Arith/CharacterSums/PascadiModularZeroFieldPartners.fieldDet_zero_scalar`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/PascadiModularZeroFieldPartners.fieldDet_zero_scalar` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Alexandru Pascadi (2026). *Non-abelian amplification and bilinear forms with Kloosterman sums*. DOI: [10.1007/s00039-026-00746-0](https://doi.org/10.1007/s00039-026-00746-0). URL: <https://arxiv.org/abs/2511.08445v2>.

*Commentary.*

Over a field, a vector with zero determinant against a nonzero vector is a scalar multiple of it.

**Definition 1.3 (First nondividing candidate scalar).**

Lean statement: `D5/S3/Arith/CharacterSums/PascadiModularZeroFieldPartners.nondividingLambda`

*Formalization.* `D5/S3/Arith/CharacterSums/PascadiModularZeroFieldPartners.nondividingLambda` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Alexandru Pascadi (2026). *Non-abelian amplification and bilinear forms with Kloosterman sums*. DOI: [10.1007/s00039-026-00746-0](https://doi.org/10.1007/s00039-026-00746-0). URL: <https://arxiv.org/abs/2511.08445v2>.

*Commentary.*

The first explicit candidate scalar, shared by the field cover and actual counting proof.

**Definition 1.4 (Second nondividing candidate scalar).**

Lean statement: `D5/S3/Arith/CharacterSums/PascadiModularZeroFieldPartners.nondividingMu`

*Formalization.* `D5/S3/Arith/CharacterSums/PascadiModularZeroFieldPartners.nondividingMu` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Alexandru Pascadi (2026). *Non-abelian amplification and bilinear forms with Kloosterman sums*. DOI: [10.1007/s00039-026-00746-0](https://doi.org/10.1007/s00039-026-00746-0). URL: <https://arxiv.org/abs/2511.08445v2>.

*Commentary.*

The second explicit candidate scalar, shared by the field cover and actual counting proof.

**Theorem 1.5 (Six ordered field-coordinate partners).**

Lean statement: `D5/S3/Arith/CharacterSums/PascadiModularZeroFieldPartners.nondividing_field_partner_cover`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/PascadiModularZeroFieldPartners.nondividing_field_partner_cover` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Alexandru Pascadi (2026). *Non-abelian amplification and bilinear forms with Kloosterman sums*. DOI: [10.1007/s00039-026-00746-0](https://doi.org/10.1007/s00039-026-00746-0). URL: <https://arxiv.org/abs/2511.08445v2>.

*Commentary.*

The formal cubic pencil identity and two nonzero direction determinants restrict every ordered field-coordinate partner to six explicit pairs.

## References

- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiModularZeroFieldPartners.fieldDet`
- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiModularZeroFieldPartners.fieldDet_zero_scalar`
- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiModularZeroFieldPartners.nondividingLambda`
- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiModularZeroFieldPartners.nondividingMu`
- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiModularZeroFieldPartners.nondividing_field_partner_cover`
- Dependency: [D5/S3/Arith/CharacterSums/PascadiOriginalCoefficients](PascadiOriginalCoefficients.md)
