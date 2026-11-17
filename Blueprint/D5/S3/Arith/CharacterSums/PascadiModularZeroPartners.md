# Modular-zero partner count: determinant component

## Abstract

The original integer chart carries the finite actual modular-zero partner set. In the regular dividing branch, the three modular determinant equations lift to exact integer equations under 8J₁J₂<p, giving a signed divisor bound. In the nondividing branch, formal polynomial cancellation classifies every field-coordinate partner among six ordered pairs; coordinate reduction is injective on the bounded integer box, so at most six actual pairs remain.

The source is the supplied proof.tex, Lemma modular-zero partner bound, lines 235–370, SHA256 81da80fcfc8b93fadb2b5bb12d99f7ea4ea7a8b4c1cd95594e763e378bc21f7f. The definitions retain Original.Coordinate, Original.Endpoint and the actual original endpointL, endpointQ and pencil. ActualPair uses u(i,j)=α+i+βj and the equation u(x)u(y)=α(α+q₁+βq₂).

For integer directions f,h with det(f,h)≠0 and AC=det(q,h)det(q,f)≠0, an oriented pair (z,v) satisfies three modular equations: det(f,z)=0, det(h,v−q)=0 and det(z−q,v)=0. The direction bounds are |f₁|≤J₁, |f₂|≤J₂, |h₁|≤2J₁, |h₂|≤2J₂; q,z,v lie in the original rectangle. Their determinant heights are at most 2J₁J₂, 8J₁J₂ and 4J₁J₂. Thus 8J₁J₂<p forces all three integer determinants to vanish.

The map (z,v)↦(det(z−q,h),det(f,v)) lands in Int.divisorsAntidiag(AC). Its injectivity follows from det(f,h)≠0 and the two line equations, without choosing primitive integer generators. Consequently the oriented count is at most the cardinality of that signed divisor antidiagonal, and allowing both endpoint orientations gives twice that cardinality. The constant satisfies |AC|≤8(J₁J₂)²<p².

The regular dividing branch supplies both modular line orientations, a divisor count for the actual pencil, and a uniform prime subpower bound under explicit direction hypotheses. The nondividing branch has an absolute six-partner bound under nonzero det(a,a+b−q) and det(a+b−q,b), using injectivity of full coordinate reduction on the bounded box. The original-source nondegeneracy supplier and combination of branches belong to PascadiOriginalModularPartners. These counts are intermediate components of the B⁵ prime-count prerequisite.

In the regular dividing branch, q=b+(1−c)a and det(b,q)≠0. Perpendicular evaluation of the homogeneous pencil identity assigns z or v to the b-line. Writing that endpoint as k b and comparing all three quadratic coefficients gives (ck−1)v=kb−q. Since det(b,q)≠0, ck−1 is nonzero. The relation then yields det(a−q,v−q)=0 and det(z−q,v)=0, or their swapped counterparts. The original mapped pencil supplies the homogeneous identity after cancelling its nonzero base linear factor, including constant and vertical directions. Consequently actual modular-zero partners in this branch satisfy the two-orientation divisor count.

For the nondividing identity L_d L_z L_v=(L_z+L_v−L_q)L_a L_b with d=a+b−q, assume det(a,d) and det(d,b) are nonzero. Formal cancellation handles zero endpoints, yielding only (0,q) and (q,0). For nonzero endpoints, evaluating at a perpendicular direction puts one endpoint on the a-line; after cancelling L_a, evaluation at a perpendicular direction to b puts the other on the b-line. Write z=ka and v=lb. Coefficient comparison gives (kl−1)d=(k−1)a+(l−1)b. Its determinants force either k=l=1 or k=(det(a,b)−det(d,b))/det(a,d) and l=(det(a,b)−det(a,d))/det(d,b). Thus six ordered field pairs suffice, including proportional a,b and characteristic two. For bounded integer endpoints, J₁,J₂≥1 and 8J₁J₂<p make coordinate reduction injective, giving the actual count at most six without injectivity of the single shifted value α+i+βj.

**Definition 1.1 (coordinateDet).**

Lean statement: `D5/S3/Arith/CharacterSums/PascadiModularZeroPartners.coordinateDet`

*Formalization.* `D5/S3/Arith/CharacterSums/PascadiModularZeroPartners.coordinateDet` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Alexandru Pascadi (2026). *Non-abelian amplification and bilinear forms with Kloosterman sums*. DOI: [10.1007/s00039-026-00746-0](https://doi.org/10.1007/s00039-026-00746-0). URL: <https://arxiv.org/abs/2511.08445v2>.

*Commentary.*

Determinant of actual integer coordinates.

**Definition 1.2 (actualValue).**

Lean statement: `D5/S3/Arith/CharacterSums/PascadiModularZeroPartners.actualValue`

*Formalization.* `D5/S3/Arith/CharacterSums/PascadiModularZeroPartners.actualValue` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Alexandru Pascadi (2026). *Non-abelian amplification and bilinear forms with Kloosterman sums*. DOI: [10.1007/s00039-026-00746-0](https://doi.org/10.1007/s00039-026-00746-0). URL: <https://arxiv.org/abs/2511.08445v2>.

*Commentary.*

Original shifted endpoint value α+i+βj.

**Definition 1.3 (ActualPair).**

Lean statement: `D5/S3/Arith/CharacterSums/PascadiModularZeroPartners.ActualPair`

*Formalization.* `D5/S3/Arith/CharacterSums/PascadiModularZeroPartners.ActualPair` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Alexandru Pascadi (2026). *Non-abelian amplification and bilinear forms with Kloosterman sums*. DOI: [10.1007/s00039-026-00746-0](https://doi.org/10.1007/s00039-026-00746-0). URL: <https://arxiv.org/abs/2511.08445v2>.

*Commentary.*

Both endpoints belong to E and satisfy the actual anchor product equation.

**Definition 1.4 (modularZeroPartners).**

Lean statement: `D5/S3/Arith/CharacterSums/PascadiModularZeroPartners.modularZeroPartners`

*Formalization.* `D5/S3/Arith/CharacterSums/PascadiModularZeroPartners.modularZeroPartners` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Alexandru Pascadi (2026). *Non-abelian amplification and bilinear forms with Kloosterman sums*. DOI: [10.1007/s00039-026-00746-0](https://doi.org/10.1007/s00039-026-00746-0). URL: <https://arxiv.org/abs/2511.08445v2>.

*Commentary.*

Finite actual endpoint pairs with identically zero original pencil modulo p.

**Definition 1.5 (Aligned).**

Lean statement: `D5/S3/Arith/CharacterSums/PascadiModularZeroPartners.Aligned`

*Formalization.* `D5/S3/Arith/CharacterSums/PascadiModularZeroPartners.Aligned` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Alexandru Pascadi (2026). *Non-abelian amplification and bilinear forms with Kloosterman sums*. DOI: [10.1007/s00039-026-00746-0](https://doi.org/10.1007/s00039-026-00746-0). URL: <https://arxiv.org/abs/2511.08445v2>.

*Commentary.*

Exact integer collinearity of both endpoints with q.

**Definition 1.6 (ModularLinePair).**

Lean statement: `D5/S3/Arith/CharacterSums/PascadiModularZeroPartners.ModularLinePair`

*Formalization.* `D5/S3/Arith/CharacterSums/PascadiModularZeroPartners.ModularLinePair` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Alexandru Pascadi (2026). *Non-abelian amplification and bilinear forms with Kloosterman sums*. DOI: [10.1007/s00039-026-00746-0](https://doi.org/10.1007/s00039-026-00746-0). URL: <https://arxiv.org/abs/2511.08445v2>.

*Commentary.*

Three modular determinant conditions on an oriented endpoint pair.

**Theorem 1.7 (modular_line_pair_integer_lift).**

Lean statement: `D5/S3/Arith/CharacterSums/PascadiModularZeroPartners.modular_line_pair_integer_lift`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/PascadiModularZeroPartners.modular_line_pair_integer_lift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Alexandru Pascadi (2026). *Non-abelian amplification and bilinear forms with Kloosterman sums*. DOI: [10.1007/s00039-026-00746-0](https://doi.org/10.1007/s00039-026-00746-0). URL: <https://arxiv.org/abs/2511.08445v2>.

*Commentary.*

All three exact integer determinant equations follow from rectangle bounds and modular vanishing.

**Theorem 1.8 (oriented_modular_line_partner_count).**

Lean statement: `D5/S3/Arith/CharacterSums/PascadiModularZeroPartners.oriented_modular_line_partner_count`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/PascadiModularZeroPartners.oriented_modular_line_partner_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Alexandru Pascadi (2026). *Non-abelian amplification and bilinear forms with Kloosterman sums*. DOI: [10.1007/s00039-026-00746-0](https://doi.org/10.1007/s00039-026-00746-0). URL: <https://arxiv.org/abs/2511.08445v2>.

*Commentary.*

The finite oriented endpoint count is bounded by the cardinality of Int.divisorsAntidiag(AC).

**Theorem 1.9 (modular_line_partner_count).**

Lean statement: `D5/S3/Arith/CharacterSums/PascadiModularZeroPartners.modular_line_partner_count`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/PascadiModularZeroPartners.modular_line_partner_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Alexandru Pascadi (2026). *Non-abelian amplification and bilinear forms with Kloosterman sums*. DOI: [10.1007/s00039-026-00746-0](https://doi.org/10.1007/s00039-026-00746-0). URL: <https://arxiv.org/abs/2511.08445v2>.

*Commentary.*

The two endpoint orientations have total cardinality at most twice the signed divisor bound; the same theorem supplies |AC|≤8(J₁J₂)²<p².

**Theorem 1.10 (regular_dividing_homogeneous_lines).**

Lean statement: `D5/S3/Arith/CharacterSums/PascadiModularZeroPartners.regular_dividing_homogeneous_lines`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/PascadiModularZeroPartners.regular_dividing_homogeneous_lines` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Alexandru Pascadi (2026). *Non-abelian amplification and bilinear forms with Kloosterman sums*. DOI: [10.1007/s00039-026-00746-0](https://doi.org/10.1007/s00039-026-00746-0). URL: <https://arxiv.org/abs/2511.08445v2>.

*Commentary.*

The regular homogeneous pencil identity forces all three determinant lines in one of the two endpoint orientations.

**Theorem 1.11 (regular_dividing_actual_line_cover).**

Lean statement: `D5/S3/Arith/CharacterSums/PascadiModularZeroPartners.regular_dividing_actual_line_cover`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/PascadiModularZeroPartners.regular_dividing_actual_line_cover` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Alexandru Pascadi (2026). *Non-abelian amplification and bilinear forms with Kloosterman sums*. DOI: [10.1007/s00039-026-00746-0](https://doi.org/10.1007/s00039-026-00746-0). URL: <https://arxiv.org/abs/2511.08445v2>.

*Commentary.*

The actual mapped pencil supplies the regular homogeneous identity and both modular line orientations.

**Theorem 1.12 (regular_dividing_modular_zero_partner_count).**

Lean statement: `D5/S3/Arith/CharacterSums/PascadiModularZeroPartners.regular_dividing_modular_zero_partner_count`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/PascadiModularZeroPartners.regular_dividing_modular_zero_partner_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Alexandru Pascadi (2026). *Non-abelian amplification and bilinear forms with Kloosterman sums*. DOI: [10.1007/s00039-026-00746-0](https://doi.org/10.1007/s00039-026-00746-0). URL: <https://arxiv.org/abs/2511.08445v2>.

*Commentary.*

The actual regular dividing partner set satisfies the two-orientation signed divisor bound.

**Theorem 1.13 (signed_divisors_antidiag_subpower).**

Lean statement: `D5/S3/Arith/CharacterSums/PascadiModularZeroPartners.signed_divisors_antidiag_subpower`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/PascadiModularZeroPartners.signed_divisors_antidiag_subpower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Alexandru Pascadi (2026). *Non-abelian amplification and bilinear forms with Kloosterman sums*. DOI: [10.1007/s00039-026-00746-0](https://doi.org/10.1007/s00039-026-00746-0). URL: <https://arxiv.org/abs/2511.08445v2>.

*Commentary.*

The signed divisor antidiagonal inherits a uniform subpower bound from the classical natural divisor estimate.

**Theorem 1.14 (regular_dividing_modular_zero_partner_subpower).**

Lean statement: `D5/S3/Arith/CharacterSums/PascadiModularZeroPartners.regular_dividing_modular_zero_partner_subpower`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/PascadiModularZeroPartners.regular_dividing_modular_zero_partner_subpower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Alexandru Pascadi (2026). *Non-abelian amplification and bilinear forms with Kloosterman sums*. DOI: [10.1007/s00039-026-00746-0](https://doi.org/10.1007/s00039-026-00746-0). URL: <https://arxiv.org/abs/2511.08445v2>.

*Commentary.*

For every positive epsilon, a constant independent of p bounds regular dividing actual partners by C times p to epsilon.

**Theorem 1.15 (nondividing_modular_zero_partner_count).**

Lean statement: `D5/S3/Arith/CharacterSums/PascadiModularZeroPartners.nondividing_modular_zero_partner_count`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/PascadiModularZeroPartners.nondividing_modular_zero_partner_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Alexandru Pascadi (2026). *Non-abelian amplification and bilinear forms with Kloosterman sums*. DOI: [10.1007/s00039-026-00746-0](https://doi.org/10.1007/s00039-026-00746-0). URL: <https://arxiv.org/abs/2511.08445v2>.

*Commentary.*

The bounded integer endpoints reduce injectively modulo p, transferring the six field-coordinate candidates to an absolute count of at most six actual partners.

**Theorem 1.16 (modular_line_divisor_height).**

Lean statement: `D5/S3/Arith/CharacterSums/PascadiModularZeroPartners.modular_line_divisor_height`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/PascadiModularZeroPartners.modular_line_divisor_height` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Alexandru Pascadi (2026). *Non-abelian amplification and bilinear forms with Kloosterman sums*. DOI: [10.1007/s00039-026-00746-0](https://doi.org/10.1007/s00039-026-00746-0). URL: <https://arxiv.org/abs/2511.08445v2>.

*Commentary.*

The divisor constant has absolute value at most 8(J₁J₂)², strictly less than p².

## References

- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiModularZeroPartners.ActualPair`
- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiModularZeroPartners.Aligned`
- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiModularZeroPartners.ModularLinePair`
- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiModularZeroPartners.actualValue`
- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiModularZeroPartners.coordinateDet`
- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiModularZeroPartners.modularZeroPartners`
- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiModularZeroPartners.modular_line_divisor_height`
- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiModularZeroPartners.modular_line_pair_integer_lift`
- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiModularZeroPartners.modular_line_partner_count`
- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiModularZeroPartners.nondividing_modular_zero_partner_count`
- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiModularZeroPartners.oriented_modular_line_partner_count`
- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiModularZeroPartners.regular_dividing_actual_line_cover`
- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiModularZeroPartners.regular_dividing_homogeneous_lines`
- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiModularZeroPartners.regular_dividing_modular_zero_partner_count`
- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiModularZeroPartners.regular_dividing_modular_zero_partner_subpower`
- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiModularZeroPartners.signed_divisors_antidiag_subpower`
- Dependency: [D5/S3/Arith/CharacterSums/PascadiModularZeroFieldPartners](PascadiModularZeroFieldPartners.md)
- Dependency: [D5/S3/Arith/CharacterSums/PascadiOriginalCoefficients](PascadiOriginalCoefficients.md)
- Dependency: [D5/S3/Arith/Divisors/DivisorSubpower](../Divisors/DivisorSubpower.md)
