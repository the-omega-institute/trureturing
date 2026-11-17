# Modular-zero partner count: determinant component

## Abstract

The original integer chart carries the finite actual modular-zero partner set. For endpoints in the rectangle, the three modular determinant equations on one orientation of two lines lift to exact integer equations under 8J₁J₂<p. A direct injective map into signed divisor pairs gives the finite count; both orientations cost a factor of two. The full polynomial-to-lines classification and nondividing absolute bound remain open.

The source is the supplied proof.tex, Lemma modular-zero partner bound, lines 235–370, SHA256 81da80fcfc8b93fadb2b5bb12d99f7ea4ea7a8b4c1cd95594e763e378bc21f7f. The definitions retain Original.Coordinate, Original.Endpoint and the actual original endpointL, endpointQ and pencil. ActualPair uses u(i,j)=α+i+βj and the equation u(x)u(y)=α(α+q₁+βq₂).

For integer directions f,h with det(f,h)≠0 and AC=det(q,h)det(q,f)≠0, an oriented pair (z,v) satisfies three modular equations: det(f,z)=0, det(h,v−q)=0 and det(z−q,v)=0. The direction bounds are |f₁|≤J₁, |f₂|≤J₂, |h₁|≤2J₁, |h₂|≤2J₂; q,z,v lie in the original rectangle. Their determinant heights are at most 2J₁J₂, 8J₁J₂ and 4J₁J₂. Thus 8J₁J₂<p forces all three integer determinants to vanish.

The map (z,v)↦(det(z−q,h),det(f,v)) lands in Int.divisorsAntidiag(AC). Its injectivity follows from det(f,h)≠0 and the two line equations, without choosing primitive integer generators. Consequently the oriented count is at most the cardinality of that signed divisor antidiagonal, and allowing both endpoint orientations gives twice that cardinality. The constant satisfies |AC|≤8(J₁J₂)²<p².

Nonaligned actual pairs have nonzero evaluations of L and Q and a nonzero quartic Q(Q−LZ), using actual injectivity and κ≠0. The regular dividing branch now supplies both modular line orientations and a divisor count for the actual pencil, under explicit nondegeneracy assumptions on the selected directions. Completing the full partner theorem still requires the nondividing absolute bound, deriving the direction nondegeneracy from the paper hypotheses, and applying divisor growth. The finite determinant count is an intermediate component of the B⁵ prime-count prerequisite.

In the regular dividing branch, q=b+(1−c)a and det(b,q)≠0. Perpendicular evaluation of the homogeneous pencil identity assigns z or v to the b-line. Writing that endpoint as k b and comparing all three quadratic coefficients gives (ck−1)v=kb−q. Since det(b,q)≠0, ck−1 is nonzero. The relation then yields det(a−q,v−q)=0 and det(z−q,v)=0, or their swapped counterparts. The original mapped pencil supplies the homogeneous identity after cancelling its nonzero base linear factor, including constant and vertical directions. Consequently actual modular-zero partners in this branch satisfy the two-orientation divisor count.

**Definition 1.1 (coordinateDet).**

Lean statement: `D5/S3/Arith/CharacterSums/PascadiModularZeroPartners.coordinateDet`

*Formalization.* `D5/S3/Arith/CharacterSums/PascadiModularZeroPartners.coordinateDet` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Alexandru Pascadi (2026). *Non-abelian amplification and bilinear forms with Kloosterman sums*. URL: <https://arxiv.org/abs/2511.08445v2>.

*Commentary.*

Determinant of actual integer coordinates.

**Definition 1.2 (actualValue).**

Lean statement: `D5/S3/Arith/CharacterSums/PascadiModularZeroPartners.actualValue`

*Formalization.* `D5/S3/Arith/CharacterSums/PascadiModularZeroPartners.actualValue` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Alexandru Pascadi (2026). *Non-abelian amplification and bilinear forms with Kloosterman sums*. URL: <https://arxiv.org/abs/2511.08445v2>.

*Commentary.*

Original shifted endpoint value α+i+βj.

**Definition 1.3 (ActualPair).**

Lean statement: `D5/S3/Arith/CharacterSums/PascadiModularZeroPartners.ActualPair`

*Formalization.* `D5/S3/Arith/CharacterSums/PascadiModularZeroPartners.ActualPair` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Alexandru Pascadi (2026). *Non-abelian amplification and bilinear forms with Kloosterman sums*. URL: <https://arxiv.org/abs/2511.08445v2>.

*Commentary.*

Both endpoints belong to E and satisfy the actual anchor product equation.

**Definition 1.4 (modularZeroPartners).**

Lean statement: `D5/S3/Arith/CharacterSums/PascadiModularZeroPartners.modularZeroPartners`

*Formalization.* `D5/S3/Arith/CharacterSums/PascadiModularZeroPartners.modularZeroPartners` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Alexandru Pascadi (2026). *Non-abelian amplification and bilinear forms with Kloosterman sums*. URL: <https://arxiv.org/abs/2511.08445v2>.

*Commentary.*

Finite actual endpoint pairs with identically zero original pencil modulo p.

**Definition 1.5 (Aligned).**

Lean statement: `D5/S3/Arith/CharacterSums/PascadiModularZeroPartners.Aligned`

*Formalization.* `D5/S3/Arith/CharacterSums/PascadiModularZeroPartners.Aligned` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Alexandru Pascadi (2026). *Non-abelian amplification and bilinear forms with Kloosterman sums*. URL: <https://arxiv.org/abs/2511.08445v2>.

*Commentary.*

Exact integer collinearity of both endpoints with q.

**Theorem 1.6 (nonaligned_actual_pair_nondegenerate).**

Lean statement: `D5/S3/Arith/CharacterSums/PascadiModularZeroPartners.nonaligned_actual_pair_nondegenerate`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/PascadiModularZeroPartners.nonaligned_actual_pair_nondegenerate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Alexandru Pascadi (2026). *Non-abelian amplification and bilinear forms with Kloosterman sums*. URL: <https://arxiv.org/abs/2511.08445v2>.

*Commentary.*

Actual injectivity excludes anchor degeneracy and proves the nonzero L,Q evaluations and quartic.

**Definition 1.7 (ModularLinePair).**

Lean statement: `D5/S3/Arith/CharacterSums/PascadiModularZeroPartners.ModularLinePair`

*Formalization.* `D5/S3/Arith/CharacterSums/PascadiModularZeroPartners.ModularLinePair` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Alexandru Pascadi (2026). *Non-abelian amplification and bilinear forms with Kloosterman sums*. URL: <https://arxiv.org/abs/2511.08445v2>.

*Commentary.*

Three modular determinant conditions on an oriented endpoint pair.

**Theorem 1.8 (modular_line_pair_integer_lift).**

Lean statement: `D5/S3/Arith/CharacterSums/PascadiModularZeroPartners.modular_line_pair_integer_lift`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/PascadiModularZeroPartners.modular_line_pair_integer_lift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Alexandru Pascadi (2026). *Non-abelian amplification and bilinear forms with Kloosterman sums*. URL: <https://arxiv.org/abs/2511.08445v2>.

*Commentary.*

All three exact integer determinant equations follow from rectangle bounds and modular vanishing.

**Theorem 1.9 (oriented_modular_line_partner_count).**

Lean statement: `D5/S3/Arith/CharacterSums/PascadiModularZeroPartners.oriented_modular_line_partner_count`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/PascadiModularZeroPartners.oriented_modular_line_partner_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Alexandru Pascadi (2026). *Non-abelian amplification and bilinear forms with Kloosterman sums*. URL: <https://arxiv.org/abs/2511.08445v2>.

*Commentary.*

The finite oriented endpoint count is bounded by the cardinality of Int.divisorsAntidiag(AC).

**Theorem 1.10 (modular_line_partner_count).**

Lean statement: `D5/S3/Arith/CharacterSums/PascadiModularZeroPartners.modular_line_partner_count`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/PascadiModularZeroPartners.modular_line_partner_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Alexandru Pascadi (2026). *Non-abelian amplification and bilinear forms with Kloosterman sums*. URL: <https://arxiv.org/abs/2511.08445v2>.

*Commentary.*

The two endpoint orientations have total cardinality at most twice the signed divisor bound; the same theorem supplies |AC|≤8(J₁J₂)²<p².

**Definition 1.11 (fieldDet).**

Lean statement: `D5/S3/Arith/CharacterSums/PascadiModularZeroPartners.fieldDet`

*Formalization.* `D5/S3/Arith/CharacterSums/PascadiModularZeroPartners.fieldDet` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Alexandru Pascadi (2026). *Non-abelian amplification and bilinear forms with Kloosterman sums*. URL: <https://arxiv.org/abs/2511.08445v2>.

*Commentary.*

Homogeneous determinant over a commutative coefficient ring.

**Theorem 1.12 (regular_dividing_homogeneous_lines).**

Lean statement: `D5/S3/Arith/CharacterSums/PascadiModularZeroPartners.regular_dividing_homogeneous_lines`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/PascadiModularZeroPartners.regular_dividing_homogeneous_lines` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Alexandru Pascadi (2026). *Non-abelian amplification and bilinear forms with Kloosterman sums*. URL: <https://arxiv.org/abs/2511.08445v2>.

*Commentary.*

The regular homogeneous pencil identity forces all three determinant lines in one of the two endpoint orientations.

**Theorem 1.13 (regular_dividing_actual_line_cover).**

Lean statement: `D5/S3/Arith/CharacterSums/PascadiModularZeroPartners.regular_dividing_actual_line_cover`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/PascadiModularZeroPartners.regular_dividing_actual_line_cover` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Alexandru Pascadi (2026). *Non-abelian amplification and bilinear forms with Kloosterman sums*. URL: <https://arxiv.org/abs/2511.08445v2>.

*Commentary.*

The actual mapped pencil supplies the regular homogeneous identity and both modular line orientations.

**Theorem 1.14 (regular_dividing_modular_zero_partner_count).**

Lean statement: `D5/S3/Arith/CharacterSums/PascadiModularZeroPartners.regular_dividing_modular_zero_partner_count`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/PascadiModularZeroPartners.regular_dividing_modular_zero_partner_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Alexandru Pascadi (2026). *Non-abelian amplification and bilinear forms with Kloosterman sums*. URL: <https://arxiv.org/abs/2511.08445v2>.

*Commentary.*

The actual regular dividing partner set satisfies the two-orientation signed divisor bound.

**Theorem 1.15 (modular_line_divisor_height).**

Lean statement: `D5/S3/Arith/CharacterSums/PascadiModularZeroPartners.modular_line_divisor_height`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/PascadiModularZeroPartners.modular_line_divisor_height` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Alexandru Pascadi (2026). *Non-abelian amplification and bilinear forms with Kloosterman sums*. URL: <https://arxiv.org/abs/2511.08445v2>.

*Commentary.*

The divisor constant has absolute value at most 8(J₁J₂)², strictly less than p².

## References

- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiModularZeroPartners.ActualPair`
- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiModularZeroPartners.Aligned`
- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiModularZeroPartners.ModularLinePair`
- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiModularZeroPartners.actualValue`
- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiModularZeroPartners.coordinateDet`
- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiModularZeroPartners.fieldDet`
- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiModularZeroPartners.modularZeroPartners`
- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiModularZeroPartners.modular_line_divisor_height`
- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiModularZeroPartners.modular_line_pair_integer_lift`
- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiModularZeroPartners.modular_line_partner_count`
- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiModularZeroPartners.nonaligned_actual_pair_nondegenerate`
- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiModularZeroPartners.oriented_modular_line_partner_count`
- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiModularZeroPartners.regular_dividing_actual_line_cover`
- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiModularZeroPartners.regular_dividing_homogeneous_lines`
- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiModularZeroPartners.regular_dividing_modular_zero_partner_count`
- Dependency: [D5/S3/Arith/CharacterSums/PascadiOriginalCoefficients](PascadiOriginalCoefficients.md)
