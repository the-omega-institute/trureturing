# Divisor counts for the prime-square word

## Abstract

Signed divisors of nonzero integer products bound the prime-square middle word in its literal affine box.

**Theorem 1.1 (Count all integer points in the shifted box).**

Lean statement: `D5/S3/Arith/CharacterSums/PascadiPrimeSquareHyperbola.shifted_hyperbola_box_card_le`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/PascadiPrimeSquareHyperbola.shifted_hyperbola_box_card_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Alexandru Pascadi (2026). *Non-abelian amplification and bilinear forms with Kloosterman sums*. DOI: [10.1007/s00039-026-00746-0](https://doi.org/10.1007/s00039-026-00746-0). URL: <https://arxiv.org/abs/2511.08445v2>.

*Commentary.*

Fix a modulus q > 1, an integer t > 0 whose residue is a unit, a unit target C, and two integer shifts A₁,A₂. Suppose uᵢ represents t Aᵢ modulo q and b represents t(C − A₁ A₂). The two literal integer intervals lie within absolute radii X₁,X₂.

For each shifted product congruence solution, the cleared expression t a₁ a₂ + u₂ a₁ + u₁ a₂ is b + kq for a unique integer k. The coordinate radii give |k| at most the floor of (t X₁ X₂ + |u₂| X₁ + |u₁| X₂ + |b|)/q. In this level the shifted integer factors have product nₖ = u₁ u₂ + t(b + kq). It reduces to the unit t² C, so the product is nonzero. The first factor injects the level into the signed divisors of nₖ. Summing twice the positive divisor count of |nₖ| over the admissible levels bounds the full box count.

**Theorem 1.2 (The actual middle word gives a unit target).**

Lean statement: `D5/S3/Arith/CharacterSums/PascadiPrimeSquareHyperbola.middle_word_unit_hyperbola`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/PascadiPrimeSquareHyperbola.middle_word_unit_hyperbola` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Alexandru Pascadi (2026). *Non-abelian amplification and bilinear forms with Kloosterman sums*. DOI: [10.1007/s00039-026-00746-0](https://doi.org/10.1007/s00039-026-00746-0). URL: <https://arxiv.org/abs/2511.08445v2>.

*Commentary.*

In ZMod(p²) for prime p, let x₁ + x₂ + z = d x₁ x₂ z and assume x₁ + z and x₂ + z are nonzero modulo p. Then (d z x₁ − 1)(d z x₂ − 1) = 1 + d z² and the right side is a unit. If its reduction vanished, the factored equation would make one of the two reduced factors vanish in the field. Combining that vanishing with 1 + d z² = 0 modulo p gives the corresponding forbidden pair sum.

In reduced slope-lattice coordinates with xᵢ = E₁ aᵢ + F₁ bᵢ, unit d, z and E₁ allow division by (d z E₁)² and give shifts of exactly the type counted above.

**Theorem 1.3 (Choose a common unit approximation multiplier).**

Lean statement: `D5/S3/Arith/CharacterSums/PascadiPrimeSquareHyperbola.prime_square_simultaneous_approximation`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/PascadiPrimeSquareHyperbola.prime_square_simultaneous_approximation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Alexandru Pascadi (2026). *Non-abelian amplification and bilinear forms with Kloosterman sums*. DOI: [10.1007/s00039-026-00746-0](https://doi.org/10.1007/s00039-026-00746-0). URL: <https://arxiv.org/abs/2511.08445v2>.

*Commentary.*

For positive P₁,P₂ with P₁P₂ < p, partition pairs of least representatives modulo p² into P₁P₂ bins. Among the first P₁P₂ + 1 multiples of the two shifts, two lie in the same bin. Their positive multiplier difference t lies below p and is a unit modulo p². The coordinate differences uᵢ represent t times the shifts and satisfy |uᵢ|Pᵢ < p².

**Theorem 1.4 (Count the actual middle word in an affine box).**

Lean statement: `D5/S3/Arith/CharacterSums/PascadiPrimeSquareHyperbola.middle_word_affine_box_card_le`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/PascadiPrimeSquareHyperbola.middle_word_affine_box_card_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Alexandru Pascadi (2026). *Non-abelian amplification and bilinear forms with Kloosterman sums*. DOI: [10.1007/s00039-026-00746-0](https://doi.org/10.1007/s00039-026-00746-0). URL: <https://arxiv.org/abs/2511.08445v2>.

*Commentary.*

Fix xᵢ = E aᵢ + vᵢ over ZMod(p²) with E and d z units, and let the aᵢ range over the prescribed integer intervals. Retain the middle-word solutions whose two pair sums xᵢ + z are nonzero modulo p.

After factoring the word, division by (d z E)² gives the two shifts. When the retained set is nonempty, any point of it certifies that the normalized target is a unit. Choose the common multiplier from the approximation step and take b to be the least residue of the cleared constant. The divisor sum for the shifted box then bounds the retained count with those same parameters. For an empty retained set the bound holds with the same choice of parameters.

The weighted asymptotic estimate also requires bounds for the reduced slope lattice and the Fejér tails.

## References

- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiPrimeSquareHyperbola.middle_word_affine_box_card_le`
- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiPrimeSquareHyperbola.middle_word_unit_hyperbola`
- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiPrimeSquareHyperbola.prime_square_simultaneous_approximation`
- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiPrimeSquareHyperbola.shifted_hyperbola_box_card_le`
