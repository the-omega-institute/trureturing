# Displacement count for short middle slopes

## Abstract

A finite count for prime-square Pascadi word lifts in middle-slope coordinates.

**Theorem 1.1 (Bound for prime-square word lifts).**

Lean statement: `D5/S3/Arith/CharacterSums/PascadiShortSlopeDisplacement.short_slope_word_count`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/PascadiShortSlopeDisplacement.short_slope_word_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Alexandru Pascadi (2026). *Non-abelian amplification and bilinear forms with Kloosterman sums*. DOI: [10.1007/s00039-026-00746-0](https://doi.org/10.1007/s00039-026-00746-0). URL: <https://arxiv.org/abs/2511.08445v2>.

*Commentary.*

For each residue triple b in the cube of a finite set S, take a finite set of lift triples k. Their integer representatives are first coordinates of the form u*b_i+p*e*k_i with u and e units modulo p. Assume they solve the Pascadi word modulo p squared and their nonzero residue differences belong to a finite set D.

The number of lifts is at most |S| cubed plus 3 times |D| times |S| squared. Subtracting the integer words and dividing by p gives a linear equation on a displacement. The lower word turns that equation into a cubic polynomial in b. Each nonzero displacement gives a nonzero polynomial, so Schwartz–Zippel bounds its base triples. Each nonempty fibre contributes one base lift and injects its other lifts into the allowed displacements.

## References

- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiShortSlopeDisplacement.short_slope_word_count`
