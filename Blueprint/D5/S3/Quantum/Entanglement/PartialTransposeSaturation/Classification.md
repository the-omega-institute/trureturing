# Partial transpose saturation

## Abstract

The equality condition for Schmidt rank two in arbitrary rectangular dimensions

Wang and Chen ask for the equality condition in their partial transpose rank bound for Schmidt rank two in arbitrary dimensions. Write X as A1 tensor B1 plus A2 tensor B2, where both coefficient pairs are linearly independent over the complex numbers. Transpose the A coefficients to form XGamma. Let hA and vA be the horizontal and vertical concatenation ranks of A1 and A2, and define hB and vB in the same way.

**Remark 1.1 (Known saturation conditions in special dimensions).**

Lean statement: `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Sufficiency.partialTranspose`

*Formalization.* `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Sufficiency.partialTranspose` (`✓ std3`).

*Citation.* N. Wang; L. Chen (2025). *Equality condition for a matrix inequality by partial transpose*. DOI: [10.1142/S1230161226500071](https://doi.org/10.1142/S1230161226500071). URL: <https://arxiv.org/abs/2508.18644v1>.

*Commentary.*

Wang and Chen already prove the saturation conditions when the first-factor coefficient matrices are column vectors, row vectors, or two-by-two matrices, in Sections IV and V near Theorem 12, Lemma 14, and Theorem 17, as summarized in the opening sentence of Section VI. At Schmidt rank two and under the two coefficient-pair linear independence hypotheses, these are known special cases of the terminal classification below. The general classification in arbitrary rectangular dimensions is FromRepo.

**Theorem 1.2 (The exact saturation criterion).**

Lean statement: `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Classification.result`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Classification.result` (`✓ std3`). ∎

*Resolves.* `Problems/wang-chen-2025-schmidt-rank-two-partial-transpose-saturation` (proved) by `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Classification.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"wang-chen-2025-schmidt-rank-two-partial-transpose-saturation","declaration_gid":"D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Classification.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* N. Wang; L. Chen (2025). *Equality condition for a matrix inequality by partial transpose*. DOI: [10.1142/S1230161226500071](https://doi.org/10.1142/S1230161226500071). URL: <https://arxiv.org/abs/2508.18644v1>.

*Commentary.*

For all four finite rectangular dimensions, rank XGamma equals twice rank X if and only if either vA equals twice hA and vB equals twice hB, or hA equals twice vA and hB equals twice vB. The coefficient matrices use finite natural index types. The only hypotheses are linear independence of each coefficient pair. The first alternative gives rank X equal to hA times hB; the second gives rank X equal to vA times vB.

A shortest polynomial kernel chain gives separating dual coordinates and two commuting projections. Their kernels split off an actual complementary pair. Repeated extraction, followed by the dual construction, leaves a square pair with a nonzero determinant polynomial. A scalar combination is therefore invertible. Reversal of Jordan chains makes this regular pair equivalent to its transpose, so its tensor rank is unchanged.

For positive singular indices r and s, equal orientations contribute ranks rs and rs plus min(r,s); opposite orientations contribute these in reverse order. Rank adds over the actual projection splittings. Every block has nonnegative defect, and equality forces every defect to vanish. Independence excludes nonzero regular pieces. Each remaining positive singular index is one, and all orientations agree across the two coefficient pairs. Their horizontal and vertical concatenation ranks give the two alternatives. Conversely, independent prescription of the two outputs proves the sufficient rank formulas directly.

Classical Kronecker matrix pencil decomposition is a precedent for the singular and regular pieces. The shortest chain splitting is constructed within the proof. No assertion is made for Schmidt rank at least three or for a complete classification of equality of the two unscaled ranks.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Classification.result`
- Truth anchor: `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Sufficiency.partialTranspose`
- Dependency: [D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Decomposition](Decomposition.md)
- Dependency: [D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Regularity](Regularity.md)
- Dependency: [D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Singular](Singular.md)
