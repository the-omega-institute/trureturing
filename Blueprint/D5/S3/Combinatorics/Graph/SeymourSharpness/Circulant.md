# Short-arc modular circulants

## Abstract

Short-arc modular circulants

For a positive modulus n, let t be the integer part of (n-1)/2. The relation on ZMod n has an arc from x to y exactly when the residue y-x has value between one and t. The inequality 2t<n prevents wraparound in a sum of two allowed offsets.

**Theorem 1.1 (Orientation of the circulant).**

Lean statement: `D5/S3/Combinatorics/Graph/SeymourSharpness/Circulant.circulant_asymm`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/SeymourSharpness/Circulant.circulant_asymm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Arpan Sadhukhan; Sagnik Sen (2026). *Locating a Seymour vertex in oriented graphs having minimum outdegree at most 7*. URL: <https://arxiv.org/abs/2606.30588v2>.

*Commentary.*

The sum of two opposite positive allowed offsets would be a strictly positive integer below n representing zero modulo n, which is impossible.

**Theorem 1.2 (The interval of exact second offsets).**

Lean statement: `D5/S3/Combinatorics/Graph/SeymourSharpness/Circulant.circulant_exact_second`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/SeymourSharpness/Circulant.circulant_exact_second` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Arpan Sadhukhan; Sagnik Sen (2026). *Locating a Seymour vertex in oriented graphs having minimum outdegree at most 7*. URL: <https://arxiv.org/abs/2606.30588v2>.

*Commentary.*

The literal exact second neighbors have offsets strictly greater than t and at most 2t. For an offset in this interval, the intermediate vertex with offset t supplies the two-edge witness. This includes moduli one and two, where both intervals of neighbors are empty.

**Theorem 1.3 (Equal first and exact second degrees).**

Lean statement: `D5/S3/Combinatorics/Graph/SeymourSharpness/Circulant.circulant_degrees`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/SeymourSharpness/Circulant.circulant_degrees` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Arpan Sadhukhan; Sagnik Sen (2026). *Locating a Seymour vertex in oriented graphs having minimum outdegree at most 7*. URL: <https://arxiv.org/abs/2606.30588v2>.

*Commentary.*

Translation and the residue-value bijection identify the first neighborhood with the integer interval (0,t] and the exact second neighborhood with (t,2t]. Both cardinalities are t.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/SeymourSharpness/Circulant.circulant_asymm`
- Truth anchor: `D5/S3/Combinatorics/Graph/SeymourSharpness/Circulant.circulant_degrees`
- Truth anchor: `D5/S3/Combinatorics/Graph/SeymourSharpness/Circulant.circulant_exact_second`
- Dependency: [D5/S3/Combinatorics/Graph/SeymourSharpness/Neighborhoods](Neighborhoods.md)
