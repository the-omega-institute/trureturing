# The original Bajnok–Beatty Conjecture 4.1

## Abstract

The original four-clause classification holds for every positive k and s.

**Theorem 1.1 (Counting through a square).**

Lean statement: `D5/S3/FiniteGroups/BajnokBeattyAllRegimes.rectangle_index_le`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/BajnokBeattyAllRegimes.rectangle_index_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* B. Bajnok and W. K. Beatty (2024). *On the Diameter of Undirected Cayley Graphs of Finite Abelian Groups*. URL: <https://arxiv.org/abs/2406.04045v1>.

*Commentary.*

If every element of the integer plane is congruent modulo a sublattice L to a point of {0, …, n − 1}², then the index of L is at most n².

**Theorem 1.2 (The square lemma at odd radius).**

Lean statement: `D5/S3/FiniteGroups/BajnokBeattyAllRegimes.even_torsor_cover`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/BajnokBeattyAllRegimes.even_torsor_cover` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* B. Bajnok and W. K. Beatty (2024). *On the Diameter of Undirected Cayley Graphs of Finite Abelian Groups*. URL: <https://arxiv.org/abs/2406.04045v1>.

*Commentary.*

If the coefficient map f covers ZMod 2 × ZMod (2k) from the diamond |x| + |y| ≤ 2t + 1, then every coset of M = T⁻¹ ker f, with T(u, v) = (u + v, u − v), has a representative in {0, …, 2t}². The difference from the chosen diamond point has even coordinate sum and difference, so halving gives a point of [−t, t]², shifted by t.

**Theorem 1.3 (The square lemma at every positive radius).**

Lean statement: `D5/S3/FiniteGroups/BajnokBeattyAllRegimes.square_cover`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/BajnokBeattyAllRegimes.square_cover` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* B. Bajnok and W. K. Beatty (2024). *On the Diameter of Undirected Cayley Graphs of Finite Abelian Groups*. URL: <https://arxiv.org/abs/2406.04045v1>.

*Commentary.*

If f maps the diamond |x| + |y| ≤ s onto ZMod 2 × ZMod (2k), then every coset of M has a representative in {0, …, s − 1}². Even radii use the existing even-radius cover and odd radii the odd-radius cover above.

**Theorem 1.4 (The order bound).**

Lean statement: `D5/S3/FiniteGroups/BajnokBeattyAllRegimes.hom_order_le`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/BajnokBeattyAllRegimes.hom_order_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* B. Bajnok and W. K. Beatty (2024). *On the Diameter of Undirected Cayley Graphs of Finite Abelian Groups*. URL: <https://arxiv.org/abs/2406.04045v1>.

*Commentary.*

Under the covering hypothesis, 2k ≤ s²: the index of M is 2k and the square has s² points.

**Theorem 1.5 (Two-generator signed radius: all regimes).**

Lean statement: `D5/S3/FiniteGroups/BajnokBeattyAllRegimes.result`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/BajnokBeattyAllRegimes.result` (`✓ std3`). ∎

*Resolves.* `Problems/bajnok-beatty-original-conjecture-4-1` (proved) by `D5/S3/FiniteGroups/BajnokBeattyAllRegimes.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"bajnok-beatty-original-conjecture-4-1","declaration_gid":"D5/S3/FiniteGroups/BajnokBeattyAllRegimes.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* B. Bajnok and W. K. Beatty (2024). *On the Diameter of Undirected Cayley Graphs of Finite Abelian Groups*. URL: <https://arxiv.org/abs/2406.04045v1>.

*Commentary.*

For positive integers k and s, the group ZMod 2 × ZMod (2k) admits two distinct elements whose signed integer combinations of coefficient absolute-value sum at most s cover every group element exactly when at least one of these four clauses holds: s is odd and 2k ≤ s² − 1; s is even and 2k ≤ s² − s; s is congruent to zero modulo four, k is even, and s² − s < 2k ≤ s²; or s is congruent to two modulo four, k is congruent to two modulo four, and s² − s < 2k ≤ s². The quantifiers allow arbitrary generating pairs; there is no assumption on their first coordinates. The doubled inequalities express the rational bounds in the original statement without integer division.

The order bound and the odd and even low regimes are the known Theorems 4.2–4.4 of Bajnok and Beatty, arXiv:2406.04045v1. Their formal proofs use exact square representatives of the relation quotient, integer-cylinder covers with consecutive coefficients, and balanced modular lifts. They carry no claim of new mathematics.

In the remaining even top strip, the proof uses the existing arbitrary-pair necessity theorem and the existing uniform sufficient skew-lattice family. Necessity forces k to be even and, when s is congruent to two modulo four, k to be congruent to two modulo four. Sufficiency sets t = s/2 and j = t² − k/2 and applies the proved family. The boundary t = 1 is included, and every positive k is excluded when s = 1.

This is a formal result for the literal original arXiv v1 conjecture. No claim about mathematical priority or the status of later publications follows; later versions are outside the source comparison.

## References

- Truth anchor: `D5/S3/FiniteGroups/BajnokBeattyAllRegimes.even_torsor_cover`
- Truth anchor: `D5/S3/FiniteGroups/BajnokBeattyAllRegimes.hom_order_le`
- Truth anchor: `D5/S3/FiniteGroups/BajnokBeattyAllRegimes.rectangle_index_le`
- Truth anchor: `D5/S3/FiniteGroups/BajnokBeattyAllRegimes.result`
- Truth anchor: `D5/S3/FiniteGroups/BajnokBeattyAllRegimes.square_cover`
- Dependency: [D5/S3/FiniteGroups/BajnokBeattyCayleyNecessity](BajnokBeattyCayleyNecessity.md)
- Dependency: [D5/S3/FiniteGroups/BajnokBeattyCayleySufficiency](BajnokBeattyCayleySufficiency.md)
