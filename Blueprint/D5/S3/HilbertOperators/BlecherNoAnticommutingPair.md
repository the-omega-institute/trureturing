# A symmetric operator algebra without a nonzero anticommuting product

## Abstract

A noncommutative symmetric operator algebra in M₁₆(ℂ) excludes nonzero anticommuting products.

**Definition 1.1 (The necessity of a nonzero anticommuting product).**

$$\left(\operatorname{D5.S3.HilbertOperators.BlecherNoAnticommutingPair.claim}\right) \Leftrightarrow \left(\forall \left(A: \operatorname{Submodule}\left(\mathbb{C}, \operatorname{Matrix}\left(\operatorname{Fin}\left(16\right), \operatorname{Fin}\left(16\right), \mathbb{C}\right)\right)\right), \left(\left(\forall \left(x: \operatorname{Matrix}\left(\operatorname{Fin}\left(16\right), \operatorname{Fin}\left(16\right), \mathbb{C}\right)\right), \left(\left(x \in A\right) \to \left(\forall \left(y: \operatorname{Matrix}\left(\operatorname{Fin}\left(16\right), \operatorname{Fin}\left(16\right), \mathbb{C}\right)\right), \left(\left(y \in A\right) \to \left(x \cdot y \in A\right)\right)\right)\right)\right) \to \left(\left(\exists \left(x: \operatorname{Matrix}\left(\operatorname{Fin}\left(16\right), \operatorname{Fin}\left(16\right), \mathbb{C}\right)\right), \left(\left(x \in A\right) \land \left(\exists \left(y: \operatorname{Matrix}\left(\operatorname{Fin}\left(16\right), \operatorname{Fin}\left(16\right), \mathbb{C}\right)\right), \left(\left(y \in A\right) \land \left(x \cdot y \ne y \cdot x\right)\right)\right)\right)\right) \to \left(\left(\forall \left(k: \mathbb{N}\right), \left(\forall \left(x: \left(\operatorname{Fin}\left(k\right)\right) \to \left(\left(\operatorname{Fin}\left(k\right)\right) \to \left(\operatorname{Matrix}\left(\operatorname{Fin}\left(16\right), \operatorname{Fin}\left(16\right), \mathbb{C}\right)\right)\right)\right), \left(\left(\forall \left(i: \operatorname{Fin}\left(k\right)\right), \left(\forall \left(j: \operatorname{Fin}\left(k\right)\right), \left(x\left(i, j\right) \in A\right)\right)\right) \to \left(\left\lVert \operatorname{Matrix.comp}\left(\operatorname{Fin}\left(k\right), \operatorname{Fin}\left(k\right), \operatorname{Fin}\left(16\right), \operatorname{Fin}\left(16\right), \mathbb{C}, \left(\lambda \left(i: \operatorname{Fin}\left(k\right)\right) \mapsto \left(\left(\lambda \left(j: \operatorname{Fin}\left(k\right)\right) \mapsto \left(\operatorname{Matrix.transpose}\left(x\left(i, j\right)\right)\right)\right)\right)\right)\right) \right\rVert = \left\lVert \operatorname{Matrix.comp}\left(\operatorname{Fin}\left(k\right), \operatorname{Fin}\left(k\right), \operatorname{Fin}\left(16\right), \operatorname{Fin}\left(16\right), \mathbb{C}, x\right) \right\rVert\right)\right)\right)\right) \to \left(\exists \left(x: \operatorname{Matrix}\left(\operatorname{Fin}\left(16\right), \operatorname{Fin}\left(16\right), \mathbb{C}\right)\right), \left(\left(x \in A\right) \land \left(\exists \left(y: \operatorname{Matrix}\left(\operatorname{Fin}\left(16\right), \operatorname{Fin}\left(16\right), \mathbb{C}\right)\right), \left(\left(y \in A\right) \land \left(\left(x \cdot y = -\left(y \cdot x\right)\right) \land \left(x \cdot y \ne 0\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/HilbertOperators/BlecherNoAnticommutingPair.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* David P. Blecher (2025). *Commutativity of operator algebras*. URL: <https://arxiv.org/html/2509.17673v2#S5.Thmtheorem5>.

*Commentary.*

The proposed necessity applies to a complex subspace of M₁₆(ℂ) that is closed under matrix multiplication, has a noncommuting pair, and retains every Euclidean operator norm under entrywise transpose on matrix amplifications. The proposed pair has xy = −yx and xy ≠ 0. This is the pair condition in Blecher, Example 5.5.

**Theorem 1.2 (A faithful sixteen-dimensional matrix representation gives a counterexample).**

$$\neg \left(\forall \left(A: \operatorname{Submodule}\left(\mathbb{C}, \operatorname{Matrix}\left(\operatorname{Fin}\left(16\right), \operatorname{Fin}\left(16\right), \mathbb{C}\right)\right)\right), \left(\left(\forall \left(x: \operatorname{Matrix}\left(\operatorname{Fin}\left(16\right), \operatorname{Fin}\left(16\right), \mathbb{C}\right)\right), \left(\left(x \in A\right) \to \left(\forall \left(y: \operatorname{Matrix}\left(\operatorname{Fin}\left(16\right), \operatorname{Fin}\left(16\right), \mathbb{C}\right)\right), \left(\left(y \in A\right) \to \left(x \cdot y \in A\right)\right)\right)\right)\right) \to \left(\left(\exists \left(x: \operatorname{Matrix}\left(\operatorname{Fin}\left(16\right), \operatorname{Fin}\left(16\right), \mathbb{C}\right)\right), \left(\left(x \in A\right) \land \left(\exists \left(y: \operatorname{Matrix}\left(\operatorname{Fin}\left(16\right), \operatorname{Fin}\left(16\right), \mathbb{C}\right)\right), \left(\left(y \in A\right) \land \left(x \cdot y \ne y \cdot x\right)\right)\right)\right)\right) \to \left(\left(\forall \left(k: \mathbb{N}\right), \left(\forall \left(x: \left(\operatorname{Fin}\left(k\right)\right) \to \left(\left(\operatorname{Fin}\left(k\right)\right) \to \left(\operatorname{Matrix}\left(\operatorname{Fin}\left(16\right), \operatorname{Fin}\left(16\right), \mathbb{C}\right)\right)\right)\right), \left(\left(\forall \left(i: \operatorname{Fin}\left(k\right)\right), \left(\forall \left(j: \operatorname{Fin}\left(k\right)\right), \left(x\left(i, j\right) \in A\right)\right)\right) \to \left(\left\lVert \operatorname{Matrix.comp}\left(\operatorname{Fin}\left(k\right), \operatorname{Fin}\left(k\right), \operatorname{Fin}\left(16\right), \operatorname{Fin}\left(16\right), \mathbb{C}, \left(\lambda \left(i: \operatorname{Fin}\left(k\right)\right) \mapsto \left(\left(\lambda \left(j: \operatorname{Fin}\left(k\right)\right) \mapsto \left(\operatorname{Matrix.transpose}\left(x\left(i, j\right)\right)\right)\right)\right)\right)\right) \right\rVert = \left\lVert \operatorname{Matrix.comp}\left(\operatorname{Fin}\left(k\right), \operatorname{Fin}\left(k\right), \operatorname{Fin}\left(16\right), \operatorname{Fin}\left(16\right), \mathbb{C}, x\right) \right\rVert\right)\right)\right)\right) \to \left(\exists \left(x: \operatorname{Matrix}\left(\operatorname{Fin}\left(16\right), \operatorname{Fin}\left(16\right), \mathbb{C}\right)\right), \left(\left(x \in A\right) \land \left(\exists \left(y: \operatorname{Matrix}\left(\operatorname{Fin}\left(16\right), \operatorname{Fin}\left(16\right), \mathbb{C}\right)\right), \left(\left(y \in A\right) \land \left(\left(x \cdot y = -\left(y \cdot x\right)\right) \land \left(x \cdot y \ne 0\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/HilbertOperators/BlecherNoAnticommutingPair.result` (`✓ std3`). ∎

*Resolves.* `Problems/blecher-2025-example-5-5-no-anticommuting-pair` (refuted) by `D5/S3/HilbertOperators/BlecherNoAnticommutingPair.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"blecher-2025-example-5-5-no-anticommuting-pair","declaration_gid":"D5/S3/HilbertOperators/BlecherNoAnticommutingPair.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* David P. Blecher (2025). *Commutativity of operator algebras*. URL: <https://arxiv.org/html/2509.17673v2#S5.Thmtheorem5>.

*Commentary.*

For a complex row r of length two and a two-by-two matrix Z, take a direct sum of four upper triangular blocks. In each block the outer slots have size one and the middle slot has size two. The three upper entries are r, the entry pairing of J with Z, and J times the transpose of r. The probes J are the identity, a single diagonal sign change, the coordinate swap and the signed coordinate swap with entries (0, −1; 1, 0).

The product in each block has only its upper-right entry, the entry pairing of J with the outer product of the two rows. The top-middle block recovers r. Adding and subtracting the first two probe readings recovers the diagonal of Z. Adding and subtracting the last two recovers its off-diagonal entries. The resulting complex-linear map is injective and multiplicative. The two standard basis rows give distinct outer products in the two orders.

If the two outer products are negatives of each other, choose a nonzero coordinate of the first row if it has one. The diagonal equation forces the corresponding coordinate of the second row to be zero. The other equations with that same row index then force the whole second row to be zero. Their product in the image is therefore zero.

For each probe, use the unitary that exchanges the outer slots and acts by J on the middle slot. Multiplying the transpose of a block by this unitary on both sides recovers the original block. The direct sum of these unitaries gives the same identity on the image. At every matrix level its copies form a block diagonal unitary. Unitary multiplication on both sides preserves the assembled Euclidean operator norm. Transpose also reverses multiplication, so it realizes the reversed algebra completely isometrically.

For each m ≥ 2 the same construction uses m² probes. There is one identity probe, m − 1 diagonal sign changes, and one unsigned swap and one signed swap for each unordered pair of distinct coordinates. Subtracting the signed swap reading from the unsigned swap reading recovers twice one off-diagonal entry. Comparing the unsigned swap reading to the identity reading recovers the other using the known diagonal. The representation is faithful in complex matrices of size m²(m + 2), and the same argument proves noncommutativity, the zero-product implication and all amplification norm equalities.

## References

- Truth anchor: `D5/S3/HilbertOperators/BlecherNoAnticommutingPair.claim`
- Truth anchor: `D5/S3/HilbertOperators/BlecherNoAnticommutingPair.result`
