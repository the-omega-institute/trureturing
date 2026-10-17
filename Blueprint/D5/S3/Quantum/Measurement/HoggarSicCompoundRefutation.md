# A SIC-compound from eight Hoggar SICs

## Abstract

Eight orthonormal fiducials generate a SIC-compound in complex dimension eight under the three-qubit Pauli action.

Fin 8 indexes the integers 0 through 7, regarded as three-bit strings. The 64 Pauli labels are pairs in Fin 8 × Fin 8; for j = (x, z), j₁ = x and j₂ = z. The operation xor is bitwise addition modulo two, written ⊕, and val takes the integer represented by a bit string. The Hermitian inner product conjugates its first argument: ⟨u, v⟩ = ∑ over b in Fin 8 of conjugate(u(b)) v(b). The symbol δ with indices j and l means 1 if j = l and 0 otherwise. Thus squared absolute values below are real, while inner products and vector entries are complex.

**Definition 1.1 (The three-qubit Pauli action).**

$$\forall (x: \operatorname{Fin}\left(8\right)), (\forall (z: \operatorname{Fin}\left(8\right)), (\forall (u: \operatorname{Fin}\left(8\right) \to \mathbb{C}), (\forall (b: \operatorname{Fin}\left(8\right)), (\operatorname{pauli}\left(x, z, u, b\right) = (-1)^{\left((\left\lfloor\frac{\operatorname{val}\left(z\right)}{1}\right\rfloor \bmod 2) \cdot (\left\lfloor\frac{\operatorname{val}\left(\operatorname{xor}\left(b, x\right)\right)}{1}\right\rfloor \bmod 2) + (\left\lfloor\frac{\operatorname{val}\left(z\right)}{2}\right\rfloor \bmod 2) \cdot (\left\lfloor\frac{\operatorname{val}\left(\operatorname{xor}\left(b, x\right)\right)}{2}\right\rfloor \bmod 2) + (\left\lfloor\frac{\operatorname{val}\left(z\right)}{4}\right\rfloor \bmod 2) \cdot (\left\lfloor\frac{\operatorname{val}\left(\operatorname{xor}\left(b, x\right)\right)}{4}\right\rfloor \bmod 2)\right) \bmod 2} \cdot u\left(\operatorname{xor}\left(b, x\right)\right)))))$$

*Formalization.* `D5/S3/Quantum/Measurement/HoggarSicCompoundRefutation.pauli` (`✓ std3`).

*Citation.* Armin Tavakoli; Ingemar Bengtsson; Nicolas Gisin; Joseph M. Renes (2020). *Compounds of symmetric informationally complete measurements and their application in quantum key distribution*. DOI: [10.1103/PhysRevResearch.2.043122](https://doi.org/10.1103/PhysRevResearch.2.043122). URL: <https://arxiv.org/abs/2007.01007v1>.

*Commentary.*

For bit strings z and a, z·a is the parity of the sum of the three products of corresponding bits. The displayed exponent writes that parity using integer remainders and floors. Thus (pauli x z u)(b) = (−1)^{z·(b ⊕ x)} u(b ⊕ x): the shift is applied before the sign. This is the three-qubit Pauli action used for the exceptional dimension-eight SICs in references [3], [51] and [52] of the source.

**Definition 1.2 (The SIC overlap condition in dimension eight).**

$$\forall (phi: \operatorname{Fin}\left(8\right) \times \operatorname{Fin}\left(8\right) \to \left(\operatorname{Fin}\left(8\right) \to \mathbb{C}\right)), (\operatorname{IsSIC}\left(phi\right) \Leftrightarrow (\forall (j: \operatorname{Fin}\left(8\right) \times \operatorname{Fin}\left(8\right)), (\forall (l: \operatorname{Fin}\left(8\right) \times \operatorname{Fin}\left(8\right)), (\left|\langle phi\left(j\right), phi\left(l\right) \rangle\right|^{2} = \frac{8 \cdot \delta_{j,l} + 1}{9}))))$$

*Formalization.* `D5/S3/Quantum/Measurement/HoggarSicCompoundRefutation.IsSIC` (`✓ std3`).

*Citation.* Armin Tavakoli; Ingemar Bengtsson; Nicolas Gisin; Joseph M. Renes (2020). *Compounds of symmetric informationally complete measurements and their application in quantum key distribution*. DOI: [10.1103/PhysRevResearch.2.043122](https://doi.org/10.1103/PhysRevResearch.2.043122). URL: <https://arxiv.org/abs/2007.01007v1>.

*Commentary.*

Equation (1), with d = 8, requires |⟨φ_j, φ_l⟩|² = (8δ_{jl} + 1)/9 for every pair of the 64 labels. The diagonal equations give unit vectors, and every off-diagonal squared overlap is 1/9.

**Definition 1.3 (The negative answer to the exceptional-SIC question).**

$$\operatorname{claim} \Leftrightarrow (\neg (\exists (f: \operatorname{Fin}\left(8\right) \to \left(\operatorname{Fin}\left(8\right) \to \mathbb{C}\right)), ((\forall (k: \operatorname{Fin}\left(8\right)), (\operatorname{IsSIC}\left(\lambda (j: \operatorname{Fin}\left(8\right) \times \operatorname{Fin}\left(8\right)) \mapsto \operatorname{pauli}\left(j_{1}, j_{2}, f\left(k\right)\right)\right))) \land (\forall (j: \operatorname{Fin}\left(8\right) \times \operatorname{Fin}\left(8\right)), (\forall (k: \operatorname{Fin}\left(8\right)), (\forall (l: \operatorname{Fin}\left(8\right)), (\langle \operatorname{pauli}\left(j_{1}, j_{2}, f\left(k\right)\right), \operatorname{pauli}\left(j_{1}, j_{2}, f\left(l\right)\right) \rangle = \delta_{k,l})))))))$$

*Formalization.* `D5/S3/Quantum/Measurement/HoggarSicCompoundRefutation.claim` (`✓ std3`).

*Citation.* Armin Tavakoli; Ingemar Bengtsson; Nicolas Gisin; Joseph M. Renes (2020). *Compounds of symmetric informationally complete measurements and their application in quantum key distribution*. DOI: [10.1103/PhysRevResearch.2.043122](https://doi.org/10.1103/PhysRevResearch.2.043122). URL: <https://arxiv.org/abs/2007.01007v1>.

*Commentary.*

The claim says that there are no eight vectors whose Pauli orbits are SICs and whose images under each Pauli operator form an orthonormal basis. Such vectors would give 512 states ψ_{j,k} = pauli(j.1, j.2, f(k)), with eight SICs as in property I and 64 orthonormal bases as in property II. They would therefore form a SIC-compound built from Hoggar SICs, the exceptional SICs of dimension eight. The paragraph on existence in dimensions 5, 6, 7 and 8 leaves this exceptional case open; the claim is its negative answer.

**Theorem 1.4 (Eight orthogonal Hoggar fiducials give a compound).**

$$\neg (\operatorname{claim})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/HoggarSicCompoundRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/tavakoli-bengtsson-gisin-renes-2020-hoggar-sic-compound-refutation` (refuted) by `D5/S3/Quantum/Measurement/HoggarSicCompoundRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"tavakoli-bengtsson-gisin-renes-2020-hoggar-sic-compound-refutation","declaration_gid":"D5/S3/Quantum/Measurement/HoggarSicCompoundRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Armin Tavakoli; Ingemar Bengtsson; Nicolas Gisin; Joseph M. Renes (2020). *Compounds of symmetric informationally complete measurements and their application in quantum key distribution*. DOI: [10.1103/PhysRevResearch.2.043122](https://doi.org/10.1103/PhysRevResearch.2.043122). URL: <https://arxiv.org/abs/2007.01007v1>.

*Commentary.*

Choose the following eight vectors with Gaussian-integer entries, with i² = −1:

w₀ = (−1 + 2i, 1, 1, 1, 1, 1, 1, 1).

w₁ = (1, i, i, i, 1 − i, 0, 0, 0).

w₂ = (1, i, 1 − i, 0, i, i, 0, 0).

w₃ = (1, 1 − i, i, 0, i, 0, i, 0).

w₄ = (1, −1, −1, 1, −1, 1, 1, 1 + 2i).

w₅ = (0, 0, 0, 1 + i, i, −i, −i, −1).

w₆ = (0, 0, 1, −1, 0, 1 − i, −1, i).

w₇ = (0, 1, 0, −1, 0, −1, 1 − i, i).

Set (r₀, …, r₇) = (12, 6, 6, 6, 12, 6, 6, 6) and fₖ = wₖ/√rₖ. The Gram matrix of the eight vectors is diag(12, 6, 6, 6, 12, 6, 6, 6): for all k and l, ⟨wₖ, wₗ⟩ = rₖ if k = l and 0 otherwise. Consequently the normalized vectors f₀, …, f₇ are orthonormal. Every Pauli operator preserves inner products, so for each Pauli label the eight images of these vectors form an orthonormal basis.

For every k and every non-identity Pauli label (x, z) ≠ (0, 0), |⟨wₖ, pauli(x, z, wₖ)⟩|² = rₖ²/9: the value is 16 for k = 0 or 4 and 4 for every other k. At (x, z) = (0, 0) the value is rₖ². After normalization, these squared self-overlaps are respectively 1/9 and 1.

For all three-bit strings x, z, y and t and all complex vectors u, pauli(x, z, pauli(y, t, u)) = (−1)^{z·y} pauli(x ⊕ y, z ⊕ t, u). Together with preservation of inner products, this multiplication law gives |⟨pauli(x, z, u), pauli(y, t, u)⟩|² = |⟨u, pauli(x ⊕ y, z ⊕ t, u)⟩|². It reduces every pair overlap in each orbit to a self-overlap. Each orbit of fₖ therefore satisfies the SIC equations. The 512 states form a SIC-compound and answer the exceptional dimension-eight question positively.

## References

- Truth anchor: `D5/S3/Quantum/Measurement/HoggarSicCompoundRefutation.IsSIC`
- Truth anchor: `D5/S3/Quantum/Measurement/HoggarSicCompoundRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Measurement/HoggarSicCompoundRefutation.pauli`
- Truth anchor: `D5/S3/Quantum/Measurement/HoggarSicCompoundRefutation.result`
- Dependency: [D5/S3/Quantum/Measurement/HoggarSicSumNegativity](HoggarSicSumNegativity.md)
