# An obstruction to the odd-order Hadamardness minimum

## Abstract

The proposed odd-order minimum of Hadamardness cannot be attained in order nine.

**Definition 1.1 (Integer sign matrices).**

$$\forall (d: \mathbb{N}), (\forall (c: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{Z}\right)), ((\operatorname{D5.S3.Quantum.Matrix.SinghNechitaOddHadamardnessRefutation.IsSignMatrix}\left(c\right)) \Leftrightarrow (\forall (i: \operatorname{Fin}\left(d\right)), (\forall (j: \operatorname{Fin}\left(d\right)), ((c\left(i, j\right) = (1: \mathbb{Z})) \lor (c\left(i, j\right) = -(1: \mathbb{Z})))))))$$

*Formalization.* `D5/S3/Quantum/Matrix/SinghNechitaOddHadamardnessRefutation.IsSignMatrix` (`✓ std3`).

*Citation.* Satvik Singh; Ion Nechita (2022). *Diagonal unitary and orthogonal symmetries in quantum theory II: Evolution operators*. DOI: [10.1088/1751-8121/ac7017](https://doi.org/10.1088/1751-8121/ac7017). URL: <https://arxiv.org/abs/2112.11123v1>.

*Commentary.*

A sign matrix is a square integer matrix whose entries are all one or minus one. The indices i and j range over Fin d. This is the sign-matrix domain in line 779 of the source, with the real signs represented exactly as integers.

**Definition 1.2 (The trace of the squared row Gram matrix).**

$$\forall (d: \mathbb{N}), (\forall (c: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{Z}\right)), ((\operatorname{D5.S3.Quantum.Matrix.SinghNechitaOddHadamardnessRefutation.hadamardness}\left(c\right): \mathbb{Z}) = \operatorname{Matrix.trace}\left(((c) \cdot (\operatorname{Matrix.transpose}\left(c\right))) \cdot ((c) \cdot (\operatorname{Matrix.transpose}\left(c\right)))\right)))$$

*Formalization.* `D5/S3/Quantum/Matrix/SinghNechitaOddHadamardnessRefutation.hadamardness` (`✓ std3`).

*Citation.* Satvik Singh; Ion Nechita (2022). *Diagonal unitary and orthogonal symmetries in quantum theory II: Evolution operators*. DOI: [10.1088/1751-8121/ac7017](https://doi.org/10.1088/1751-8121/ac7017). URL: <https://arxiv.org/abs/2112.11123v1>.

*Commentary.*

Hadamardness is the trace of the square of the row Gram matrix c cᵀ. The definition is meaningful for every square integer matrix c, without a sign hypothesis. For sign matrices it is the integer-valued form of the measure in equation eq:Hada_measure, lines 780–783 of the source. Real sign matrices have conjugate transpose equal to transpose, so the integer trace has the same value as the real trace.

**Definition 1.3 (The proposed minimum in every odd order).**

$$(\operatorname{D5.S3.Quantum.Matrix.SinghNechitaOddHadamardnessRefutation.claim}) \Leftrightarrow (\forall (d: \mathbb{N}), ((\operatorname{Odd}\left(d\right)) \to (\exists (c: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{Z}\right)), ((\operatorname{D5.S3.Quantum.Matrix.SinghNechitaOddHadamardnessRefutation.IsSignMatrix}\left(c\right)) \land ((\operatorname{D5.S3.Quantum.Matrix.SinghNechitaOddHadamardnessRefutation.hadamardness}\left(c\right) = (\operatorname{Nat.cast}\left((d^{3} + (d) \cdot (d - 1): \mathbb{N})\right): \mathbb{Z})) \land (\forall (b: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{Z}\right)), ((\operatorname{D5.S3.Quantum.Matrix.SinghNechitaOddHadamardnessRefutation.IsSignMatrix}\left(b\right)) \to ((\operatorname{Nat.cast}\left((d^{3} + (d) \cdot (d - 1): \mathbb{N})\right): \mathbb{Z}) \le \operatorname{D5.S3.Quantum.Matrix.SinghNechitaOddHadamardnessRefutation.hadamardness}\left(b\right)))))))))$$

*Formalization.* `D5/S3/Quantum/Matrix/SinghNechitaOddHadamardnessRefutation.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Satvik Singh; Ion Nechita (2022). *Diagonal unitary and orthogonal symmetries in quantum theory II: Evolution operators*. DOI: [10.1088/1751-8121/ac7017](https://doi.org/10.1088/1751-8121/ac7017). URL: <https://arxiv.org/abs/2112.11123v1>.

*Commentary.*

For every odd natural d, some sign matrix c attains d cubed plus d times (d minus one), and every sign matrix b has Hadamardness at least that value. Together these clauses say that the value is the minimum over sign matrices. They express the conjecture in line 848 of the source. The entire expression d^3 + d*(d−1) is evaluated in the natural numbers, including natural subtraction, and then cast to the integers in both the equality and the lower bound.

**Theorem 1.4 (Nonattainment in order nine).**

$$\neg (\operatorname{D5.S3.Quantum.Matrix.SinghNechitaOddHadamardnessRefutation.claim})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/SinghNechitaOddHadamardnessRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/singh-nechita-2022-odd-hadamardness` (refuted) by `D5/S3/Quantum/Matrix/SinghNechitaOddHadamardnessRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"singh-nechita-2022-odd-hadamardness","declaration_gid":"D5/S3/Quantum/Matrix/SinghNechitaOddHadamardnessRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Satvik Singh; Ion Nechita (2022). *Diagonal unitary and orthogonal symmetries in quantum theory II: Evolution operators*. DOI: [10.1088/1751-8121/ac7017](https://doi.org/10.1088/1751-8121/ac7017). URL: <https://arxiv.org/abs/2112.11123v1>.

*Commentary.*

For a sign matrix c of order nine, put G = c cᵀ. Symmetry of G gives trace(GG) = Σᵢ Σⱼ Gᵢⱼ², by expressing the trace as the dot product of the vectorized Gram matrix with itself. Each diagonal entry Gᵢᵢ is nine, since it is the sum of nine squared signs. Every entry Gᵢⱼ is one modulo two, since each of its nine summands is a product of two signs.

Suppose the Hadamardness of c is 801. Each diagonal square Gᵢᵢ² equals 81; every off-diagonal Gᵢⱼ is nonzero by its residue modulo two, so its square is at least one. These lower bounds sum to 9·81 + 9·8 = 801. Equality of the total sums forces equality first in every row sum and then in every individual summand. Thus each off-diagonal Gᵢⱼ has square one and is a sign.

For any three rows indexed by i, j and r, sign arithmetic modulo four gives Gᵢⱼ = Gᵢᵣ + Gᵣⱼ − 1 modulo four: the corresponding identity holds in each column, and the nine subtracted ones sum to one modulo four. Set s(0)=1 and s(i)=Gᵢ₀ for i≠0, and let b = diagonal(s)c. Every s(i) is a sign, so b is a sign matrix and (bbᵀ)ᵢⱼ = s(i)s(j)Gᵢⱼ. Its off-diagonal entries are signs, and (bbᵀ)ᵢ₀ = Gᵢ₀² = 1 for i≠0. Symmetry supplies the same identity in row zero. For distinct nonzero i and j, the preceding congruence with r=0 makes (bbᵀ)ᵢⱼ equal to one modulo four, excluding minus one. Its diagonal entries are nine. Therefore bbᵀ = 8I + J, where J is the matrix with every entry one.

Map b entrywise from the integers to ZMod 3, obtaining a. Let u and v be the vectors of length nine with constant entries two and one in ZMod 3. The mapped identity is aaᵀ = 2(I + uvᵀ), with uvᵀ expressed as the product of the single column u and the single row v indexed by Unit. Taking determinants and using the determinant formula for a rank-one addition to the identity yields det(a)² = 2⁹(1 + Σᵢ v(i)u(i)) = 2 in ZMod 3. No element z of ZMod 3 has square two: taking the natural representative z.val would give a natural square congruent to two modulo three, whereas natural squares have residue zero or one. This is a contradiction.

If claim held, its instance at the odd natural number nine would provide a sign matrix c with Hadamardness 9³ + 9·(9−1) = 801. The preceding argument rules out such a matrix, so claim is false. Its additional lower-bound clause is unnecessary for this contradiction.

## References

- Truth anchor: `D5/S3/Quantum/Matrix/SinghNechitaOddHadamardnessRefutation.IsSignMatrix`
- Truth anchor: `D5/S3/Quantum/Matrix/SinghNechitaOddHadamardnessRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Matrix/SinghNechitaOddHadamardnessRefutation.hadamardness`
- Truth anchor: `D5/S3/Quantum/Matrix/SinghNechitaOddHadamardnessRefutation.result`
- Dependency: [D5/S3/Factorization/CubeGapFiveNoSquare](../../Factorization/CubeGapFiveNoSquare.md)
