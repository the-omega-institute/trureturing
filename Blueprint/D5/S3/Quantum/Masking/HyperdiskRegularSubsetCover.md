# A regular subset without a finite hyperdisk cover

## Abstract

A regular subset of a four-dimensional hyperdisk has no finite hyperdisk cover.

**Definition 1.1 (Hyperdisks of unit vectors).**

$$\forall \left(n: \mathbb{N}\right), \left(\forall \left(s: \operatorname{Set}\left(\operatorname{EuclideanSpace}\left(\mathbb{C}, \operatorname{Fin}\left(n\right)\right)\right)\right), \left(\operatorname{D5.S3.Quantum.Masking.HyperdiskRegularSubsetCover.IsHyperdisk}\left(s\right) = \left(\exists \left(m: \mathbb{N}\right), \left(\exists \left(\phi: \left(\operatorname{Fin}\left(m\right)\right) \to \left(\operatorname{EuclideanSpace}\left(\mathbb{C}, \operatorname{Fin}\left(n\right)\right)\right)\right), \left(\exists \left(r: \left(\operatorname{Fin}\left(m\right)\right) \to \left(\mathbb{R}\right)\right), \left(\left(\operatorname{Orthonormal}\left(\mathbb{C}, \phi\right)\right) \land \left(\left(\operatorname{Submodule.span}\left(\mathbb{C}, \operatorname{Set.range}\left(\phi\right)\right) = \operatorname{Submodule.span}\left(\mathbb{C}, s\right)\right) \land \left(\left(\forall \left(j: \operatorname{Fin}\left(m\right)\right), \left(\left(0: \mathbb{R}\right) < r\left(j\right)\right)\right) \land \left(s = \{\left(\psi: \operatorname{EuclideanSpace}\left(\mathbb{C}, \operatorname{Fin}\left(n\right)\right)\right) \mid \left(\left\lVert \psi \right\rVert = \left(1: \mathbb{R}\right)\right) \land \left(\forall \left(j: \operatorname{Fin}\left(m\right)\right), \left(\left\lVert \operatorname{inner}\left(\mathbb{C}, \phi\left(j\right), \psi\right) \right\rVert = r\left(j\right)\right)\right)\}\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Masking/HyperdiskRegularSubsetCover.IsHyperdisk` (`✓ std3`).

*Citation.* Ding, Feng; Hu, Xueyuan (2020). *Masking quantum information on hyperdisks*. DOI: [10.1103/PhysRevA.102.042404](https://doi.org/10.1103/PhysRevA.102.042404). URL: <https://arxiv.org/abs/1909.11256v3>.

*Commentary.*

A hyperdisk is the full set of unit vectors with specified strictly positive coefficient moduli in a finite orthonormal family spanning its complex linear span. The family has m elements, and r assigns their real coefficient moduli; the span equality makes this family a basis of the displayed span. This is Definition 1 of Ding and Hu, arXiv:1909.11256v3, masking.tex lines 110–125. Pure states are represented by unit vectors, so all global phases remain in the set. The equality of spans and the equality with the entire modulus level set are both required.

**Definition 1.2 (Regular subsets).**

$$\forall \left(n: \mathbb{N}\right), \left(\forall \left(c: \operatorname{Set}\left(\operatorname{EuclideanSpace}\left(\mathbb{C}, \operatorname{Fin}\left(n\right)\right)\right)\right), \left(\forall \left(s: \operatorname{Set}\left(\operatorname{EuclideanSpace}\left(\mathbb{C}, \operatorname{Fin}\left(n\right)\right)\right)\right), \left(\operatorname{D5.S3.Quantum.Masking.HyperdiskRegularSubsetCover.IsRegularSubset}\left(c, s\right) = \left(\left(\operatorname{D5.S3.Quantum.Masking.HyperdiskRegularSubsetCover.IsHyperdisk}\left(s\right)\right) \land \left(\operatorname{Set.inter}\left(\left(\operatorname{SetLike.coe}\left(\operatorname{Submodule.span}\left(\mathbb{C}, c\right)\right): \operatorname{Set}\left(\operatorname{EuclideanSpace}\left(\mathbb{C}, \operatorname{Fin}\left(n\right)\right)\right)\right), s\right) = c\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Masking/HyperdiskRegularSubsetCover.IsRegularSubset` (`✓ std3`).

*Citation.* Ding, Feng; Hu, Xueyuan (2020). *Masking quantum information on hyperdisks*. DOI: [10.1103/PhysRevA.102.042404](https://doi.org/10.1103/PhysRevA.102.042404). URL: <https://arxiv.org/abs/1909.11256v3>.

*Commentary.*

The set c is regular in s when s is a hyperdisk and intersecting s with the complex linear span of c returns exactly c. The submodule is explicitly coerced to its underlying set before intersection. This is Definition 4, masking.tex lines 251–258; in particular, the equality implies that c is contained in s.

**Definition 1.3 (The finite-cover question).**

$$\operatorname{D5.S3.Quantum.Masking.HyperdiskRegularSubsetCover.claim} = \left(\forall \left(n: \mathbb{N}\right), \left(\forall \left(s: \operatorname{Set}\left(\operatorname{EuclideanSpace}\left(\mathbb{C}, \operatorname{Fin}\left(n\right)\right)\right)\right), \left(\forall \left(c: \operatorname{Set}\left(\operatorname{EuclideanSpace}\left(\mathbb{C}, \operatorname{Fin}\left(n\right)\right)\right)\right), \left(\left(\operatorname{D5.S3.Quantum.Masking.HyperdiskRegularSubsetCover.IsRegularSubset}\left(c, s\right)\right) \to \left(\exists \left(k: \mathbb{N}\right), \left(\exists \left(h: \left(\operatorname{Fin}\left(k\right)\right) \to \left(\operatorname{Set}\left(\operatorname{EuclideanSpace}\left(\mathbb{C}, \operatorname{Fin}\left(n\right)\right)\right)\right)\right), \left(\left(\forall \left(i: \operatorname{Fin}\left(k\right)\right), \left(\left(\operatorname{D5.S3.Quantum.Masking.HyperdiskRegularSubsetCover.IsHyperdisk}\left(h\left(i\right)\right)\right) \land \left(h\left(i\right) \subseteq c\right)\right)\right) \land \left(c = \operatorname{Set.iUnion}\left(\left(\lambda \left(i: \operatorname{Fin}\left(k\right)\right) \mapsto h\left(i\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Masking/HyperdiskRegularSubsetCover.claim` (`✓ std3`).

*Citation.* Ding, Feng; Hu, Xueyuan (2020). *Masking quantum information on hyperdisks*. DOI: [10.1103/PhysRevA.102.042404](https://doi.org/10.1103/PhysRevA.102.042404). URL: <https://arxiv.org/abs/1909.11256v3>.

*Commentary.*

The source states: "A related open question is whether a regular subset of a hyperdisk can be covered with finite number of hyperdisks." For every natural dimension n and every regular subset c of a hyperdisk s, the assertion asks for a natural k and k hyperdisks h i, each contained in c, whose union is exactly c. It expresses the second open question in the conclusion, masking.tex line 651, with the contained-cover convention of lines 272–279. There is no positivity restriction on n or k, and no identification of vectors modulo global phase.

**Theorem 1.4 (A four-coordinate counterexample).**

$$\neg \left(\forall \left(n: \mathbb{N}\right), \left(\forall \left(s: \operatorname{Set}\left(\operatorname{EuclideanSpace}\left(\mathbb{C}, \operatorname{Fin}\left(n\right)\right)\right)\right), \left(\forall \left(c: \operatorname{Set}\left(\operatorname{EuclideanSpace}\left(\mathbb{C}, \operatorname{Fin}\left(n\right)\right)\right)\right), \left(\left(\operatorname{D5.S3.Quantum.Masking.HyperdiskRegularSubsetCover.IsRegularSubset}\left(c, s\right)\right) \to \left(\exists \left(k: \mathbb{N}\right), \left(\exists \left(h: \left(\operatorname{Fin}\left(k\right)\right) \to \left(\operatorname{Set}\left(\operatorname{EuclideanSpace}\left(\mathbb{C}, \operatorname{Fin}\left(n\right)\right)\right)\right)\right), \left(\left(\forall \left(i: \operatorname{Fin}\left(k\right)\right), \left(\left(\operatorname{D5.S3.Quantum.Masking.HyperdiskRegularSubsetCover.IsHyperdisk}\left(h\left(i\right)\right)\right) \land \left(h\left(i\right) \subseteq c\right)\right)\right) \land \left(c = \operatorname{Set.iUnion}\left(\left(\lambda \left(i: \operatorname{Fin}\left(k\right)\right) \mapsto h\left(i\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Masking/HyperdiskRegularSubsetCover.result` (`✓ std3`). ∎

*Resolves.* `Problems/ding-hu-2020-hyperdisk-regular-subset-finite-cover` (refuted) by `D5/S3/Quantum/Masking/HyperdiskRegularSubsetCover.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"ding-hu-2020-hyperdisk-regular-subset-finite-cover","declaration_gid":"D5/S3/Quantum/Masking/HyperdiskRegularSubsetCover.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Ding, Feng; Hu, Xueyuan (2020). *Masking quantum information on hyperdisks*. DOI: [10.1103/PhysRevA.102.042404](https://doi.org/10.1103/PhysRevA.102.042404). URL: <https://arxiv.org/abs/1909.11256v3>.

*Commentary.*

In complex Euclidean four-space, set ρ = (1,2,3,4)/√30 and let S consist of the unit vectors x with |xⱼ| = ρⱼ. Let V be the kernel of the complex coordinate-projection linear map x ↦ 6x₀ + 3x₁ + 2x₂ + 3x₃, and set C = V ∩ S. The squared coordinate moduli sum to one. To see that S spans the whole space, compare the vector with positive real coordinates ρⱼ to the vector obtained by reversing the sign of just coordinate j. Their difference is 2ρⱼ times the jth coordinate vector, and ρⱼ is positive. Thus the standard orthonormal basis exhibits S as a hyperdisk. Since C lies in V, its linear span lies in V as well; hence span(C) ∩ S = C, and C is regular in S.

For each natural a take tₐ = −1/2 − 1/(4(a+1)), where a is included in the real numbers. Then −3/4 ≤ tₐ ≤ −1/2. For such a real t put z = t + i√(1−t²), w = −2−z, q = 5+4t and κ = √((4−q)/q). The four complex phases are z, w(1+iκ)/2, w(1−iκ)/2 and 1. Here |z|² = 1, |w|² = q and 0 < q ≤ 4, so the squared moduli of the middle phases are q(1+κ²)/4 = 1. The sum of the first three phases plus twice the fourth is zero. Multiplying these phases coordinatewise by ρ therefore gives a unit vector xₐ in C.

If xₐ = u xᵦ for a complex scalar u, comparison of their identical nonzero fourth coordinates gives u = 1. The real parts of the first coordinates then give tₐ = tᵦ. The defining reciprocals have positive denominators, so this equality gives a = b. Thus these vectors lie on pairwise distinct complex rays.

The phase comparison used next starts with complex A and B. If |−A+B| = |A+B| and |iA+B| = |A+B|, expanding the squared moduli makes both the real and imaginary parts of A times the conjugate of B zero. Consequently A = 0 or B = 0. Now suppose the modulus of a finite sum of coefficients times independent unit phases is constant. If one coefficient is nonzero, varying its phase through 1, −1 and i forces the sum of all remaining terms to vanish for every choice of their phases. Comparing the all-one choice with the choice that negates a second phase makes that second coefficient zero. Hence at most one coefficient is nonzero.

For an orthonormal system φ spanning a vector x, orthonormal expansion reconstructs x from its inner-product coefficients. The orthogonal-family norm identity gives the squared norm of a linear combination of the φ p as the sum of the squared coefficient moduli. Therefore, if x belongs to a hyperdisk with positive coefficient moduli r p, those moduli have squared sum one, and every vector Σₚ (r p)uₚ φ p with independent unit phases uₚ belongs to the same hyperdisk; the real numbers r p are included in the complex scalars. If this hyperdisk is contained in C, each coordinate of these vectors has the constant modulus ρⱼ. Applying the phase comparison coordinate by coordinate shows that distinct vectors φ p have disjoint coordinate supports.

The cancellation obstruction concerns two disjointly supported four-coordinate vectors whose coordinate sums are zero. Suppose the first has fourth-coordinate modulus 2 and each of its first three coordinates is zero or has modulus 1. Its fourth coordinate forces the second vector's fourth coordinate to vanish. The first vector cannot have zero or just one nonzero coordinate among its first three: their sum could not cancel a term of modulus 2. If it has exactly two, the second vector can only have the remaining coordinate, which its zero-sum condition forces to vanish. If it has all three, disjointness already makes the second vector zero.

Also, if a linear combination of independent unit phases vanishes for every phase choice, comparing all phases equal to one with one phase negated shows that each coefficient vanishes. Apply this to the functional defining V and to all phase choices in a hyperdisk contained in C. It follows that every φ p separately lies in V. For each p, multiply the jth coordinate of (r p)φ p by the jth entry of (6,3,2,3) and by √30/6. The resulting vector has coordinate sum zero; on its nonzero coordinates its moduli are the corresponding entries of (1,1,1,2). Indeed the vector with all phases equal to one belongs to C, and disjoint supports isolate each nonzero coordinate. Its fourth coordinate is nonzero, so some φ p has a nonzero fourth coordinate. The cancellation obstruction forces every other scaled vector to vanish. That would make every other φ p zero, contradicting orthonormality. Thus there is at most one basis vector.

A hyperdisk contained in C and containing a unit vector cannot have an empty basis, since orthonormal reconstruction would make that vector zero. It therefore has exactly one basis vector. Expanding any two of its vectors x and y in that basis shows that x is the scalar multiple of y given by the ratio of their inner-product coefficients; the denominator is nonzero because its modulus is strictly positive. Hence any two vectors in such a hyperdisk lie on the same complex ray. The proof uses that a nonempty Fin m with m ≤ 1 is subsingleton, so the single surviving basis index supports the reconstruction.

Assume a finite cover of C by hyperdisks h i indexed by Fin k. For each natural a choose f(a) with xₐ in h(f(a)). If f(a) = f(b), the preceding one-ray conclusion makes xₐ a complex scalar multiple of xᵦ, so a = b. This gives an injection from the natural numbers into Fin k, which would make the natural numbers finite. Their infinitude is the contradiction.

## References

- Truth anchor: `D5/S3/Quantum/Masking/HyperdiskRegularSubsetCover.IsHyperdisk`
- Truth anchor: `D5/S3/Quantum/Masking/HyperdiskRegularSubsetCover.IsRegularSubset`
- Truth anchor: `D5/S3/Quantum/Masking/HyperdiskRegularSubsetCover.claim`
- Truth anchor: `D5/S3/Quantum/Masking/HyperdiskRegularSubsetCover.result`
