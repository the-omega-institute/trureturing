# A dimension defect for uniform matrix product states

## Abstract

Two-site uniform matrix product states with bond dimension two and five symbols miss the expected dimension.

**Definition 1.1 (Trace coefficients of a matrix word).**

$$\forall (b: \mathbb{N}), (\forall (d: \mathbb{N}), (\forall (n: \mathbb{N}), (\forall (m: (\operatorname{Fin}\left(d\right)) \to (\operatorname{Matrix}\left(\operatorname{Fin}\left(b\right), \operatorname{Fin}\left(b\right), \mathbb{C}\right))), (\forall (i: (\operatorname{Fin}\left(n\right)) \to (\operatorname{Fin}\left(d\right))), ((\operatorname{D5.S3.Quantum.TensorNetworks.UniformMPSExpectedDimensionRefutation.traceWord}\left(b, d, n, m, i\right): \mathbb{C}) = \operatorname{Matrix.trace}\left(\operatorname{List.prod}\left(\operatorname{List.ofFn}\left(\lambda (k: \operatorname{Fin}\left(n\right)) \mapsto (m\left(i\left(k\right)\right))\right)\right)\right))))))$$

*Formalization.* `D5/S3/Quantum/TensorNetworks/UniformMPSExpectedDimensionRefutation.traceWord` (`✓ std3`).

*Citation.* Adam Czapliński; Mateusz Michałek; Tim Seynnaeve (2023). *Uniform matrix product states from an algebraic geometer's point of view*. DOI: [10.1016/j.aam.2022.102417](https://doi.org/10.1016/j.aam.2022.102417). URL: <https://arxiv.org/abs/1904.07563v1>.

*Commentary.*

For a family m of d complex b by b matrices and a word i of length n, take the trace of the product m(i(0)) through m(i(n - 1)), in that order. These are the coefficients of the tensor T_n in uMPS-final.tex, lines 180–185. List.ofFn lists the sites in order; its product is the identity matrix when n is zero. The definition permits all natural b, d and n, while the source assumes that all three are positive.

**Definition 1.2 (The image of the trace-word map).**

$$\forall (b: \mathbb{N}), (\forall (d: \mathbb{N}), (\forall (n: \mathbb{N}), ((\operatorname{D5.S3.Quantum.TensorNetworks.UniformMPSExpectedDimensionRefutation.uMPS}\left(b, d, n\right): \operatorname{Set}\left(((\operatorname{Fin}\left(n\right)) \to (\operatorname{Fin}\left(d\right))) \to (\mathbb{C})\right)) = \operatorname{Set.range}\left(\operatorname{D5.S3.Quantum.TensorNetworks.UniformMPSExpectedDimensionRefutation.traceWord}\left(b, d, n\right)\right))))$$

*Formalization.* `D5/S3/Quantum/TensorNetworks/UniformMPSExpectedDimensionRefutation.uMPS` (`✓ std3`).

*Citation.* Adam Czapliński; Mateusz Michałek; Tim Seynnaeve (2023). *Uniform matrix product states from an algebraic geometer's point of view*. DOI: [10.1016/j.aam.2022.102417](https://doi.org/10.1016/j.aam.2022.102417). URL: <https://arxiv.org/abs/1904.07563v1>.

*Commentary.*

The set uMPS b d n consists of all coefficient functions obtained by varying the same family of matrices at every site. The ambient space is the space of complex functions on words Fin n → Fin d. This is the image description of uniform periodic matrix product states in uMPS-final.tex, lines 187–193, with no normalization condition.

**Definition 1.3 (Dimension through the vanishing ideal).**

$$\forall (\sigma: \operatorname{Type}*), (\forall (s: \operatorname{Set}\left((\sigma) \to (\mathbb{C})\right)), ((\operatorname{D5.S3.Quantum.TensorNetworks.UniformMPSExpectedDimensionRefutation.varietyDim}\left(s\right): \operatorname{WithBot}\left(\mathbb{N}_{\infty}\right)) = \operatorname{ringKrullDim}\left((\operatorname{MvPolynomial}\left(\sigma, \mathbb{C}\right)) / (\operatorname{MvPolynomial.vanishingIdeal}\left(\mathbb{C}, s\right))\right)))$$

*Formalization.* `D5/S3/Quantum/TensorNetworks/UniformMPSExpectedDimensionRefutation.varietyDim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Adam Czapliński; Mateusz Michałek; Tim Seynnaeve (2023). *Uniform matrix product states from an algebraic geometer's point of view*. DOI: [10.1016/j.aam.2022.102417](https://doi.org/10.1016/j.aam.2022.102417). URL: <https://arxiv.org/abs/1904.07563v1>.

*Commentary.*

For a set s of complex-valued functions on any type σ, form the polynomial ring with one variable for each element of σ and quotient by all polynomials vanishing on s. The Krull dimension of this coordinate ring defines varietyDim s, with values in WithBot ℕ∞. For finite σ this measures the dimension of the Zariski closure, so the image itself need not be closed. The source considers this closure in uMPS-final.tex, line 211, and its dimension in lines 272–273.

**Definition 1.4 (Expected dimension for every positive triple).**

$$(\operatorname{D5.S3.Quantum.TensorNetworks.UniformMPSExpectedDimensionRefutation.claim}) \Leftrightarrow (\forall (b: \mathbb{N}), (\forall (d: \mathbb{N}), (\forall (n: \mathbb{N}), ((0 < b) \to ((0 < d) \to ((0 < n) \to (\operatorname{D5.S3.Quantum.TensorNetworks.UniformMPSExpectedDimensionRefutation.varietyDim}\left(\operatorname{D5.S3.Quantum.TensorNetworks.UniformMPSExpectedDimensionRefutation.uMPS}\left(b, d, n\right)\right) = (\operatorname{Nat.cast}\left((\operatorname{min}\left((((d) - (1)) \cdot (b^{2})) + (1), \operatorname{Module.finrank}\left(\mathbb{C}, \operatorname{Subtype}\left(\lambda (x: ((\operatorname{Fin}\left(n\right)) \to (\operatorname{Fin}\left(d\right))) \to (\mathbb{C})) \mapsto (x \in \operatorname{LinearMap.fixedSubmodule}\left(\operatorname{LinearMap.funLeft}\left(\mathbb{C}, \mathbb{C}, \lambda (i: (\operatorname{Fin}\left(n\right)) \to (\operatorname{Fin}\left(d\right))) \mapsto (\operatorname{Function.comp}\left(i, \operatorname{Equiv.toFun}\left(\operatorname{finRotate}\left(n\right)\right)\right))\right)\right))\right)\right)\right): \mathbb{N})\right): \operatorname{WithBot}\left(\mathbb{N}_{\infty}\right)))))))))$$

*Formalization.* `D5/S3/Quantum/TensorNetworks/UniformMPSExpectedDimensionRefutation.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Adam Czapliński; Mateusz Michałek; Tim Seynnaeve (2023). *Uniform matrix product states from an algebraic geometer's point of view*. DOI: [10.1016/j.aam.2022.102417](https://doi.org/10.1016/j.aam.2022.102417). URL: <https://arxiv.org/abs/1904.07563v1>.

*Commentary.*

For every positive b, d and n, the asserted dimension is the smaller of (d - 1)b² + 1 and the complex dimension of the fixed subspace of cyclic rotation. Here rotation sends a word i to i composed with finRotate n; a coefficient function is fixed exactly when its value is unchanged by this operation. The rotation equivalence is used through its underlying function, and the fixed submodule through its underlying subtype of coefficient functions. The minimum is computed in ℕ and then cast to WithBot ℕ∞. This expresses the expected-dimension equality of uMPS-final.tex, lines 299–305, for every triple as in Conjecture 2.14, lines 311–313; the cyclic subspace is described at line 209.

**Theorem 1.5 (A determinant forces a strict dimension defect).**

$$\neg (\operatorname{D5.S3.Quantum.TensorNetworks.UniformMPSExpectedDimensionRefutation.claim})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/UniformMPSExpectedDimensionRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/czaplinski-michalek-seynnaeve-2023-umps-expected-dimension` (refuted) by `D5/S3/Quantum/TensorNetworks/UniformMPSExpectedDimensionRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"czaplinski-michalek-seynnaeve-2023-umps-expected-dimension","declaration_gid":"D5/S3/Quantum/TensorNetworks/UniformMPSExpectedDimensionRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Adam Czapliński; Mateusz Michałek; Tim Seynnaeve (2023). *Uniform matrix product states from an algebraic geometer's point of view*. DOI: [10.1016/j.aam.2022.102417](https://doi.org/10.1016/j.aam.2022.102417). URL: <https://arxiv.org/abs/1904.07563v1>.

*Commentary.*

Let U be the set of pairs (a,b) in Fin 5 × Fin 5 with a ≤ b, and let the sorted pair associated to (i,j) be (min(i,j),max(i,j)). There are 15 elements of U. A function v : U → ℂ determines a two-site coefficient function by sending a word i to v at the sorted pair of i(0) and i(1). Rotation interchanges the two entries, so this coefficient function is fixed. This construction is complex linear and injective: evaluation on the word (a,b) recovers v(a,b) for every (a,b) in U. Consequently the cyclic fixed subspace has dimension at least 15.

For five complex 2 by 2 matrices m(i), the two-site coefficients are S(i,j) = tr(m(i)m(j)). Define X(i,(a,b)) = m(i)(a,b) and Y((a,b),j) = m(j)(b,a), with (a,b) in Fin 2 × Fin 2. Expanding the trace as a double sum gives S = XY. The linear map represented by Y has a five-dimensional domain and a four-dimensional codomain, so it has a nonzero kernel vector. The same vector is killed by XY, and therefore det S = 0.

Write A for the coordinate ring of uMPS 2 5 2 and x(i,j) for the variable indexed by the two-letter word (i,j). Since tr(m(i)m(j)) = tr(m(j)m(i)), each difference x(i,j) - x(j,i) belongs to the vanishing ideal. There is a complex algebra homomorphism ψ from P = ℂ[y(p) : p in U] to A sending y(a,b) to the class of x(a,b). The symmetry relations show that y at the sorted pair of (i,j) maps to the class of x(i,j), including when i > j. Thus every coordinate variable is in the image. Induction on polynomials, using constants, addition and multiplication by a variable, then proves that ψ is surjective.

In P take Δ to be the determinant of the symmetric 5 by 5 matrix whose (i,j) entry is y at the sorted pair of (i,j). Evaluating the diagonal variables at 1 and the other variables at 0 gives the identity matrix and hence Δ = 1 under this evaluation. Therefore Δ is a nonzero polynomial. Determinants commute with algebra homomorphisms; ψ(Δ) is the class of det(x(i,j)). Evaluating this determinant at any trace-word image gives det S = 0, so it belongs to the vanishing ideal and ψ(Δ) = 0.

The polynomial ring P is a domain, so the nonzero element Δ is a nonzero divisor. The Krull-dimension inequality for a surjective ring homomorphism killing such an element gives dim A + 1 ≤ dim P. There are 15 variables and ℂ has Krull dimension zero, so dim P = 15. Cancellation in WithBot ℕ∞ yields varietyDim (uMPS 2 5 2) ≤ 14.

Suppose claim holds and apply it to b = 2, d = 5 and n = 2, which are all positive. The first entry of its minimum is (5 - 1)2² + 1 = 17, and the cyclic-space bound makes the second entry at least 15. Thus the minimum is at least 15 in ℕ. Casting this inequality to WithBot ℕ∞ and substituting the asserted dimension equality gives 15 ≤ varietyDim (uMPS 2 5 2) ≤ 14, a contradiction.

## References

- Truth anchor: `D5/S3/Quantum/TensorNetworks/UniformMPSExpectedDimensionRefutation.claim`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/UniformMPSExpectedDimensionRefutation.result`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/UniformMPSExpectedDimensionRefutation.traceWord`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/UniformMPSExpectedDimensionRefutation.uMPS`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/UniformMPSExpectedDimensionRefutation.varietyDim`
- Dependency: [D5/S3/Arith/Lattices/Klartag/Walk/ChainWiring](../../Arith/Lattices/Klartag/Walk/ChainWiring.md)
