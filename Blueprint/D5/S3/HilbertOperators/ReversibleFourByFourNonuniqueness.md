# Reversible four-by-four algebras need not be unitarily equivalent

## Abstract

A weighted anticommuting algebra of four-by-four complex matrices disproves unitary uniqueness of reversible algebras.

**Definition 1.1 (Multiplicative closure).**

$$\forall \left(b: \operatorname{Submodule}\left(\mathbb{C}, \operatorname{Matrix}\left(\operatorname{Fin}\left(\left(4: \mathbb{N}\right)\right), \operatorname{Fin}\left(\left(4: \mathbb{N}\right)\right), \mathbb{C}\right)\right)\right), \left(\left(\operatorname{D5.S3.HilbertOperators.ReversibleFourByFourNonuniqueness.IsMatrixAlgebra}\left(b\right)\right) \Leftrightarrow \left(\forall \left(x: \operatorname{Matrix}\left(\operatorname{Fin}\left(\left(4: \mathbb{N}\right)\right), \operatorname{Fin}\left(\left(4: \mathbb{N}\right)\right), \mathbb{C}\right)\right), \left(\left(x \in b\right) \to \left(\forall \left(y: \operatorname{Matrix}\left(\operatorname{Fin}\left(\left(4: \mathbb{N}\right)\right), \operatorname{Fin}\left(\left(4: \mathbb{N}\right)\right), \mathbb{C}\right)\right), \left(\left(y \in b\right) \to \left(\left(x\right) \cdot \left(y\right) \in b\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/HilbertOperators/ReversibleFourByFourNonuniqueness.IsMatrixAlgebra` (`✓ std3`).

*Citation.* David P. Blecher (2025). *Commutativity of operator algebras*. DOI: [10.1016/j.exmath.2025.125742](https://doi.org/10.1016/j.exmath.2025.125742). URL: <https://arxiv.org/abs/2509.17673v2>.

*Commentary.*

A complex subspace b of the four-by-four matrices is a matrix algebra when it is closed under multiplication. No multiplicative identity is required. This is the finite-matrix setting of the concrete operator algebras in 3commfarx.tex, lines 140–145; the norm is inherited from the ambient operators.

**Definition 1.2 (A noncommuting pair).**

$$\forall \left(b: \operatorname{Submodule}\left(\mathbb{C}, \operatorname{Matrix}\left(\operatorname{Fin}\left(\left(4: \mathbb{N}\right)\right), \operatorname{Fin}\left(\left(4: \mathbb{N}\right)\right), \mathbb{C}\right)\right)\right), \left(\left(\operatorname{D5.S3.HilbertOperators.ReversibleFourByFourNonuniqueness.IsNoncommutative}\left(b\right)\right) \Leftrightarrow \left(\exists \left(x: \operatorname{Matrix}\left(\operatorname{Fin}\left(\left(4: \mathbb{N}\right)\right), \operatorname{Fin}\left(\left(4: \mathbb{N}\right)\right), \mathbb{C}\right)\right), \left(\left(x \in b\right) \land \left(\exists \left(y: \operatorname{Matrix}\left(\operatorname{Fin}\left(\left(4: \mathbb{N}\right)\right), \operatorname{Fin}\left(\left(4: \mathbb{N}\right)\right), \mathbb{C}\right)\right), \left(\left(y \in b\right) \land \left(\left(x\right) \cdot \left(y\right) \ne \left(y\right) \cdot \left(x\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/HilbertOperators/ReversibleFourByFourNonuniqueness.IsNoncommutative` (`✓ std3`).

*Citation.* David P. Blecher (2025). *Commutativity of operator algebras*. DOI: [10.1016/j.exmath.2025.125742](https://doi.org/10.1016/j.exmath.2025.125742). URL: <https://arxiv.org/abs/2509.17673v2>.

*Commentary.*

Noncommutativity means that b contains two matrices x and y for which xy differs from yx. The same criterion appears for the CAR example in 3commfarx.tex, line 661.

**Definition 1.3 (Reversed multiplication with all matrix norms preserved).**

$$\forall \left(b: \operatorname{Submodule}\left(\mathbb{C}, \operatorname{Matrix}\left(\operatorname{Fin}\left(\left(4: \mathbb{N}\right)\right), \operatorname{Fin}\left(\left(4: \mathbb{N}\right)\right), \mathbb{C}\right)\right)\right), \left(\left(\operatorname{D5.S3.HilbertOperators.ReversibleFourByFourNonuniqueness.IsReversible}\left(b\right)\right) \Leftrightarrow \left(\exists \left(m: \mathbb{N}\right), \left(\left(\left(0: \mathbb{N}\right) < m\right) \land \left(\exists \left(\rho: \left(\operatorname{Matrix}\left(\operatorname{Fin}\left(\left(4: \mathbb{N}\right)\right), \operatorname{Fin}\left(\left(4: \mathbb{N}\right)\right), \mathbb{C}\right)\right) \to_{l}[\mathbb{C}] \left(\operatorname{Matrix}\left(\operatorname{Fin}\left(m\right), \operatorname{Fin}\left(m\right), \mathbb{C}\right)\right)\right), \left(\left(\forall \left(x: \operatorname{Matrix}\left(\operatorname{Fin}\left(\left(4: \mathbb{N}\right)\right), \operatorname{Fin}\left(\left(4: \mathbb{N}\right)\right), \mathbb{C}\right)\right), \left(\left(x \in b\right) \to \left(\forall \left(y: \operatorname{Matrix}\left(\operatorname{Fin}\left(\left(4: \mathbb{N}\right)\right), \operatorname{Fin}\left(\left(4: \mathbb{N}\right)\right), \mathbb{C}\right)\right), \left(\left(y \in b\right) \to \left(\left(\operatorname{DFunLike.coe}\left(\rho\right): \left(\operatorname{Matrix}\left(\operatorname{Fin}\left(\left(4: \mathbb{N}\right)\right), \operatorname{Fin}\left(\left(4: \mathbb{N}\right)\right), \mathbb{C}\right)\right) \to \left(\operatorname{Matrix}\left(\operatorname{Fin}\left(m\right), \operatorname{Fin}\left(m\right), \mathbb{C}\right)\right)\right)\left(\left(y\right) \cdot \left(x\right)\right) = \left(\left(\operatorname{DFunLike.coe}\left(\rho\right): \left(\operatorname{Matrix}\left(\operatorname{Fin}\left(\left(4: \mathbb{N}\right)\right), \operatorname{Fin}\left(\left(4: \mathbb{N}\right)\right), \mathbb{C}\right)\right) \to \left(\operatorname{Matrix}\left(\operatorname{Fin}\left(m\right), \operatorname{Fin}\left(m\right), \mathbb{C}\right)\right)\right)\left(x\right)\right) \cdot \left(\left(\operatorname{DFunLike.coe}\left(\rho\right): \left(\operatorname{Matrix}\left(\operatorname{Fin}\left(\left(4: \mathbb{N}\right)\right), \operatorname{Fin}\left(\left(4: \mathbb{N}\right)\right), \mathbb{C}\right)\right) \to \left(\operatorname{Matrix}\left(\operatorname{Fin}\left(m\right), \operatorname{Fin}\left(m\right), \mathbb{C}\right)\right)\right)\left(y\right)\right)\right)\right)\right)\right)\right) \land \left(\forall \left(n: \mathbb{N}\right), \left(\forall \left(x: \left(\operatorname{Fin}\left(n\right)\right) \to \left(\left(\operatorname{Fin}\left(n\right)\right) \to \left(\operatorname{Matrix}\left(\operatorname{Fin}\left(\left(4: \mathbb{N}\right)\right), \operatorname{Fin}\left(\left(4: \mathbb{N}\right)\right), \mathbb{C}\right)\right)\right)\right), \left(\left(\forall \left(i: \operatorname{Fin}\left(n\right)\right), \left(\forall \left(j: \operatorname{Fin}\left(n\right)\right), \left(x\left(i, j\right) \in b\right)\right)\right) \to \left(\left\lVert \operatorname{Matrix.comp}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \operatorname{Fin}\left(m\right), \operatorname{Fin}\left(m\right), \mathbb{C}, \left(\lambda \left(i: \operatorname{Fin}\left(n\right)\right) \mapsto \left(\left(\lambda \left(j: \operatorname{Fin}\left(n\right)\right) \mapsto \left(\left(\operatorname{DFunLike.coe}\left(\rho\right): \left(\operatorname{Matrix}\left(\operatorname{Fin}\left(\left(4: \mathbb{N}\right)\right), \operatorname{Fin}\left(\left(4: \mathbb{N}\right)\right), \mathbb{C}\right)\right) \to \left(\operatorname{Matrix}\left(\operatorname{Fin}\left(m\right), \operatorname{Fin}\left(m\right), \mathbb{C}\right)\right)\right)\left(x\left(i, j\right)\right)\right)\right)\right)\right)\right) \right\rVert = \left\lVert \operatorname{Matrix.comp}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \operatorname{Fin}\left(\left(4: \mathbb{N}\right)\right), \operatorname{Fin}\left(\left(4: \mathbb{N}\right)\right), \mathbb{C}, x\right) \right\rVert\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/HilbertOperators/ReversibleFourByFourNonuniqueness.IsReversible` (`✓ std3`).

*Citation.* David P. Blecher (2025). *Commutativity of operator algebras*. DOI: [10.1016/j.exmath.2025.125742](https://doi.org/10.1016/j.exmath.2025.125742). URL: <https://arxiv.org/abs/2509.17673v2>.

*Commentary.*

There must be a positive natural m and a complex-linear map ρ from the whole ambient four-by-four matrix space to the m-by-m matrices. On b the map reverses multiplication, and entrywise application preserves the Euclidean operator norm of every Matrix.comp assembly of an n-by-n family of four-by-four blocks, for every natural n. DFunLike.coe explicitly treats ρ as a function. The condition on block entries is an implication. Reversibility in 3commfarx.tex, line 145, means that reversed multiplication with the same matrix norms is again an abstract operator algebra. The displayed finite-matrix representation is a sufficient condition for that notion: the restriction of ρ to b is a completely isometric antihomomorphism. It specifies a finite-dimensional representation and an ambient linear map, neither of which is required in the source's general definition.

**Definition 1.4 (The CAR algebra in four dimensions).**

$$\left(\operatorname{D5.S3.HilbertOperators.ReversibleFourByFourNonuniqueness.carAlgebra}: \operatorname{Submodule}\left(\mathbb{C}, \operatorname{Matrix}\left(\operatorname{Fin}\left(\left(4: \mathbb{N}\right)\right), \operatorname{Fin}\left(\left(4: \mathbb{N}\right)\right), \mathbb{C}\right)\right)\right) = \left(\operatorname{let} \left(u: \operatorname{Matrix}\left(\operatorname{Fin}\left(\left(4: \mathbb{N}\right)\right), \operatorname{Fin}\left(\left(4: \mathbb{N}\right)\right), \mathbb{C}\right)\right) = \left(\left(\operatorname{Matrix.single}\left(\left(0: \operatorname{Fin}\left(\left(4: \mathbb{N}\right)\right)\right), \left(2: \operatorname{Fin}\left(\left(4: \mathbb{N}\right)\right)\right), \left(1: \mathbb{C}\right)\right)\right) + \left(\operatorname{Matrix.single}\left(\left(1: \operatorname{Fin}\left(\left(4: \mathbb{N}\right)\right)\right), \left(3: \operatorname{Fin}\left(\left(4: \mathbb{N}\right)\right)\right), \left(1: \mathbb{C}\right)\right)\right)\right); \left(\operatorname{let} \left(v: \operatorname{Matrix}\left(\operatorname{Fin}\left(\left(4: \mathbb{N}\right)\right), \operatorname{Fin}\left(\left(4: \mathbb{N}\right)\right), \mathbb{C}\right)\right) = \left(\left(\operatorname{Matrix.single}\left(\left(0: \operatorname{Fin}\left(\left(4: \mathbb{N}\right)\right)\right), \left(1: \operatorname{Fin}\left(\left(4: \mathbb{N}\right)\right)\right), \left(1: \mathbb{C}\right)\right)\right) - \left(\operatorname{Matrix.single}\left(\left(2: \operatorname{Fin}\left(\left(4: \mathbb{N}\right)\right)\right), \left(3: \operatorname{Fin}\left(\left(4: \mathbb{N}\right)\right)\right), \left(1: \mathbb{C}\right)\right)\right)\right); \operatorname{Submodule.span}\left(\mathbb{C}, \left\{u, v, \left(u\right) \cdot \left(v\right)\right\}\right)\right)\right)$$

*Formalization.* `D5/S3/HilbertOperators/ReversibleFourByFourNonuniqueness.carAlgebra` (`✓ std3`).

*Citation.* David P. Blecher (2025). *Commutativity of operator algebras*. DOI: [10.1016/j.exmath.2025.125742](https://doi.org/10.1016/j.exmath.2025.125742). URL: <https://arxiv.org/abs/2509.17673v2>.

*Commentary.*

Matrix.single i j 1 is the matrix unit with its only nonzero entry at row i, column j. Indices start at zero, so u = e₀₂ + e₁₃ and v = e₀₁ − e₂₃ are precisely the matrices U = e₁₃ + e₂₄ and V = e₁₂ − e₃₄ of 3commfarx.tex, lines 647–653. The subspace is their complex span together with their product uv. The displayed local definitions bind u and v before taking that span.

**Definition 1.5 (Equality under unitary conjugation).**

$$\forall \left(b: \operatorname{Submodule}\left(\mathbb{C}, \operatorname{Matrix}\left(\operatorname{Fin}\left(\left(4: \mathbb{N}\right)\right), \operatorname{Fin}\left(\left(4: \mathbb{N}\right)\right), \mathbb{C}\right)\right)\right), \left(\forall \left(c: \operatorname{Submodule}\left(\mathbb{C}, \operatorname{Matrix}\left(\operatorname{Fin}\left(\left(4: \mathbb{N}\right)\right), \operatorname{Fin}\left(\left(4: \mathbb{N}\right)\right), \mathbb{C}\right)\right)\right), \left(\left(\operatorname{D5.S3.HilbertOperators.ReversibleFourByFourNonuniqueness.UnitarilyEquivalent}\left(b, c\right)\right) \Leftrightarrow \left(\exists \left(q: \operatorname{CoeSort.coe}\left(\operatorname{Matrix.unitaryGroup}\left(\operatorname{Fin}\left(\left(4: \mathbb{N}\right)\right), \mathbb{C}\right)\right)\right), \left(\forall \left(x: \operatorname{Matrix}\left(\operatorname{Fin}\left(\left(4: \mathbb{N}\right)\right), \operatorname{Fin}\left(\left(4: \mathbb{N}\right)\right), \mathbb{C}\right)\right), \left(\left(x \in b\right) \Leftrightarrow \left(\left(\left(\operatorname{star}\left(\left(\operatorname{Subtype.val}\left(q\right): \operatorname{Matrix}\left(\operatorname{Fin}\left(\left(4: \mathbb{N}\right)\right), \operatorname{Fin}\left(\left(4: \mathbb{N}\right)\right), \mathbb{C}\right)\right)\right)\right) \cdot \left(x\right)\right) \cdot \left(\left(\operatorname{Subtype.val}\left(q\right): \operatorname{Matrix}\left(\operatorname{Fin}\left(\left(4: \mathbb{N}\right)\right), \operatorname{Fin}\left(\left(4: \mathbb{N}\right)\right), \mathbb{C}\right)\right)\right) \in c\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/HilbertOperators/ReversibleFourByFourNonuniqueness.UnitarilyEquivalent` (`✓ std3`).

*Citation.* David P. Blecher (2025). *Commutativity of operator algebras*. DOI: [10.1016/j.exmath.2025.125742](https://doi.org/10.1016/j.exmath.2025.125742). URL: <https://arxiv.org/abs/2509.17673v2>.

*Commentary.*

There is a unitary matrix q such that x belongs to b exactly when qᴴxq belongs to c, for every ambient matrix x. The quantified type consists of the elements of the unitary group. Subtype.val explicitly extracts the matrix from q, and star is its adjoint. Thus conjugation carries b onto c, rather than merely into c. This is unitary equivalence as used in the conjecture in 3commfarx.tex, line 684; replacing q by its adjoint reverses the orientation.

**Definition 1.6 (The proposed unitary uniqueness).**

$$\left(\operatorname{D5.S3.HilbertOperators.ReversibleFourByFourNonuniqueness.claim}\right) \Leftrightarrow \left(\forall \left(b: \operatorname{Submodule}\left(\mathbb{C}, \operatorname{Matrix}\left(\operatorname{Fin}\left(\left(4: \mathbb{N}\right)\right), \operatorname{Fin}\left(\left(4: \mathbb{N}\right)\right), \mathbb{C}\right)\right)\right), \left(\left(\operatorname{D5.S3.HilbertOperators.ReversibleFourByFourNonuniqueness.IsMatrixAlgebra}\left(b\right)\right) \to \left(\left(\operatorname{D5.S3.HilbertOperators.ReversibleFourByFourNonuniqueness.IsNoncommutative}\left(b\right)\right) \to \left(\left(\operatorname{D5.S3.HilbertOperators.ReversibleFourByFourNonuniqueness.IsReversible}\left(b\right)\right) \to \left(\operatorname{D5.S3.HilbertOperators.ReversibleFourByFourNonuniqueness.UnitarilyEquivalent}\left(b, \operatorname{D5.S3.HilbertOperators.ReversibleFourByFourNonuniqueness.carAlgebra}\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/HilbertOperators/ReversibleFourByFourNonuniqueness.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* David P. Blecher (2025). *Commutativity of operator algebras*. DOI: [10.1016/j.exmath.2025.125742](https://doi.org/10.1016/j.exmath.2025.125742). URL: <https://arxiv.org/abs/2509.17673v2>.

*Commentary.*

Every multiplicatively closed, noncommutative complex subspace b of the four-by-four matrices satisfying the displayed reversibility condition would be unitarily equivalent to carAlgebra. This is the finite-matrix representation reading of the conjecture in 3commfarx.tex, line 684. The source's conjecture implies this assertion because this reversibility condition implies the source's abstract reversibility.

**Theorem 1.7 (A weighted algebra separates the unitary classes).**

$$\neg \left(\operatorname{D5.S3.HilbertOperators.ReversibleFourByFourNonuniqueness.claim}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/HilbertOperators/ReversibleFourByFourNonuniqueness.result` (`✓ std3`). ∎

*Resolves.* `Problems/blecher-2025-reversible-four-by-four-nonuniqueness` (refuted) by `D5/S3/HilbertOperators/ReversibleFourByFourNonuniqueness.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"blecher-2025-reversible-four-by-four-nonuniqueness","declaration_gid":"D5/S3/HilbertOperators/ReversibleFourByFourNonuniqueness.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* David P. Blecher (2025). *Commutativity of operator algebras*. DOI: [10.1016/j.exmath.2025.125742](https://doi.org/10.1016/j.exmath.2025.125742). URL: <https://arxiv.org/abs/2509.17673v2>.

*Commentary.*

For complex t, a, b and c, write F(t,a,b,c) for the matrix whose only possibly nonzero entries are (0,1) = tb, (0,2) = ta, (0,3) = c, (1,3) = a and (2,3) = −b. Put U₂ = F(2,1,0,0), V₂ = F(2,0,1,0), W = F(2,0,0,1) = e₀₃, and B = spanℂ{U₂,V₂,W}. Entrywise expansion gives aF(t,1,0,0) + bF(t,0,1,0) + cF(t,0,0,1) = F(t,a,b,c). Consequently the elements of B are exactly F(2,a,b,c).

Multiplication gives F(t,a,b,c)F(t,d,e,f) = F(t,0,0,t(bd − ae)). The matrices u and v defining carAlgebra are F(1,1,0,0) and F(1,0,1,0); their product is −W. Changing the sign of the third span coefficient shows that the elements of carAlgebra are exactly F(1,a,b,c).

The product identity first proves that B is closed under multiplication, since every product is a scalar multiple of W. Interchanging the two factors negates bd − ae, so xy = −yx for every x and y in B. Moreover U₂V₂ = −2W and V₂U₂ = 2W. Their (0,3) entries are −2 and 2, proving noncommutativity. For reversibility take m = 4 and ρ = −id on the ambient matrix space. Anticommutation gives ρ(yx) = −yx = xy = ρ(x)ρ(y). Applying ρ to every block negates the assembled matrix, so its norm is unchanged at every natural block size.

For a unitary q let T(X) = qᴴXq, where Xᴴ denotes the adjoint. The current proof expresses T as Unitary.conjStarAlgAut and applies Matrix.trace_units_conj' after transporting products, adjoints and squares. Thus Δ(X) = 2tr((XXᴴ)²) − tr(XXᴴ)² is invariant under T. Direct expansion gives Δ(F(1,a,b,0)) = 0 for all complex a and b, whereas Δ(U₂) = 9.

Suppose T carries B into carAlgebra. Write T(U₂) = F(1,a,b,c) and T(V₂) = F(1,d,e,f). Since W = (1/2)V₂U₂, multiplicativity and complex linearity give T(W) = ((ea − db)/2)W. Denote this coefficient by t. It is nonzero: otherwise injectivity of T would give W = 0, contradicting its (0,3) entry, which is one.

Next write T(U₂) = F(1,a,b,c) again. The equality tr(WᴴU₂) = 0 is preserved by T, so tr(T(W)ᴴT(U₂)) = 0. Substituting T(W) = tW and expanding the trace gives conj(t)c = 0. Since t is nonzero, c = 0. Thus T(U₂) = F(1,a,b,0).

A unitary equivalence between B and carAlgebra would give the inclusion just used. Invariance of Δ would then identify Δ(F(1,a,b,0)) with Δ(U₂), forcing 0 = 9. Hence those two subspaces are not unitarily equivalent. Finally, applying claim to B, with its multiplicative closure, noncommutativity and reversibility established above, would supply exactly that impossible equivalence. Therefore claim is false.

## References

- Truth anchor: `D5/S3/HilbertOperators/ReversibleFourByFourNonuniqueness.IsMatrixAlgebra`
- Truth anchor: `D5/S3/HilbertOperators/ReversibleFourByFourNonuniqueness.IsNoncommutative`
- Truth anchor: `D5/S3/HilbertOperators/ReversibleFourByFourNonuniqueness.IsReversible`
- Truth anchor: `D5/S3/HilbertOperators/ReversibleFourByFourNonuniqueness.UnitarilyEquivalent`
- Truth anchor: `D5/S3/HilbertOperators/ReversibleFourByFourNonuniqueness.carAlgebra`
- Truth anchor: `D5/S3/HilbertOperators/ReversibleFourByFourNonuniqueness.claim`
- Truth anchor: `D5/S3/HilbertOperators/ReversibleFourByFourNonuniqueness.result`
