# Refutation of Labelle's Toda numerator unimodality conjecture

## Abstract

Labelle's recursively defined Toda specialization has a non-unimodal numerator in type C2 at the positive-root coordinates (2,2).

**Definition 1.1 (Normalized finite-type Cartan data).**

$$\forall r : \mathbb{N}, \operatorname{CartanDatum}\left(r\right) = \{(C, G, d) : ((\operatorname{Matrix}\left(\operatorname{Fin}\left(r\right), \operatorname{Fin}\left(r\right), \mathbb{Z}\right)) \times (\operatorname{Matrix}\left(\operatorname{Fin}\left(r\right), \operatorname{Fin}\left(r\right), \mathbb{Z}\right))) \times ((\operatorname{Fin}\left(r\right)) \to (\mathbb{N})) \mid (\forall i : \operatorname{Fin}\left(r\right), C\left(i, i\right) = 2) \land ((\forall i : \operatorname{Fin}\left(r\right), \forall j : \operatorname{Fin}\left(r\right), (i \ne j) \Rightarrow (C\left(i, j\right) \le 0)) \land ((\forall i : \operatorname{Fin}\left(r\right), \forall j : \operatorname{Fin}\left(r\right), (C\left(i, j\right) = 0) \Leftrightarrow (C\left(j, i\right) = 0)) \land ((\forall i : \operatorname{Fin}\left(r\right), \forall j : \operatorname{Fin}\left(r\right), G\left(i, j\right) = G\left(j, i\right)) \land ((\forall i : \operatorname{Fin}\left(r\right), 0 < d\left(i\right)) \land ((\forall i : \operatorname{Fin}\left(r\right), \exists j : \operatorname{Fin}\left(r\right), (SimpleGraph.Reachable\left(SimpleGraph.fromRel\left(\Lambda u : \operatorname{Fin}\left(r\right), \Lambda v : \operatorname{Fin}\left(r\right), C\left(u, v\right) \ne 0\right), i, j\right)) \land (d\left(j\right) = 1)) \land ((\forall x : (\operatorname{Fin}\left(r\right)) \to (\mathbb{Q}), (x \ne 0) \Rightarrow (0 < \operatorname{sum}\left(\operatorname{univ}\left(\operatorname{Fin}\left(r\right)\right), (\Lambda i : \operatorname{Fin}\left(r\right), \operatorname{sum}\left(\operatorname{univ}\left(\operatorname{Fin}\left(r\right)\right), (\Lambda j : \operatorname{Fin}\left(r\right), x\left(i\right) \cdot \operatorname{algebraMap}\left(\mathbb{Z}, \mathbb{Q}\right)\left(G\left(i, j\right)\right) \cdot x\left(j\right))\right))\right))) \land ((\forall i : \operatorname{Fin}\left(r\right), G\left(i, i\right) = 2 \cdot \operatorname{Int}.\operatorname{ofNat}\left(d\left(i\right)\right)) \land ((\forall i : \operatorname{Fin}\left(r\right), \forall j : \operatorname{Fin}\left(r\right), G\left(i, j\right) = \operatorname{Int}.\operatorname{ofNat}\left(d\left(i\right)\right) \cdot C\left(i, j\right)) \land (\forall \beta : (\operatorname{Fin}\left(r\right)) \to (\mathbb{Z}), \exists k : \mathbb{Z}, \operatorname{sum}\left(\operatorname{univ}\left(\operatorname{Fin}\left(r\right)\right), (\Lambda i : \operatorname{Fin}\left(r\right), \operatorname{sum}\left(\operatorname{univ}\left(\operatorname{Fin}\left(r\right)\right), (\Lambda j : \operatorname{Fin}\left(r\right), \beta\left(i\right) \cdot G\left(i, j\right) \cdot \beta\left(j\right))\right))\right) = k + k)))))))))\}$$

*Formalization.* `D5/S0/Certificates/Combinatorics/TodaSpecializationUnimodalityRefutation.CartanDatum` (`✓ std3`).

*Citation.* Labelle, A. (2025). *On a specialization of Toda eigenfunctions*. DOI: [10.48550/arXiv.2502.10655](https://doi.org/10.48550/arXiv.2502.10655). URL: <https://arxiv.org/abs/2502.10655v3>.

*Commentary.*

Section 1 fixes a split semisimple Lie algebra over Q and normalizes short roots to squared length 2. For every finite rank r, CartanDatum(r) encodes its finite-type symmetrizable generalized Cartan data. C and G are integer matrices on Fin(r), and d is a positive-integer function. The generalized Cartan axioms, symmetry and positive definiteness of G, G(i,i)=2d(i), and G(i,j)=d(i)C(i,j) are retained. Every index is connected in the Dynkin graph of nonzero off-diagonal Cartan entries to an index with d=1; this is vacuous at rank zero. The integral quadratic form is even on every integral coordinate vector. The tuple fields C,G,d correspond to cartan,gram,d; the displayed constraints correspond to every proof field.

**Definition 1.2 (The displayed q-factor).**

$$\forall r : \mathbb{N}, \forall D : \operatorname{CartanDatum}\left(r\right), \forall \alpha : (\operatorname{Fin}\left(r\right)) \to (\mathbb{N}), \operatorname{qFactor}\left(D, \alpha\right) = \operatorname{prod}\left(\operatorname{univ}\left(\operatorname{Fin}\left(r\right)\right), (\Lambda i : \operatorname{Fin}\left(r\right), \operatorname{prod}\left(\operatorname{range}\left(\alpha\left(i\right)\right), (\Lambda j : \mathbb{N}, 1 - \operatorname{RatFunc}.X^{\operatorname{d}\left(D\right)\left(i\right) \cdot \left(j + 1\right)})\right))\right)$$

*Formalization.* `D5/S0/Certificates/Combinatorics/TodaSpecializationUnimodalityRefutation.qFactor` (`✓ std3`).

*Citation.* Labelle, A. (2025). *On a specialization of Toda eigenfunctions*. DOI: [10.48550/arXiv.2502.10655](https://doi.org/10.48550/arXiv.2502.10655). URL: <https://arxiv.org/abs/2502.10655v3>.

*Commentary.*

Definition 1.1 defines (q)_alpha as the product over all simple-root coordinates of the factors 1-q^(d(i)j), with 1<=j<=alpha(i). The displayed nested finite products retain every coordinate at arbitrary finite rank. RatFunc.X is the indeterminate in RatFunc(Q). prod(s,f) multiplies f over s, univ(Fin(r)) is the complete coordinate index set, and range(a)={0,...,a-1}.

**Definition 1.3 (Half the invariant quadratic form).**

$$\forall r : \mathbb{N}, \forall D : \operatorname{CartanDatum}\left(r\right), \forall \alpha : (\operatorname{Fin}\left(r\right)) \to (\mathbb{N}), \operatorname{quad}\left(D, \alpha\right) = \frac{\operatorname{sum}\left(\operatorname{univ}\left(\operatorname{Fin}\left(r\right)\right), (\Lambda i : \operatorname{Fin}\left(r\right), \operatorname{sum}\left(\operatorname{univ}\left(\operatorname{Fin}\left(r\right)\right), (\Lambda j : \operatorname{Fin}\left(r\right), \operatorname{Int}.\operatorname{ofNat}\left(\alpha\left(i\right)\right) \cdot \operatorname{Int}.\operatorname{ofNat}\left(\alpha\left(j\right)\right) \cdot \operatorname{gram}\left(D\right)\left(i, j\right))\right))\right)}{2}$$

*Formalization.* `D5/S0/Certificates/Combinatorics/TodaSpecializationUnimodalityRefutation.quad` (`✓ std3`).

*Citation.* Labelle, A. (2025). *On a specialization of Toda eigenfunctions*. DOI: [10.48550/arXiv.2502.10655](https://doi.org/10.48550/arXiv.2502.10655). URL: <https://arxiv.org/abs/2502.10655v3>.

*Commentary.*

The exponent is literally the integer quotient of the Gram quadratic form (alpha,alpha) by 2. The datum supplies evenness for every integral coordinate vector, so this quotient is the exact integer half. Thus quad takes values in Z, with no conversion to a natural number. Powers of RatFunc.X in J use integer exponentiation. Int.ofNat casts the nonnegative root coordinates to Z. The displayed division by 2 is exact because its numerator is even.

**Definition 1.4 (Definition 1.1's fermionic recursion).**

$$\forall r : \mathbb{N}, \forall D : \operatorname{CartanDatum}\left(r\right), \forall \alpha : (\operatorname{Fin}\left(r\right)) \to (\mathbb{N}), \operatorname{J}\left(D, \alpha\right) = \operatorname{ite}\left(\alpha = 0, 1, \frac{1}{1 - \operatorname{RatFunc}.X^{\operatorname{quad}\left(D, \alpha\right)}} \cdot \operatorname{sum}\left(\operatorname{piFinset}\left((\Lambda i : \operatorname{Fin}\left(r\right), \operatorname{range}\left(\alpha\left(i\right) + 1\right))\right), (\Lambda \beta : (\operatorname{Fin}\left(r\right)) \to (\mathbb{N}), \operatorname{ite}\left((\forall i : \operatorname{Fin}\left(r\right), \beta\left(i\right) \le \alpha\left(i\right)) \land (\beta \ne \alpha), \frac{\operatorname{RatFunc}.X^{\operatorname{quad}\left(D, \beta\right)}}{\operatorname{qFactor}\left(D, \alpha - \beta\right)} \cdot \operatorname{J}\left(D, \beta\right), 0\right))\right)\right)$$

*Formalization.* `D5/S0/Certificates/Combinatorics/TodaSpecializationUnimodalityRefutation.J` (`✓ std3`).

*Citation.* Labelle, A. (2025). *On a specialization of Toda eigenfunctions*. DOI: [10.48550/arXiv.2502.10655](https://doi.org/10.48550/arXiv.2502.10655). URL: <https://arxiv.org/abs/2502.10655v3>.

*Commentary.*

Definition 1.1 defines J_alpha in Q(q) for every nonnegative root-lattice coordinate vector. Equation (2) moves the beta=alpha term to the left for nonzero alpha and divides by 1-q^((alpha,alpha)/2). The displayed ite and finite sum are that recursion, with J(D,0)=1. piFinset forms the finite box of all vectors beta with 0<=beta(i)<=alpha(i) in every coordinate. The summand excludes beta=alpha; alpha-beta is pointwise natural subtraction, equal to the root-lattice difference under these bounds. sum(s,f) adds f over s. Every recursive argument has strictly smaller total coordinate height. The definitions contain no certificate values.

**Definition 1.5 (Weak unimodality).**

$$\forall p : \operatorname{Polynomial}\left(\mathbb{Q}\right), (\operatorname{Unimodal}\left(p\right)) \Leftrightarrow (\exists m : \mathbb{N}, (m \le \operatorname{natDegree}\left(p\right)) \land ((\forall i : \mathbb{N}, (i < m) \Rightarrow (\operatorname{coeff}\left(p, i\right) \le \operatorname{coeff}\left(p, i + 1\right))) \land (\forall i : \mathbb{N}, ((m \le i) \land (i < \operatorname{natDegree}\left(p\right))) \Rightarrow (\operatorname{coeff}\left(p, i + 1\right) \le \operatorname{coeff}\left(p, i\right)))))$$

*Formalization.* `D5/S0/Certificates/Combinatorics/TodaSpecializationUnimodalityRefutation.Unimodal` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Labelle, A. (2025). *On a specialization of Toda eigenfunctions*. DOI: [10.48550/arXiv.2502.10655](https://doi.org/10.48550/arXiv.2502.10655). URL: <https://arxiv.org/abs/2502.10655v3>.

*Commentary.*

A polynomial is unimodal when its finite coefficient list a(0),...,a(n), with n=natDegree(p), weakly increases up to a peak m and weakly decreases thereafter. The peak lies between 0 and n; decreasing comparisons stop at i<n. This definition applies to signed coefficients as well as nonnegative coefficients and imposes no comparison with the zero tail beyond the degree.

**Definition 1.6 (The C2 datum).**

$$(\forall i : \operatorname{Fin}\left(2\right), \forall j : \operatorname{Fin}\left(2\right), \operatorname{cartan}\left(\operatorname{c2}\right)\left(i, j\right) = \operatorname{ite}\left(i = j, 2, \operatorname{ite}\left(i = 0, -2, -1\right)\right)) \land ((\forall i : \operatorname{Fin}\left(2\right), \forall j : \operatorname{Fin}\left(2\right), \operatorname{gram}\left(\operatorname{c2}\right)\left(i, j\right) = \operatorname{ite}\left(i \ne j, -2, \operatorname{ite}\left(i = 0, 2, 4\right)\right)) \land (\forall i : \operatorname{Fin}\left(2\right), \operatorname{d}\left(\operatorname{c2}\right)\left(i\right) = \operatorname{ite}\left(i = 0, 1, 2\right)))$$

*Formalization.* `D5/S0/Certificates/Combinatorics/TodaSpecializationUnimodalityRefutation.c2` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Labelle, A. (2025). *On a specialization of Toda eigenfunctions*. DOI: [10.48550/arXiv.2502.10655](https://doi.org/10.48550/arXiv.2502.10655). URL: <https://arxiv.org/abs/2502.10655v3>.

*Commentary.*

The first simple root is short. The Cartan matrix is [[2,−2],[−1,2]], the Gram matrix is [[2,−2],[−2,4]], and d=(1,2). Every CartanDatum field is satisfied. In particular, its quadratic form is 2(x−y)²+2y², strictly positive off the origin. This is the finite reduced crystallographic type C2, the root datum of the split semisimple Lie algebra sp4 over Q.

**Definition 1.7 (Labelle, Conjecture 7.3).**

$$(\operatorname{claim}) \Leftrightarrow (\forall r : \mathbb{N}, \forall D : \operatorname{CartanDatum}\left(r\right), \forall \alpha : (\operatorname{Fin}\left(r\right)) \to (\mathbb{N}), \exists p : \operatorname{Polynomial}\left(\mathbb{Q}\right), (\operatorname{algebraMap}\left(\operatorname{Polynomial}\left(\mathbb{Q}\right), \operatorname{RatFunc}\left(\mathbb{Q}\right)\right)\left(p\right) = \operatorname{qFactor}\left(D, \alpha\right)^{2} \cdot \operatorname{J}\left(D, \alpha\right)) \land (\operatorname{Unimodal}\left(p\right)))$$

*Formalization.* `D5/S0/Certificates/Combinatorics/TodaSpecializationUnimodalityRefutation.claim` (`✓ std3`).

*Citation.* Labelle, A. (2025). *On a specialization of Toda eigenfunctions*. DOI: [10.48550/arXiv.2502.10655](https://doi.org/10.48550/arXiv.2502.10655). URL: <https://arxiv.org/abs/2502.10655v3>.

*Commentary.*

Conjecture 7.3 states: The polynomial (q)_alpha^2 J_alpha is unimodal. The encoding quantifies over every finite rank r, every normalized finite-type CartanDatum(r), and every nonnegative coordinate vector alpha:Fin(r)->N. The existential polynomial p has image qFactor(D,alpha)^2 J(D,alpha) under the canonical algebra map Q[X] to RatFunc(Q). Injectivity uniquely identifies p with the source polynomial, so its coefficients cannot be changed by the choice of representation.

**Theorem 1.8 (Refutation in type C2 at (2,2)).**

$$\neg \operatorname{claim}$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/Combinatorics/TodaSpecializationUnimodalityRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/labelle-2025-toda-numerator-unimodality-refutation` (refuted) by `D5/S0/Certificates/Combinatorics/TodaSpecializationUnimodalityRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"labelle-2025-toda-numerator-unimodality-refutation","declaration_gid":"D5/S0/Certificates/Combinatorics/TodaSpecializationUnimodalityRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Labelle, A. (2025). *On a specialization of Toda eigenfunctions*. DOI: [10.48550/arXiv.2502.10655](https://doi.org/10.48550/arXiv.2502.10655). URL: <https://arxiv.org/abs/2502.10655v3>.

*Commentary.*

The recursive J values are verified at all nine pairs 0≤a,b≤2, in increasing height, by clearing nonzero denominators. At (2,2), multiplying J by qFactor² gives 1+q+3q²+2q³+5q⁴+2q⁵+3q⁶+q⁷+q⁸. Injectivity of the polynomial algebra map identifies any p in claim with this polynomial. Its coefficients at degrees 2,3,4 are 3,2,5, a strict valley. A peak at or before degree 2 would require 5≤2 on the decreasing side; a later peak would require 3≤2 on the increasing side. Both are impossible. The type-A results and the general positivity conjecture are outside this refutation.

## References

- Truth anchor: `D5/S0/Certificates/Combinatorics/TodaSpecializationUnimodalityRefutation.CartanDatum`
- Truth anchor: `D5/S0/Certificates/Combinatorics/TodaSpecializationUnimodalityRefutation.J`
- Truth anchor: `D5/S0/Certificates/Combinatorics/TodaSpecializationUnimodalityRefutation.Unimodal`
- Truth anchor: `D5/S0/Certificates/Combinatorics/TodaSpecializationUnimodalityRefutation.c2`
- Truth anchor: `D5/S0/Certificates/Combinatorics/TodaSpecializationUnimodalityRefutation.claim`
- Truth anchor: `D5/S0/Certificates/Combinatorics/TodaSpecializationUnimodalityRefutation.qFactor`
- Truth anchor: `D5/S0/Certificates/Combinatorics/TodaSpecializationUnimodalityRefutation.quad`
- Truth anchor: `D5/S0/Certificates/Combinatorics/TodaSpecializationUnimodalityRefutation.result`
