# A positive answer to Question 14's final interrogative

## Abstract

Finite full automorphisms coexist with infinitely many natural bases modulo arbitrary permutation and independent nonzero scaling.

Question 14 in section 2.2.2 of arXiv:2610.22248v1 asks: Describe the set of natural bases (up to permutation and scaling) of a non-degenerate evolution algebra. When is it finite? Can it be infinite for an algebra whose automorphism group is finite? The result answers the complete final sentence only. The survey works over a field and assumes finite dimension unless stated otherwise. Complex scalars are permitted; no assertion for every field is needed. Non-degenerate means the annihilator is zero. Aut means all invertible linear maps preserving multiplication, or the field-valued points of the automorphism group scheme, rather than a chosen monomial subgroup.

**Definition 1.1 (All actual natural bases in the canonical two-element presentation).**

$$\forall V \in Type,\; [\operatorname{AddCommGroup}\left(V\right)] [\operatorname{Module}\left(Complex, V\right)], \forall m \in \operatorname{LinearMap}\left(Complex, V, \operatorname{LinearMap}\left(Complex, V, V\right)\right),\; \operatorname{NaturalBasis}\left(m\right) = \{b:\operatorname{Basis}\left(\operatorname{Fin}\left(2\right), Complex, V\right) \mid \forall i \in \operatorname{Fin}\left(2\right),\; \forall j \in \operatorname{Fin}\left(2\right),\; i \ne j \Rightarrow m\left(b\left(i\right), b\left(j\right)\right) = 0\}$$

*Formalization.* `D5/S3/QuadraticForms/EvolutionAlgebras/FiniteAutomorphismsInfiniteNaturalBases.NaturalBasis` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ivan Kaygorodov; Cándido Martín González; Antonio Viruel (2026). *Evolution algebras: a survey of results and a list of open problems*. DOI: [10.48550/arXiv.2610.22248](https://doi.org/10.48550/arXiv.2610.22248). URL: <https://arxiv.org/abs/2610.22248v1>.

*Acknowledgement.* Maria Inez Cardoso Goncalves; Daniel Goncalves; Dolores Martin Barquero; Candido Martin Gonzalez; Mercedes Siles Molina (2018). *Squares and associative representations of two dimensional evolution algebras*. DOI: [10.48550/arXiv.1807.02362](https://doi.org/10.48550/arXiv.1807.02362). URL: <https://arxiv.org/abs/1807.02362v1>.

*Commentary.*

An element contains a Module.Basis, including linear independence and spanning, and the zero mixed-product proof. It is not merely an ordered pair of vectors. For the witness the dimension is two. Every vector-space basis is finite by Module.Finite.finite_basis and has exactly two elements by Module.finrank_eq_card_basis. It can be reindexed by Fin 2 using Basis.reindex. Any two such choices differ by a permutation of Fin 2. Thus after the permutation quotient this canonical indexing represents the source domain of actual bases; it adds no identification and omits no basis. The theorem uses this presentation, without claiming a separately compiled equivalence across all possible index types.

**Definition 1.2 (Exactly permutation and independent nonzero rescaling).**

$$\forall V \in Type,\; [\operatorname{AddCommGroup}\left(V\right)] [\operatorname{Module}\left(Complex, V\right)], \forall m \in \operatorname{LinearMap}\left(Complex, V, \operatorname{LinearMap}\left(Complex, V, V\right)\right),\; \forall b \in \operatorname{NaturalBasis}\left(m\right),\; \forall c \in \operatorname{NaturalBasis}\left(m\right),\; \operatorname{Rel}\left(\operatorname{basisSetoid}\left(m\right), b, c\right) \Leftrightarrow \left(\exists sigma \in \operatorname{Perm}\left(\operatorname{Fin}\left(2\right)\right),\; \exists u \in \operatorname{Fin}\left(2\right) \to \operatorname{Units}\left(Complex\right),\; \forall i \in \operatorname{Fin}\left(2\right),\; b\left(i\right) = u\left(i\right) \cdot c\left(sigma\left(i\right)\right)\right)$$

*Formalization.* `D5/S3/QuadraticForms/EvolutionAlgebras/FiniteAutomorphismsInfiniteNaturalBases.basisSetoid` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ivan Kaygorodov; Cándido Martín González; Antonio Viruel (2026). *Evolution algebras: a survey of results and a list of open problems*. DOI: [10.48550/arXiv.2610.22248](https://doi.org/10.48550/arXiv.2610.22248). URL: <https://arxiv.org/abs/2610.22248v1>.

*Acknowledgement.* Maria Inez Cardoso Goncalves; Daniel Goncalves; Dolores Martin Barquero; Candido Martin Gonzalez; Mercedes Siles Molina (2018). *Squares and associative representations of two dimensional evolution algebras*. DOI: [10.48550/arXiv.1807.02362](https://doi.org/10.48550/arXiv.1807.02362). URL: <https://arxiv.org/abs/1807.02362v1>.

*Commentary.*

Every permutation is allowed, and each vector has its own arbitrary complex unit. Over a field each nonzero scalar yields Units.mk0 and every unit has nonzero value, so these are exactly the independent nonzero scalars in the source. Identity, inverse permutation with inverse units, and composition with product units prove reflexivity, symmetry and transitivity. Quotient identifies precisely this relation. There is no quotient by algebra automorphisms, no restriction to real rescalings, and no normalization of a basis before taking the quotient.

**Definition 1.3 (The older algebra with one-dimensional square).**

$$\forall x \in \operatorname{Prod}\left(Complex, Complex\right),\; \forall y \in \operatorname{Prod}\left(Complex, Complex\right),\; mu\left(x, y\right) = \operatorname{pair}\left(\operatorname{fst}\left(x\right) \cdot \operatorname{fst}\left(y\right) + \operatorname{snd}\left(x\right) \cdot \operatorname{snd}\left(y\right), 0\right)$$

*Formalization.* `D5/S3/QuadraticForms/EvolutionAlgebras/FiniteAutomorphismsInfiniteNaturalBases.mu` (`✓ std3`).

*Citation.* Maria Inez Cardoso Goncalves; Daniel Goncalves; Dolores Martin Barquero; Candido Martin Gonzalez; Mercedes Siles Molina (2018). *Squares and associative representations of two dimensional evolution algebras*. DOI: [10.48550/arXiv.1807.02362](https://doi.org/10.48550/arXiv.1807.02362). URL: <https://arxiv.org/abs/1807.02362v1>.

*Commentary.*

The carrier is Complex times Complex and mu is complex linear in each argument; neither coefficient is conjugated. Its standard coordinate basis has e(0)^2=e(0), e(1)^2=e(0), and zero mixed products. The coordinate e(0) is u and e(1) is v in the 2018 algebra A_(8,1); the survey's Proposition 14 at n=1 uses the order (e(1),u). The square lies in the first coordinate line and contains e(0), so the algebra is non-perfect. Testing a vector against e(0) and e(1) proves that its annihilator is zero. Isotropic square-zero vectors are not confused with annihilator elements. This is a bilinear, possibly nonassociative algebra, and no associative AlgEquiv is used.

The full-group proof starts with an arbitrary member of EvolutionAutomorphismControl.Aut mu, whose defining subgroup contains every invertible complex-linear multiplication-preserving map. The image of e(0) is a nonzero idempotent and must equal e(0). Its mixed product with the image of e(1) forces that image's first coordinate to vanish. Preservation of e(1)^2=e(0) forces its second coordinate d to satisfy d*d=1. Hence d is either 1 or -1, and linearity determines the map everywhere. Its value of d gives an injection into Bool, proving finiteness. This full-group classification is a published ingredient.

For every natural number n, let t=n+1 and take u(n)=(1,t), v(n)=(-t,1). Their mixed product is zero. The matrix with these columns has determinant 1+t*t, a positive natural integer embedded in Complex, hence nonzero. The explicit inverse sends (x,y) to ((x+t*y)/(1+t*t),(-t*x+y)/(1+t*t)); both inverse laws are proved. Mapping the standard basis along this linear equivalence therefore constructs an actual natural basis for every n.

Suppose the classes for n and m coincide, and put s=m+1. The exact quotient relation sends u(n) to an arbitrary complex scalar multiple of either u(m) or v(m). In the first case the first coordinates force the scalar to be one, then t=s and n=m. In the swapped case the second coordinates force the scalar to be t, and the first coordinates give t*s=-1. This contradicts the nonzero positive natural integer t*s+1 embedded in Complex. Thus n maps injectively into the quotient of all natural bases. Infinite.of_injective gives the required infinite quotient, rather than just infinitely many ordered or rescaled representatives.

**Theorem 1.4 (The full source-faithful existence conjunction).**

$$\exists m \in \operatorname{LinearMap}\left(Complex, \operatorname{Prod}\left(Complex, Complex\right), \operatorname{LinearMap}\left(Complex, \operatorname{Prod}\left(Complex, Complex\right), \operatorname{Prod}\left(Complex, Complex\right)\right)\right),\; \operatorname{finrank}\left(Complex, \operatorname{Prod}\left(Complex, Complex\right)\right) = 2 \land \left(\left(\forall x \in \operatorname{Prod}\left(Complex, Complex\right),\; \forall y \in \operatorname{Prod}\left(Complex, Complex\right),\; m\left(x, y\right) = m\left(y, x\right)\right) \land \left(\left(\forall x \in \operatorname{Prod}\left(Complex, Complex\right),\; \left(\forall y \in \operatorname{Prod}\left(Complex, Complex\right),\; m\left(x, y\right) = 0\right) \Rightarrow x = 0\right) \land \left(\operatorname{Nonempty}\left(\operatorname{NaturalBasis}\left(m\right)\right) \land \left(\operatorname{Finite}\left(\operatorname{EvolutionAutomorphismControl}.\operatorname{Aut}\left(m\right)\right) \land \operatorname{Infinite}\left(\operatorname{Quotient}\left(\operatorname{basisSetoid}\left(m\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/EvolutionAlgebras/FiniteAutomorphismsInfiniteNaturalBases.result` (`✓ std3`). ∎

*Resolves.* `Problems/kaygorodov-martin-gonzalez-viruel-2026-finite-aut-infinite-natural-bases` (proved) by `D5/S3/QuadraticForms/EvolutionAlgebras/FiniteAutomorphismsInfiniteNaturalBases.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"kaygorodov-martin-gonzalez-viruel-2026-finite-aut-infinite-natural-bases","declaration_gid":"D5/S3/QuadraticForms/EvolutionAlgebras/FiniteAutomorphismsInfiniteNaturalBases.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Ivan Kaygorodov; Cándido Martín González; Antonio Viruel (2026). *Evolution algebras: a survey of results and a list of open problems*. DOI: [10.48550/arXiv.2610.22248](https://doi.org/10.48550/arXiv.2610.22248). URL: <https://arxiv.org/abs/2610.22248v1>.

*Acknowledgement.* Maria Inez Cardoso Goncalves; Daniel Goncalves; Dolores Martin Barquero; Candido Martin Gonzalez; Mercedes Siles Molina (2018). *Squares and associative representations of two dimensional evolution algebras*. DOI: [10.48550/arXiv.1807.02362](https://doi.org/10.48550/arXiv.1807.02362). URL: <https://arxiv.org/abs/1807.02362v1>.

*Commentary.*

The witness is the published mu on the two-dimensional complex space. The six conjuncts state dimension two, commutativity, zero annihilator, existence of an actual natural basis, finiteness of the full linear multiplication-automorphism group, and infinitude of the exact natural-basis quotient. Complex is a permitted field; the LinearMap types supply bilinearity.

The 2018 classification, Lemma 3.15 and section 5.1, already provides this algebra, the arbitrary-natural-basis determinant and orthogonality equations, and its finite full automorphism group. Non-degenerate evolution algebras, arXiv:2303.00862v1, Theorem 26 and Remark 29, gives the same finite-group ingredient. Natural families in evolution algebras, arXiv:2006.14460v1, Corollary 2.13 and Proposition 2.16, supplies structural basis results. Solenoids in automorphism groups of evolution algebras, arXiv:2505.14584v1, Example 6.3, gives an older infinite quotient example with nonzero annihilator and infinite full group. These ingredients receive prior credit. No prior published whole answer was found in the bounded search; worldwide absence and priority remain unverified. Authenticated code search was unavailable, so no search-complete claim is made. The general description and finiteness criterion asked in Q14's first two sentences remain outside this result.

## References

- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/FiniteAutomorphismsInfiniteNaturalBases.NaturalBasis`
- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/FiniteAutomorphismsInfiniteNaturalBases.basisSetoid`
- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/FiniteAutomorphismsInfiniteNaturalBases.mu`
- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/FiniteAutomorphismsInfiniteNaturalBases.result`
- Dependency: [D5/S3/QuadraticForms/EvolutionAlgebras/EvolutionAutomorphismControl](EvolutionAutomorphismControl.md)
