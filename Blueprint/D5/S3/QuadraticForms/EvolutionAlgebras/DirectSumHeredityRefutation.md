# Direct sums and intrinsic evolution subalgebras

## Abstract

Hereditary evolution algebras need not have a hereditary direct sum.

**Definition 1.1 (inheritedProduct).**

$$\forall (K : \operatorname{Type}), ([\operatorname{Field}\left(K\right)] \forall (V : \operatorname{Type}), ([\operatorname{AddCommGroup}\left(V\right)] [\operatorname{Module}\left(K, V\right)] \forall (\mu : \operatorname{LinearMap}\left(K, V, \operatorname{LinearMap}\left(K, V, V\right)\right)), (\forall (S : \operatorname{Submodule}\left(K, V\right)), (\forall (closed : \forall (x : V), (\forall (y : V), ((x \in S) \Rightarrow ((y \in S) \Rightarrow (\mu\left(x, y\right) \in S))))), (\forall (x : S), (\forall (y : S), (\operatorname{inheritedProduct}\left(\mu, S, closed, x, y\right) = \langle\mu\left(\operatorname{val}\left(x\right), \operatorname{val}\left(y\right)\right), closed\left(\operatorname{val}\left(x\right), \operatorname{val}\left(y\right), \operatorname{Subtype}.\operatorname{property}\left(x\right), \operatorname{Subtype}.\operatorname{property}\left(y\right)\right)\rangle)))))))$$

*Formalization.* `D5/S3/QuadraticForms/EvolutionAlgebras/DirectSumHeredityRefutation.inheritedProduct` (`✓ std3`).

*Citation.* Ivan Kaygorodov; Cándido Martín González; Antonio Viruel (2026). *Evolution algebras: a survey of results and a list of open problems*. DOI: [10.48550/arXiv.2610.22248](https://doi.org/10.48550/arXiv.2610.22248). URL: <https://arxiv.org/abs/2610.22248v1>.

*Commentary.*

A multiplication-closed linear subspace has the restricted bilinear multiplication. The displayed subtype value includes the closure proof; no unit, associativity or extension of a basis is required.

**Definition 1.2 (Hereditary).**

$$\forall (K : \operatorname{Type}), ([\operatorname{Field}\left(K\right)] \forall (V : \operatorname{Type}), ([\operatorname{AddCommGroup}\left(V\right)] [\operatorname{Module}\left(K, V\right)] \forall (\mu : \operatorname{LinearMap}\left(K, V, \operatorname{LinearMap}\left(K, V, V\right)\right)), (\operatorname{Hereditary}\left(\mu\right) = \forall (S : \operatorname{Submodule}\left(K, V\right)), (\forall (closed : \forall (x : V), (\forall (y : V), ((x \in S) \Rightarrow ((y \in S) \Rightarrow (\mu\left(x, y\right) \in S))))), (\operatorname{DerivationAnnihilatorObstruction}.\operatorname{IsEvolutionAlgebra}\left(\operatorname{inheritedProduct}\left(\mu, S, closed\right)\right))))))$$

*Formalization.* `D5/S3/QuadraticForms/EvolutionAlgebras/DirectSumHeredityRefutation.Hereditary` (`✓ std3`).

*Citation.* Ivan Kaygorodov; Cándido Martín González; Antonio Viruel (2026). *Evolution algebras: a survey of results and a list of open problems*. DOI: [10.48550/arXiv.2610.22248](https://doi.org/10.48550/arXiv.2610.22248). URL: <https://arxiv.org/abs/2610.22248v1>.

*Commentary.*

Question 12 (Hereditary evolution algebras), §2.2.2, p. 22: “Characterise the evolution algebras all of whose subalgebras are evolution algebras. Is this property detected by the graphs? Is it preserved by tensor products and direct sums? What about ideals?” A subalgebra is a linear subspace closed under multiplication. Every such subspace, including zero and the whole space, must admit its own natural basis; that basis need not extend to the ambient algebra.

**Definition 1.3 (directSumProduct).**

$$\forall (K : \operatorname{Type}), ([\operatorname{Field}\left(K\right)] \forall (V : \operatorname{Type}), ([\operatorname{AddCommGroup}\left(V\right)] [\operatorname{Module}\left(K, V\right)] \forall (W : \operatorname{Type}), ([\operatorname{AddCommGroup}\left(W\right)] [\operatorname{Module}\left(K, W\right)] \forall (\mu : \operatorname{LinearMap}\left(K, V, \operatorname{LinearMap}\left(K, V, V\right)\right)), (\forall (\nu : \operatorname{LinearMap}\left(K, W, \operatorname{LinearMap}\left(K, W, W\right)\right)), (\forall (x : V \times W), (\forall (y : V \times W), (\operatorname{directSumProduct}\left(\mu, \nu, x, y\right) = (\mu\left(x.1, y.1\right), \nu\left(x.2, y.2\right)))))))))$$

*Formalization.* `D5/S3/QuadraticForms/EvolutionAlgebras/DirectSumHeredityRefutation.directSumProduct` (`✓ std3`).

*Citation.* Ivan Kaygorodov; Cándido Martín González; Antonio Viruel (2026). *Evolution algebras: a survey of results and a list of open problems*. DOI: [10.48550/arXiv.2610.22248](https://doi.org/10.48550/arXiv.2610.22248). URL: <https://arxiv.org/abs/2610.22248v1>.

*Commentary.*

The finite direct sum has componentwise multiplication. The displayed pair is the full value of the bilinear map at two vectors.

**Definition 1.4 (claim).**

$$\operatorname{claim} = \forall (K : \operatorname{Type}), ([\operatorname{Field}\left(K\right)] \forall (m : \mathbb{N}), (\forall (n : \mathbb{N}), (\forall (\mu : \operatorname{LinearMap}\left(K, (\operatorname{Fin}\left(m\right) \to K), \operatorname{LinearMap}\left(K, (\operatorname{Fin}\left(m\right) \to K), (\operatorname{Fin}\left(m\right) \to K)\right)\right)), (\forall (\nu : \operatorname{LinearMap}\left(K, (\operatorname{Fin}\left(n\right) \to K), \operatorname{LinearMap}\left(K, (\operatorname{Fin}\left(n\right) \to K), (\operatorname{Fin}\left(n\right) \to K)\right)\right)), ((\operatorname{DerivationAnnihilatorObstruction}.\operatorname{IsEvolutionAlgebra}\left(\mu\right)) \Rightarrow ((\operatorname{DerivationAnnihilatorObstruction}.\operatorname{IsEvolutionAlgebra}\left(\nu\right)) \Rightarrow ((\operatorname{Hereditary}\left(\mu\right)) \Rightarrow ((\operatorname{Hereditary}\left(\nu\right)) \Rightarrow (\operatorname{Hereditary}\left(\operatorname{directSumProduct}\left(\mu, \nu\right)\right))))))))))$$

*Formalization.* `D5/S3/QuadraticForms/EvolutionAlgebras/DirectSumHeredityRefutation.claim` (`✓ std3`).

*Citation.* Ivan Kaygorodov; Cándido Martín González; Antonio Viruel (2026). *Evolution algebras: a survey of results and a list of open problems*. DOI: [10.48550/arXiv.2610.22248](https://doi.org/10.48550/arXiv.2610.22248). URL: <https://arxiv.org/abs/2610.22248v1>.

*Commentary.*

Question 12 (Hereditary evolution algebras), §2.2.2, p. 22: “Characterise the evolution algebras all of whose subalgebras are evolution algebras. Is this property detected by the graphs? Is it preserved by tensor products and direct sums? What about ideals?” The formula selects the affirmative direct-sum assertion. The field K is arbitrary, and m and n range over all finite dimensions, including zero. The coordinate spaces are Fin m → K and Fin n → K. IsEvolutionAlgebra is the intrinsic predicate from DerivationAnnihilatorObstruction: a commutative bilinear multiplication with an actual Module.Basis of pairwise zero mixed products.

**Theorem 1.5 (result).**

$$\neg (\forall (K : \operatorname{Type}), ([\operatorname{Field}\left(K\right)] \forall (m : \mathbb{N}), (\forall (n : \mathbb{N}), (\forall (\mu : \operatorname{LinearMap}\left(K, (\operatorname{Fin}\left(m\right) \to K), \operatorname{LinearMap}\left(K, (\operatorname{Fin}\left(m\right) \to K), (\operatorname{Fin}\left(m\right) \to K)\right)\right)), (\forall (\nu : \operatorname{LinearMap}\left(K, (\operatorname{Fin}\left(n\right) \to K), \operatorname{LinearMap}\left(K, (\operatorname{Fin}\left(n\right) \to K), (\operatorname{Fin}\left(n\right) \to K)\right)\right)), ((\operatorname{DerivationAnnihilatorObstruction}.\operatorname{IsEvolutionAlgebra}\left(\mu\right)) \Rightarrow ((\operatorname{DerivationAnnihilatorObstruction}.\operatorname{IsEvolutionAlgebra}\left(\nu\right)) \Rightarrow ((\operatorname{Hereditary}\left(\mu\right)) \Rightarrow ((\operatorname{Hereditary}\left(\nu\right)) \Rightarrow (\operatorname{Hereditary}\left(\operatorname{directSumProduct}\left(\mu, \nu\right)\right)))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/EvolutionAlgebras/DirectSumHeredityRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/kmvq12` (refuted) by `D5/S3/QuadraticForms/EvolutionAlgebras/DirectSumHeredityRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"kmvq12","declaration_gid":"D5/S3/QuadraticForms/EvolutionAlgebras/DirectSumHeredityRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Ivan Kaygorodov; Cándido Martín González; Antonio Viruel (2026). *Evolution algebras: a survey of results and a list of open problems*. DOI: [10.48550/arXiv.2610.22248](https://doi.org/10.48550/arXiv.2610.22248). URL: <https://arxiv.org/abs/2610.22248v1>.

*Commentary.*

Over ℚ take dimensions four and three, with symmetric forms diag(1,−1,1,−1) and diag(1,−1,1). Multiply each scalar output by (1,1,0,0) and (1,1,0), respectively. The orthogonal-basis theorem applied on every closed subspace makes both factors hereditary. In their direct sum impose a₀ = a₁, b₀ = b₁ and b₂ = a₂ + a₃. Zero mixed products in a natural basis would force the sum and difference coordinate functionals to be proportional. The vectors ((0,0,1,0),(0,0,1)) and ((0,0,0,1),(0,0,1)) contradict that proportionality. Thus direct-sum preservation fails. Graph detection, tensor products, ideals, characteristic two, minimal dimensions and the full characterization remain separate questions.

## References

- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/DirectSumHeredityRefutation.Hereditary`
- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/DirectSumHeredityRefutation.claim`
- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/DirectSumHeredityRefutation.directSumProduct`
- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/DirectSumHeredityRefutation.inheritedProduct`
- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/DirectSumHeredityRefutation.result`
- Dependency: [D5/S3/QuadraticForms/EvolutionAlgebras/DerivationAnnihilatorObstruction](DerivationAnnihilatorObstruction.md)
