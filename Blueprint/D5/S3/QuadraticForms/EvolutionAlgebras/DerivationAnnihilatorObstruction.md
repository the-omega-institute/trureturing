# Natural squares and semisimple derivations

## Abstract

Natural squares and semisimple derivations.

**Definition 1.1 (IsEvolutionAlgebra).**

$$\forall (k : \operatorname{Type}), ([\operatorname{Field}\left(k\right)] \forall (V : \operatorname{Type}), ([\operatorname{AddCommGroup}\left(V\right)] [\operatorname{Module}\left(k, V\right)] \forall (\mu : \operatorname{LinearMap}\left(k, V, \operatorname{LinearMap}\left(k, V, V\right)\right)), (\operatorname{IsEvolutionAlgebra}\left(\mu\right) = ((\forall (x : V), (\forall (y : V), (\mu\left(x, y\right) = (\mu\left(y, x\right))))) \land (\exists (\iota : \operatorname{Type}), (\exists (b : \operatorname{Module}.\operatorname{Basis}\left(\iota, k, V\right)), (\forall (i : \iota), (\forall (j : \iota), ((i \ne j) \Rightarrow (\mu\left(b\left(i\right), b\left(j\right)\right) = (0)))))))))))$$

*Formalization.* `D5/S3/QuadraticForms/EvolutionAlgebras/DerivationAnnihilatorObstruction.IsEvolutionAlgebra` (`✓ std3`).

*Citation.* Ivan Kaygorodov; Cándido Martín González; Antonio Viruel (2026). *Evolution algebras: a survey of results and a list of open problems*. DOI: [10.48550/arXiv.2610.22248](https://doi.org/10.48550/arXiv.2610.22248). URL: <https://arxiv.org/abs/2610.22248v1>.

*Commentary.*

Section 1.1, p. 3: “Let k be a field. A k-algebra A is called an evolution algebra if it admits a basis B = {eᵢ}ᵢ∈Λ, called a natural basis, such that eᵢeⱼ = 0 whenever i ≠ j. Evolution algebras are commutative, and in general they are neither associative nor power-associative.” Here the two conjuncts express commutativity and the natural basis property; no associativity or unit is assumed.

**Definition 1.2 (derivations).**

$$\forall (k : \operatorname{Type}), ([\operatorname{Field}\left(k\right)] \forall (V : \operatorname{Type}), ([\operatorname{AddCommGroup}\left(V\right)] [\operatorname{Module}\left(k, V\right)] \forall (\mu : \operatorname{LinearMap}\left(k, V, \operatorname{LinearMap}\left(k, V, V\right)\right)), (\operatorname{derivations}\left(\mu\right) = (\{D : \operatorname{Module}.\operatorname{End}\left(k, V\right) \mid \forall (x : V), (\forall (y : V), (D\left(\mu\left(x, y\right)\right) = (\mu\left(D\left(x\right), y\right) + \mu\left(x, D\left(y\right)\right))))\}))))$$

*Formalization.* `D5/S3/QuadraticForms/EvolutionAlgebras/DerivationAnnihilatorObstruction.derivations` (`✓ std3`).

*Citation.* Ivan Kaygorodov; Cándido Martín González; Antonio Viruel (2026). *Evolution algebras: a survey of results and a list of open problems*. DOI: [10.48550/arXiv.2610.22248](https://doi.org/10.48550/arXiv.2610.22248). URL: <https://arxiv.org/abs/2610.22248v1>.

*Commentary.*

Der(A) consists of the linear maps D satisfying D(xy) = D(x)y + xD(y), with the commutator bracket. The displayed carrier determines the Lie subalgebra.

**Theorem 1.3 (semisimple perfect).**

$$\forall (k : \operatorname{Type}), ([\operatorname{Field}\left(k\right)] \forall (L : \operatorname{Type}), ([\operatorname{LieRing}\left(L\right)] [\operatorname{LieAlgebra}\left(k, L\right)] [\operatorname{LieAlgebra}.\operatorname{IsSemisimple}\left(k, L\right)] \operatorname{Bracket}.\operatorname{bracket}\left(\operatorname{top} : \operatorname{LieIdeal}\left(k, L\right), \operatorname{top} : \operatorname{LieIdeal}\left(k, L\right)\right) = (\operatorname{top} : \operatorname{LieIdeal}\left(k, L\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/EvolutionAlgebras/DerivationAnnihilatorObstruction.semisimple_perfect` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ivan Kaygorodov; Cándido Martín González; Antonio Viruel (2026). *Evolution algebras: a survey of results and a list of open problems*. DOI: [10.48550/arXiv.2610.22248](https://doi.org/10.48550/arXiv.2610.22248). URL: <https://arxiv.org/abs/2610.22248v1>.

*Commentary.*

A semisimple Lie algebra equals its derived ideal.

**Definition 1.4 (square).**

$$\forall (k : \operatorname{Type}), ([\operatorname{Field}\left(k\right)] \forall (V : \operatorname{Type}), ([\operatorname{AddCommGroup}\left(V\right)] [\operatorname{Module}\left(k, V\right)] \forall (\mu : \operatorname{LinearMap}\left(k, V, \operatorname{LinearMap}\left(k, V, V\right)\right)), (\operatorname{Annihilator}.\operatorname{square}\left(\mu\right) = (\operatorname{Submodule}.\operatorname{span}\left(k, \{v \mid \exists (x : V), (\exists (y : V), (\mu\left(x, y\right) = (v)))\}\right)))))$$

*Formalization.* `D5/S3/QuadraticForms/EvolutionAlgebras/DerivationAnnihilatorObstruction.square` (`✓ std3`).

*Citation.* Ivan Kaygorodov; Cándido Martín González; Antonio Viruel (2026). *Evolution algebras: a survey of results and a list of open problems*. DOI: [10.48550/arXiv.2610.22248](https://doi.org/10.48550/arXiv.2610.22248). URL: <https://arxiv.org/abs/2610.22248v1>.

*Commentary.*

The square space is the span of all products.

**Theorem 1.5 (semisimple ann or perfect).**

$$\forall (k : \operatorname{Type}), ([\operatorname{Field}\left(k\right)] \forall (V : \operatorname{Type}), ([\operatorname{AddCommGroup}\left(V\right)] [\operatorname{Module}\left(k, V\right)] \forall (\mu : \operatorname{LinearMap}\left(k, V, \operatorname{LinearMap}\left(k, V, V\right)\right)), ((\forall (x : V), (\forall (y : V), (\mu\left(x, y\right) = (\mu\left(y, x\right))))) \Rightarrow ([\operatorname{FiniteDimensional}\left(k, V\right)] [\operatorname{LieAlgebra}.\operatorname{IsSemisimple}\left(k, \operatorname{derivations}\left(\mu\right)\right)] (\operatorname{LinearMap}.\operatorname{ker}\left(\mu\right) = (\operatorname{bot})) \lor (\operatorname{Annihilator}.\operatorname{square}\left(\mu\right) = (\operatorname{top}))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/EvolutionAlgebras/DerivationAnnihilatorObstruction.semisimple_ann_or_perfect` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ivan Kaygorodov; Cándido Martín González; Antonio Viruel (2026). *Evolution algebras: a survey of results and a list of open problems*. DOI: [10.48550/arXiv.2610.22248](https://doi.org/10.48550/arXiv.2610.22248). URL: <https://arxiv.org/abs/2610.22248v1>.

*Commentary.*

For a finite-dimensional commutative bilinear algebra with semisimple derivations, either the annihilator is zero or every vector belongs to the square space. A nonzero annihilator together with a proper square space produces an abelian ideal or an annihilator action of trace one.

**Theorem 1.6 (semisimple natural squares ne zero).**

$$\forall (k : \operatorname{Type}), ([\operatorname{Field}\left(k\right)] \forall (V : \operatorname{Type}), ([\operatorname{AddCommGroup}\left(V\right)] [\operatorname{Module}\left(k, V\right)] \forall (\mu : \operatorname{LinearMap}\left(k, V, \operatorname{LinearMap}\left(k, V, V\right)\right)), ((\forall (x : V), (\forall (y : V), (\mu\left(x, y\right) = (\mu\left(y, x\right))))) \Rightarrow (\forall (\iota : \operatorname{Type}), (\forall (b : \operatorname{Module}.\operatorname{Basis}\left(\iota, k, V\right)), ((\forall (i : \iota), (\forall (j : \iota), ((i \ne j) \Rightarrow (\mu\left(b\left(i\right), b\left(j\right)\right) = (0))))) \Rightarrow ([\operatorname{FiniteDimensional}\left(k, V\right)] [\operatorname{LieAlgebra}.\operatorname{IsSemisimple}\left(k, \operatorname{derivations}\left(\mu\right)\right)] \forall (i : \iota), (\mu\left(b\left(i\right), b\left(i\right)\right) \ne 0))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/EvolutionAlgebras/DerivationAnnihilatorObstruction.semisimple_natural_squares_ne_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ivan Kaygorodov; Cándido Martín González; Antonio Viruel (2026). *Evolution algebras: a survey of results and a list of open problems*. DOI: [10.48550/arXiv.2610.22248](https://doi.org/10.48550/arXiv.2610.22248). URL: <https://arxiv.org/abs/2610.22248v1>.

*Commentary.*

Every vector of a natural basis has nonzero square. A zero square makes the square-map singular and supplies a nonzero annihilator vector, contradicting the preceding dichotomy.

## References

- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/DerivationAnnihilatorObstruction.IsEvolutionAlgebra`
- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/DerivationAnnihilatorObstruction.derivations`
- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/DerivationAnnihilatorObstruction.semisimple_ann_or_perfect`
- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/DerivationAnnihilatorObstruction.semisimple_natural_squares_ne_zero`
- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/DerivationAnnihilatorObstruction.semisimple_perfect`
- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/DerivationAnnihilatorObstruction.square`
