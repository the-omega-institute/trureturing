# Semisimple derivation algebras are sums of orthogonal algebras

## Abstract

Semisimple derivation algebras are sums of orthogonal algebras.

**Definition 1.1 (claim).**

$$\operatorname{claim} = (\forall (k : \operatorname{Type}), ([\operatorname{Field}\left(k\right)] [\operatorname{IsAlgClosed}\left(k\right)] [\operatorname{CharZero}\left(k\right)] \forall (V : \operatorname{Type}), ([\operatorname{AddCommGroup}\left(V\right)] [\operatorname{Module}\left(k, V\right)] [\operatorname{FiniteDimensional}\left(k, V\right)] \forall (\mu : \operatorname{LinearMap}\left(k, V, \operatorname{LinearMap}\left(k, V, V\right)\right)), ((\operatorname{IsEvolutionAlgebra}\left(\mu\right)) \Rightarrow ((\operatorname{LieAlgebra}.\operatorname{IsSemisimple}\left(k, \operatorname{derivations}\left(\mu\right)\right)) \Rightarrow (\exists (r : \mathbb{N}), (\exists (m : (\operatorname{Fin}\left(r\right) \to \mathbb{N})), ((\forall (i : \operatorname{Fin}\left(r\right)), (3 \le m\left(i\right))) \land (\operatorname{Nonempty}\left(\operatorname{LieEquiv}\left(k, \operatorname{derivations}\left(\mu\right), \operatorname{DirectSum}\left(\operatorname{Fin}\left(r\right), (\operatorname{fun} i \mapsto \operatorname{LieAlgebra}.\operatorname{Orthogonal}.\operatorname{so}\left(\operatorname{Fin}\left(m\left(i\right)\right), k\right))\right)\right)\right))))))))))$$

*Formalization.* `D5/S3/QuadraticForms/EvolutionAlgebras/SemisimpleDerivationClassification.claim` (`✓ std3`).

*Citation.* Ivan Kaygorodov; Cándido Martín González; Antonio Viruel (2026). *Evolution algebras: a survey of results and a list of open problems*. DOI: [10.48550/arXiv.2610.22248](https://doi.org/10.48550/arXiv.2610.22248). URL: <https://arxiv.org/abs/2610.22248v1>.

*Commentary.*

Conjecture 5 (Semisimple derivation algebras), p. 28: “Let k be algebraically closed of characteristic 0. If Der(A) is semisimple for a finite-dimensional evolution algebra A, then Der(A) ≅ ⊕ᵢ so_{mᵢ} with mᵢ ≥ 3.” The field k and vector space V are arbitrary; μ is the bilinear product, and r = 0 permits the zero Lie algebra.

**Theorem 1.2 (result).**

$$\forall (k : \operatorname{Type}), ([\operatorname{Field}\left(k\right)] [\operatorname{IsAlgClosed}\left(k\right)] [\operatorname{CharZero}\left(k\right)] \forall (V : \operatorname{Type}), ([\operatorname{AddCommGroup}\left(V\right)] [\operatorname{Module}\left(k, V\right)] [\operatorname{FiniteDimensional}\left(k, V\right)] \forall (\mu : \operatorname{LinearMap}\left(k, V, \operatorname{LinearMap}\left(k, V, V\right)\right)), ((\operatorname{IsEvolutionAlgebra}\left(\mu\right)) \Rightarrow ((\operatorname{LieAlgebra}.\operatorname{IsSemisimple}\left(k, \operatorname{derivations}\left(\mu\right)\right)) \Rightarrow (\exists (r : \mathbb{N}), (\exists (m : (\operatorname{Fin}\left(r\right) \to \mathbb{N})), ((\forall (i : \operatorname{Fin}\left(r\right)), (3 \le m\left(i\right))) \land (\operatorname{Nonempty}\left(\operatorname{LieEquiv}\left(k, \operatorname{derivations}\left(\mu\right), \operatorname{DirectSum}\left(\operatorname{Fin}\left(r\right), (\operatorname{fun} i \mapsto \operatorname{LieAlgebra}.\operatorname{Orthogonal}.\operatorname{so}\left(\operatorname{Fin}\left(m\left(i\right)\right), k\right))\right)\right)\right)))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/EvolutionAlgebras/SemisimpleDerivationClassification.result` (`✓ std3`). ∎

*Resolves.* `Problems/kaygorodov-martin-gonzalez-viruel-2026-evolution-algebra-derivations-conjecture-5` (proved) by `D5/S3/QuadraticForms/EvolutionAlgebras/SemisimpleDerivationClassification.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"kaygorodov-martin-gonzalez-viruel-2026-evolution-algebra-derivations-conjecture-5","declaration_gid":"D5/S3/QuadraticForms/EvolutionAlgebras/SemisimpleDerivationClassification.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Ivan Kaygorodov; Cándido Martín González; Antonio Viruel (2026). *Evolution algebras: a survey of results and a list of open problems*. DOI: [10.48550/arXiv.2610.22248](https://doi.org/10.48550/arXiv.2610.22248). URL: <https://arxiv.org/abs/2610.22248v1>.

*Commentary.*

The annihilator obstruction removes zero natural squares. The block decomposition identifies all derivations with independent orthogonal pointwise stabilizers. Their radical quotients give standard orthogonal algebras. Dimensions zero and one contribute zero, and dimension two is excluded by its nonzero abelian algebra. The remaining factors have dimension at least three.

## References

- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/SemisimpleDerivationClassification.claim`
- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/SemisimpleDerivationClassification.result`
- Dependency: [D5/S3/QuadraticForms/EvolutionAlgebras/DerivationAnnihilatorObstruction](DerivationAnnihilatorObstruction.md)
- Dependency: [D5/S3/QuadraticForms/EvolutionAlgebras/NondegenerateDerivationBlocks](NondegenerateDerivationBlocks.md)
- Dependency: [D5/S3/QuadraticForms/OrthogonalPointwiseStabilizers](../OrthogonalPointwiseStabilizers.md)
