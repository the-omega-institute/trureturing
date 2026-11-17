# Semisimple derivation algebras are sums of orthogonal algebras

## Abstract

Semisimple derivation algebras are sums of orthogonal algebras.

**Theorem 1.1 (Transfer of trivial radical through a Lie equivalence).**

$$\forall (k : \operatorname{Type}), ([\operatorname{Field}\left(k\right)] \forall (L : \operatorname{Type}), ([\operatorname{LieRing}\left(L\right)] [\operatorname{LieAlgebra}\left(k, L\right)] \forall (N : \operatorname{Type}), ([\operatorname{LieRing}\left(N\right)] [\operatorname{LieAlgebra}\left(k, N\right)] [\operatorname{LieAlgebra}.\operatorname{HasTrivialRadical}\left(k, L\right)] \forall (e : \operatorname{LieEquiv}\left(k, L, N\right)), (\operatorname{LieAlgebra}.\operatorname{HasTrivialRadical}\left(k, N\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/EvolutionAlgebras/SemisimpleDerivationClassification.trivialRadical_of_equiv` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary Lie algebras L and N over a field, a Lie equivalence L to N transfers trivial actual solvable radical from L to N. This is the original canonical proof made public for the actual orthogonal dimension-four split; the existing semisimple classification and all its hypotheses retain their meanings.

**Theorem 1.2 (Zero diagonal coefficients).**

$$\forall (k : \operatorname{Type}), ([\operatorname{Field}\left(k\right)] [\operatorname{CharZero}\left(k\right)] \forall (n : \operatorname{Type}), ([\operatorname{Fintype}\left(n\right)] [\operatorname{DecidableEq}\left(n\right)] \forall (A : \operatorname{LieAlgebra}.\operatorname{Orthogonal}.\operatorname{so}\left(n, k\right)), (\forall (i : n), (\operatorname{val}\left(A, i, i\right) = (0)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/EvolutionAlgebras/SemisimpleDerivationClassification.diagonal_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ivan Kaygorodov; Cándido Martín González; Antonio Viruel (2026). *Evolution algebras: a survey of results and a list of open problems*. DOI: [10.48550/arXiv.2610.22248](https://doi.org/10.48550/arXiv.2610.22248). URL: <https://arxiv.org/abs/2610.22248v1>.

*Commentary.*

Every diagonal coefficient of an orthogonal Lie algebra matrix vanishes in characteristic zero.

**Theorem 1.3 (Skew transpose coefficients).**

$$\forall (k : \operatorname{Type}), ([\operatorname{Field}\left(k\right)] [\operatorname{CharZero}\left(k\right)] \forall (n : \operatorname{Type}), ([\operatorname{Fintype}\left(n\right)] [\operatorname{DecidableEq}\left(n\right)] \forall (A : \operatorname{LieAlgebra}.\operatorname{Orthogonal}.\operatorname{so}\left(n, k\right)), (\forall (i : n), (\forall (j : n), (\operatorname{val}\left(A, j, i\right) = (-\operatorname{val}\left(A, i, j\right)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/EvolutionAlgebras/SemisimpleDerivationClassification.coefficient_skew` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ivan Kaygorodov; Cándido Martín González; Antonio Viruel (2026). *Evolution algebras: a survey of results and a list of open problems*. DOI: [10.48550/arXiv.2610.22248](https://doi.org/10.48550/arXiv.2610.22248). URL: <https://arxiv.org/abs/2610.22248v1>.

*Commentary.*

Transposing the indices negates each coefficient of an orthogonal Lie algebra matrix.

**Definition 1.4 (claim).**

$$\operatorname{claim} = (\forall (k : \operatorname{Type}), ([\operatorname{Field}\left(k\right)] [\operatorname{IsAlgClosed}\left(k\right)] [\operatorname{CharZero}\left(k\right)] \forall (V : \operatorname{Type}), ([\operatorname{AddCommGroup}\left(V\right)] [\operatorname{Module}\left(k, V\right)] [\operatorname{FiniteDimensional}\left(k, V\right)] \forall (\mu : \operatorname{LinearMap}\left(k, V, \operatorname{LinearMap}\left(k, V, V\right)\right)), ((\operatorname{IsEvolutionAlgebra}\left(\mu\right)) \Rightarrow ((\operatorname{LieAlgebra}.\operatorname{IsSemisimple}\left(k, \operatorname{derivations}\left(\mu\right)\right)) \Rightarrow (\exists (r : \mathbb{N}), (\exists (m : (\operatorname{Fin}\left(r\right) \to \mathbb{N})), ((\forall (i : \operatorname{Fin}\left(r\right)), (3 \le m\left(i\right))) \land (\operatorname{Nonempty}\left(\operatorname{LieEquiv}\left(k, \operatorname{derivations}\left(\mu\right), \operatorname{DirectSum}\left(\operatorname{Fin}\left(r\right), (\operatorname{fun} i \mapsto \operatorname{LieAlgebra}.\operatorname{Orthogonal}.\operatorname{so}\left(\operatorname{Fin}\left(m\left(i\right)\right), k\right))\right)\right)\right))))))))))$$

*Formalization.* `D5/S3/QuadraticForms/EvolutionAlgebras/SemisimpleDerivationClassification.claim` (`✓ std3`).

*Citation.* Ivan Kaygorodov; Cándido Martín González; Antonio Viruel (2026). *Evolution algebras: a survey of results and a list of open problems*. DOI: [10.48550/arXiv.2610.22248](https://doi.org/10.48550/arXiv.2610.22248). URL: <https://arxiv.org/abs/2610.22248v1>.

*Commentary.*

Conjecture 5 (Semisimple derivation algebras), p. 28: “Let k be algebraically closed of characteristic 0. If Der(A) is semisimple for a finite-dimensional evolution algebra A, then Der(A) ≅ ⊕ᵢ so_{mᵢ} with mᵢ ≥ 3.” The field k and vector space V are arbitrary; μ is the bilinear product, and r = 0 permits the zero Lie algebra.

**Theorem 1.5 (result).**

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
- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/SemisimpleDerivationClassification.coefficient_skew`
- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/SemisimpleDerivationClassification.diagonal_zero`
- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/SemisimpleDerivationClassification.result`
- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/SemisimpleDerivationClassification.trivialRadical_of_equiv`
- Dependency: [D5/S3/QuadraticForms/EvolutionAlgebras/DerivationAnnihilatorObstruction](DerivationAnnihilatorObstruction.md)
- Dependency: [D5/S3/QuadraticForms/EvolutionAlgebras/NondegenerateDerivationBlocks](NondegenerateDerivationBlocks.md)
- Dependency: [D5/S3/QuadraticForms/OrthogonalPointwiseStabilizers](../OrthogonalPointwiseStabilizers.md)
