# A negative answer to Question 31 for algebraic groups and group schemes

## Abstract

SL3 refutes universal realization by full evolution-algebra automorphism functors.

**Definition 1.1 (claim).**

$$\operatorname{claim} = \left(\forall G \in \operatorname{LinearAlgebraicGroup}\left(\operatorname{Complex}\right),\; \exists d \in \operatorname{Nat},\; \exists mu \in \operatorname{LinearMap}\left(\operatorname{RingHom}.\operatorname{id}\left(\operatorname{Complex}\right), (\operatorname{Fin}\left(d\right) \to \operatorname{Complex}), \operatorname{LinearMap}\left(\operatorname{RingHom}.\operatorname{id}\left(\operatorname{Complex}\right), (\operatorname{Fin}\left(d\right) \to \operatorname{Complex}), (\operatorname{Fin}\left(d\right) \to \operatorname{Complex})\right)\right),\; \operatorname{IsEvolutionAlgebra}\left(mu\right) \land \operatorname{Nonempty}\left(\operatorname{Realizes}\left(G, mu\right)\right)\right)$$

*Formalization.* `D5/S3/QuadraticForms/EvolutionAlgebras/AlgebraicGroupRealizationRefutation.claim` (`✓ std3`).

*Citation.* Ivan Kaygorodov; Cándido Martín González; Antonio Viruel (2026). *Evolution algebras: a survey of results and a list of open problems*. DOI: [10.48550/arXiv.2610.22248](https://doi.org/10.48550/arXiv.2610.22248). URL: <https://arxiv.org/abs/2610.22248v1>.

*Commentary.*

Question 31 (Realisation of algebraic groups), page 24: “Let G be a linear algebraic group over 𝕜. Is there a finite-dimensional evolution 𝕜-algebra A with Aut(A) ≅ G(𝕜) as abstract groups? with Aut(A) ≅ G as algebraic groups? with 𝐀𝐮𝐭(A) ≅ G as group schemes?” The second and third interrogatives are expressed over Complex using polynomial-closed matrix groups and natural equivalences over every commutative unital Complex-algebra. The source assumes finite dimension unless stated otherwise. The integer d includes zero, the product is arbitrary bilinear multiplication on Fin d → Complex, and IsEvolutionAlgebra supplies an arbitrary natural basis. The first interrogative is outside this assertion.

**Theorem 1.2 (result).**

$$\neg (\forall G \in \operatorname{LinearAlgebraicGroup}\left(\operatorname{Complex}\right),\; \exists d \in \operatorname{Nat},\; \exists mu \in \operatorname{LinearMap}\left(\operatorname{RingHom}.\operatorname{id}\left(\operatorname{Complex}\right), (\operatorname{Fin}\left(d\right) \to \operatorname{Complex}), \operatorname{LinearMap}\left(\operatorname{RingHom}.\operatorname{id}\left(\operatorname{Complex}\right), (\operatorname{Fin}\left(d\right) \to \operatorname{Complex}), (\operatorname{Fin}\left(d\right) \to \operatorname{Complex})\right)\right),\; \operatorname{IsEvolutionAlgebra}\left(mu\right) \land \operatorname{Nonempty}\left(\operatorname{Realizes}\left(G, mu\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/EvolutionAlgebras/AlgebraicGroupRealizationRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/kmvq31` (refuted) by `D5/S3/QuadraticForms/EvolutionAlgebras/AlgebraicGroupRealizationRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"kmvq31","declaration_gid":"D5/S3/QuadraticForms/EvolutionAlgebras/AlgebraicGroupRealizationRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Ivan Kaygorodov; Cándido Martín González; Antonio Viruel (2026). *Evolution algebras: a survey of results and a list of open problems*. DOI: [10.48550/arXiv.2610.22248](https://doi.org/10.48550/arXiv.2610.22248). URL: <https://arxiv.org/abs/2610.22248v1>.

*Commentary.*

For G = slGroup 3, naturality over dual numbers and iterated dual numbers forces the derivation Lie algebra to be sl3. Its dimension is eight and its radical is zero. The semisimple derivation classification of arbitrary finite-dimensional evolution algebras expresses it as a finite sum of orthogonal algebras so(m), m ≥ 3. A summand of dimension at most eight has m = 3 or m = 4 and dimension three or six. A sum of such dimensions is divisible by three and cannot equal eight. This includes products with nonzero annihilator. The comparison between the algebraic-group and group-scheme categories uses characteristic-zero smoothness; the Lean statement uses exactly the full functor formulation. The SLn family outside n = 3, the abstract-group interrogative, positive characteristic, SL2 and SL4 remain outside this theorem. Finite-group, general-linear and orthogonal examples in the survey are unaffected.

## References

- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/AlgebraicGroupRealizationRefutation.claim`
- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/AlgebraicGroupRealizationRefutation.result`
- Dependency: [D5/S3/QuadraticForms/EvolutionAlgebras/DerivationAnnihilatorObstruction](DerivationAnnihilatorObstruction.md)
- Dependency: [D5/S3/QuadraticForms/EvolutionAlgebras/EvolutionAutomorphismTangentBridge](EvolutionAutomorphismTangentBridge.md)
- Dependency: [D5/S3/QuadraticForms/EvolutionAlgebras/SemisimpleDerivationClassification](SemisimpleDerivationClassification.md)
