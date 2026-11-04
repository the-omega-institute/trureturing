# Evolution automorphisms and the tangent Lie algebra

## Abstract

A natural SL3 realization identifies all infinitesimal automorphisms with derivations.

**Definition 1.1 (automorphisms).**

$$\forall R \in \operatorname{Type},\; [\operatorname{CommRing}\left(R\right)] \forall V \in \operatorname{Type},\; [\operatorname{AddCommGroup}\left(V\right)] [\operatorname{Module}\left(R, V\right)] \forall mu \in \operatorname{LinearMap}\left(\operatorname{RingHom}.\operatorname{id}\left(R\right), V, \operatorname{LinearMap}\left(\operatorname{RingHom}.\operatorname{id}\left(R\right), V, V\right)\right),\; \operatorname{automorphisms}\left(mu\right) = \{g:\operatorname{LinearEquiv}\left(\operatorname{RingHom}.\operatorname{id}\left(R\right), V, V\right) \mid \forall x \in V,\; \forall y \in V,\; g\left(mu\left(x, y\right)\right) = mu\left(g\left(x\right), g\left(y\right)\right)\}$$

*Formalization.* `D5/S3/QuadraticForms/EvolutionAlgebras/EvolutionAutomorphismTangentBridge.automorphisms` (`✓ std3`).

*Citation.* Ivan Kaygorodov; Cándido Martín González; Antonio Viruel (2026). *Evolution algebras: a survey of results and a list of open problems*. DOI: [10.48550/arXiv.2610.22248](https://doi.org/10.48550/arXiv.2610.22248). URL: <https://arxiv.org/abs/2610.22248v1>.

*Commentary.*

All invertible linear maps preserving the given bilinear multiplication form a subgroup. No identity element or associativity of the multiplication is required.

**Definition 1.2 (glCoordinates).**

$$\forall degree \in \operatorname{Nat},\; \forall R \in \operatorname{Type},\; [\operatorname{CommRing}\left(R\right)] \forall g \in \operatorname{Matrix}.\operatorname{GeneralLinearGroup}\left(\operatorname{Fin}\left(degree\right), R\right),\; \left(\forall i \in \operatorname{Fin}\left(degree\right),\; \forall j \in \operatorname{Fin}\left(degree\right),\; \operatorname{glCoordinates}\left(g\right)\left(\operatorname{Sum}.\operatorname{inl}\left((i, j)\right)\right) = (g :\operatorname{Matrix}\left(\operatorname{Fin}\left(degree\right), \operatorname{Fin}\left(degree\right), R\right))\left(i, j\right)\right) \land \left(\forall u \in \operatorname{Unit},\; \operatorname{glCoordinates}\left(g\right)\left(\operatorname{Sum}.\operatorname{inr}\left(u\right)\right) = \operatorname{val}\left(\operatorname{Inv}.\operatorname{inv}\left(\operatorname{Matrix}.\operatorname{GeneralLinearGroup}.\operatorname{det}\left(g\right)\right)\right)\right)$$

*Formalization.* `D5/S3/QuadraticForms/EvolutionAlgebras/EvolutionAutomorphismTangentBridge.glCoordinates` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ivan Kaygorodov; Cándido Martín González; Antonio Viruel (2026). *Evolution algebras: a survey of results and a list of open problems*. DOI: [10.48550/arXiv.2610.22248](https://doi.org/10.48550/arXiv.2610.22248). URL: <https://arxiv.org/abs/2610.22248v1>.

*Commentary.*

The affine coordinates of GL consist of every matrix entry and the inverse determinant. The sum type adds one coordinate indexed by Unit.

**Definition 1.3 (LinearAlgebraicGroup).**

$$\forall k \in \operatorname{Type},\; [\operatorname{Field}\left(k\right)] \operatorname{LinearAlgebraicGroup}\left(k\right) = \{degree:\operatorname{Nat}, equations:\operatorname{Set}\left(\operatorname{MvPolynomial}\left(\operatorname{Sum}\left(\operatorname{Prod}\left(\operatorname{Fin}\left(degree\right), \operatorname{Fin}\left(degree\right)\right), \operatorname{Unit}\right), k\right)\right), points:\forall R \in \operatorname{Type},\; [\operatorname{CommRing}\left(R\right)] [\operatorname{Algebra}\left(k, R\right)] \operatorname{Subgroup}\left(\operatorname{Matrix}.\operatorname{GeneralLinearGroup}\left(\operatorname{Fin}\left(degree\right), R\right)\right) \mid (\forall R \in \operatorname{Type},\; [\operatorname{CommRing}\left(R\right)] [\operatorname{Algebra}\left(k, R\right)] \forall g \in \operatorname{Matrix}.\operatorname{GeneralLinearGroup}\left(\operatorname{Fin}\left(degree\right), R\right),\; g \in points\left(R\right) \Leftrightarrow \left(\forall p \in \operatorname{MvPolynomial}\left(\operatorname{Sum}\left(\operatorname{Prod}\left(\operatorname{Fin}\left(degree\right), \operatorname{Fin}\left(degree\right)\right), \operatorname{Unit}\right), k\right),\; p \in equations \Rightarrow \operatorname{MvPolynomial}.\operatorname{eval}_{2}\left(\operatorname{algebraMap}\left(k, R\right), \operatorname{glCoordinates}\left(g\right), p\right) = 0\right)) \land (\forall R \in \operatorname{Type},\; [\operatorname{CommRing}\left(R\right)] [\operatorname{Algebra}\left(k, R\right)] \forall S \in \operatorname{Type},\; [\operatorname{CommRing}\left(S\right)] [\operatorname{Algebra}\left(k, S\right)] \forall f \in \operatorname{AlgHom}\left(k, R, S\right),\; \forall g \in \operatorname{Matrix}.\operatorname{GeneralLinearGroup}\left(\operatorname{Fin}\left(degree\right), R\right),\; g \in points\left(R\right) \Rightarrow \operatorname{Matrix}.\operatorname{GeneralLinearGroup}.\operatorname{map}\left(f.\operatorname{toRingHom}, g\right) \in points\left(S\right))\}$$

*Formalization.* `D5/S3/QuadraticForms/EvolutionAlgebras/EvolutionAutomorphismTangentBridge.LinearAlgebraicGroup` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ivan Kaygorodov; Cándido Martín González; Antonio Viruel (2026). *Evolution algebras: a survey of results and a list of open problems*. DOI: [10.48550/arXiv.2610.22248](https://doi.org/10.48550/arXiv.2610.22248). URL: <https://arxiv.org/abs/2610.22248v1>.

*Commentary.*

A closed matrix group consists of a degree, polynomial equations and subgroups over every commutative coefficient algebra. Membership is exactly their common zero locus, and matrix maps preserve membership. The two conditions after the vertical bar are the zero-locus and change-of-algebra fields.

**Definition 1.4 (Realizes).**

$$\forall k \in \operatorname{Type},\; [\operatorname{Field}\left(k\right)] \forall V \in \operatorname{Type},\; [\operatorname{AddCommGroup}\left(V\right)] [\operatorname{Module}\left(k, V\right)] \forall G \in \operatorname{LinearAlgebraicGroup}\left(k\right),\; \forall mu \in \operatorname{LinearMap}\left(\operatorname{RingHom}.\operatorname{id}\left(k\right), V, \operatorname{LinearMap}\left(\operatorname{RingHom}.\operatorname{id}\left(k\right), V, V\right)\right),\; \operatorname{Realizes}\left(G, mu\right) = \{equiv:\forall R \in \operatorname{Type},\; [\operatorname{CommRing}\left(R\right)] [\operatorname{Algebra}\left(k, R\right)] \operatorname{MulEquiv}\left(G.\operatorname{points}\left(R\right), \operatorname{automorphisms}\left(\operatorname{LinearMap}.\operatorname{BilinMap}.\operatorname{baseChange}\left(R, mu\right)\right)\right) \mid \forall R \in \operatorname{Type},\; [\operatorname{CommRing}\left(R\right)] [\operatorname{Algebra}\left(k, R\right)] \forall S \in \operatorname{Type},\; [\operatorname{CommRing}\left(S\right)] [\operatorname{Algebra}\left(k, S\right)] \forall f \in \operatorname{AlgHom}\left(k, R, S\right),\; \forall g \in G.\operatorname{points}\left(R\right),\; \forall x \in \operatorname{TensorProduct}\left(k, R, V\right),\; \operatorname{TensorProduct}.\operatorname{map}\left(f.\operatorname{toLinearMap}, \operatorname{LinearMap}.\operatorname{id}\right)\left(\operatorname{val}\left(equiv\left(R, g\right)\right)\left(x\right)\right) = \operatorname{val}\left(equiv\left(S, \langle\operatorname{Matrix}.\operatorname{GeneralLinearGroup}.\operatorname{map}\left(f.\operatorname{toRingHom}, \operatorname{val}\left(g\right)\right), G.\operatorname{mapMem}\left(R, S, f, \operatorname{val}\left(g\right), g.\operatorname{property}\right)\rangle\right)\right)\left(\operatorname{TensorProduct}.\operatorname{map}\left(f.\operatorname{toLinearMap}, \operatorname{LinearMap}.\operatorname{id}\right)\left(x\right)\right)\}$$

*Formalization.* `D5/S3/QuadraticForms/EvolutionAlgebras/EvolutionAutomorphismTangentBridge.Realizes` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ivan Kaygorodov; Cándido Martín González; Antonio Viruel (2026). *Evolution algebras: a survey of results and a list of open problems*. DOI: [10.48550/arXiv.2610.22248](https://doi.org/10.48550/arXiv.2610.22248). URL: <https://arxiv.org/abs/2610.22248v1>.

*Commentary.*

A realization consists of group equivalences over every commutative coefficient algebra, commuting with every algebra homomorphism on every tensor. TensorProduct.map uses the identity on V. This expresses an isomorphism of the full group-valued functors, including algebras with nilpotents.

**Definition 1.5 (slGroup).**

$$\forall n \in \operatorname{Nat},\; \operatorname{slGroup}\left(n\right) = \{\operatorname{degree}:=n, \operatorname{equations}:=\{\operatorname{Matrix}.\operatorname{det}\left((\operatorname{fun} i \mapsto (\operatorname{fun} j \mapsto \operatorname{MvPolynomial}.\operatorname{X}\left(\operatorname{Sum}.\operatorname{inl}\left((i, j)\right)\right)))\right) - 1\}, \operatorname{points}:=\operatorname{fun} (R:\operatorname{Type}) [\operatorname{CommRing}\left(R\right)] [\operatorname{Algebra}\left(\operatorname{Complex}, R\right)] \mapsto \operatorname{MonoidHom}.\operatorname{ker}\left(\operatorname{Matrix}.\operatorname{GeneralLinearGroup}.\operatorname{det} :\operatorname{MonoidHom}\left(\operatorname{Matrix}.\operatorname{GeneralLinearGroup}\left(\operatorname{Fin}\left(n\right), R\right), \operatorname{Units}\left(R\right)\right)\right)\}$$

*Formalization.* `D5/S3/QuadraticForms/EvolutionAlgebras/EvolutionAutomorphismTangentBridge.slGroup` (`✓ std3`).

*Citation.* Ivan Kaygorodov; Cándido Martín González; Antonio Viruel (2026). *Evolution algebras: a survey of results and a list of open problems*. DOI: [10.48550/arXiv.2610.22248](https://doi.org/10.48550/arXiv.2610.22248). URL: <https://arxiv.org/abs/2610.22248v1>.

*Commentary.*

The single equation det(X) − 1 defines SL at every coefficient algebra. Its points are the kernel of the determinant homomorphism on Matrix.GeneralLinearGroup. The remaining structure fields prove the zero-locus characterization and preservation under matrix maps.

**Theorem 1.6 (tangent_lie_equivalence).**

$$\forall V \in \operatorname{Type},\; [\operatorname{AddCommGroup}\left(V\right)] [\operatorname{Module}\left(\operatorname{Complex}, V\right)] \forall mu \in \operatorname{LinearMap}\left(\operatorname{RingHom}.\operatorname{id}\left(\operatorname{Complex}\right), V, \operatorname{LinearMap}\left(\operatorname{RingHom}.\operatorname{id}\left(\operatorname{Complex}\right), V, V\right)\right),\; (\operatorname{Realizes}\left(\operatorname{slGroup}\left(3\right), mu\right) \to \operatorname{Nonempty}\left(\operatorname{LieEquiv}\left(\operatorname{Complex}, \operatorname{LieAlgebra}.\operatorname{SpecialLinear}.\operatorname{sl}\left(\operatorname{Fin}\left(3\right), \operatorname{Complex}\right), \operatorname{derivations}\left(mu\right)\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/EvolutionAlgebras/EvolutionAutomorphismTangentBridge.tangent_lie_equivalence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ivan Kaygorodov; Cándido Martín González; Antonio Viruel (2026). *Evolution algebras: a survey of results and a list of open problems*. DOI: [10.48550/arXiv.2610.22248](https://doi.org/10.48550/arXiv.2610.22248). URL: <https://arxiv.org/abs/2610.22248v1>.

*Commentary.*

Dual-number coefficients reconstruct every derivation from a tangent automorphism. Addition is composition, scalar multiplication is substitution of epsilon, and the commutator over iterated dual numbers recovers the Lie bracket. Naturality therefore gives a complex Lie equivalence from trace-zero 3 by 3 matrices to all derivations.

## References

- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/EvolutionAutomorphismTangentBridge.LinearAlgebraicGroup`
- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/EvolutionAutomorphismTangentBridge.Realizes`
- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/EvolutionAutomorphismTangentBridge.automorphisms`
- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/EvolutionAutomorphismTangentBridge.glCoordinates`
- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/EvolutionAutomorphismTangentBridge.slGroup`
- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/EvolutionAutomorphismTangentBridge.tangent_lie_equivalence`
- Dependency: [D5/S3/QuadraticForms/EvolutionAlgebras/DerivationAnnihilatorObstruction](DerivationAnnihilatorObstruction.md)
