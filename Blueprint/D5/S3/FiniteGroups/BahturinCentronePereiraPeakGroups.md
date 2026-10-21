# Refutation of the peak-group dichotomy

## Abstract

The constructed finite peak group is neither solvable nor a Frobenius group.

**Definition 1.1 (Complex character degrees).**

$$\forall G \in Type,\; [Group\left(G\right)], \operatorname{D5}.\operatorname{S3}.\operatorname{FiniteGroups}.\operatorname{BahturinCentronePereiraPeakGroups}.\operatorname{BCP31}.\operatorname{degreeSet}\left(G\right) = \{d: \mathbb{N} | (\exists V \in FDRep\left(\mathbb{C}, G\right),\; (\operatorname{CategoryTheory}.\operatorname{Simple}\left(V\right)) \land (\operatorname{Module}.\operatorname{finrank}\left(\mathbb{C}, V\right) = d))\}$$

*Formalization.* `D5/S3/FiniteGroups/BahturinCentronePereiraPeakGroups.degreeSet` (`✓ std3`).

*Citation.* Bahturin, Yuri; Centrone, Lucio; Pereira, Kauê (2026). *Quantum regularity of finite dimensional semisimple algebras*. DOI: [10.48550/arXiv.2608.21936](https://doi.org/10.48550/arXiv.2608.21936). URL: <https://arxiv.org/abs/2608.21936v1>.

*Commentary.*

The set consists of the dimensions of simple finite-dimensional complex representations.

**Definition 1.2 (Peak groups).**

$$\forall G \in Type,\; [Group\left(G\right)], \operatorname{D5}.\operatorname{S3}.\operatorname{FiniteGroups}.\operatorname{BahturinCentronePereiraPeakGroups}.\operatorname{BCP31}.\operatorname{IsPeak}\left(G\right) = (\exists d \in \mathbb{N},\; (d \in \operatorname{D5}.\operatorname{S3}.\operatorname{FiniteGroups}.\operatorname{BahturinCentronePereiraPeakGroups}.\operatorname{BCP31}.\operatorname{degreeSet}\left(G\right)) \land (\forall e \in \mathbb{N},\; (e \in \operatorname{D5}.\operatorname{S3}.\operatorname{FiniteGroups}.\operatorname{BahturinCentronePereiraPeakGroups}.\operatorname{BCP31}.\operatorname{degreeSet}\left(G\right)) \Rightarrow (e \mid d)))$$

*Formalization.* `D5/S3/FiniteGroups/BahturinCentronePereiraPeakGroups.IsPeak` (`✓ std3`).

*Citation.* Bahturin, Yuri; Centrone, Lucio; Pereira, Kauê (2026). *Quantum regularity of finite dimensional semisimple algebras*. DOI: [10.48550/arXiv.2608.21936](https://doi.org/10.48550/arXiv.2608.21936). URL: <https://arxiv.org/abs/2608.21936v1>.

*Commentary.*

A peak group has a character degree divisible by every character degree.

**Definition 1.3 (Frobenius complements).**

$$\forall G \in Type,\; [Group\left(G\right)], \forall H \in Subgroup\left(G\right),\; \operatorname{D5}.\operatorname{S3}.\operatorname{FiniteGroups}.\operatorname{BahturinCentronePereiraPeakGroups}.\operatorname{BCP31}.\operatorname{IsFrobeniusWithComplement}\left(G, H\right) = ((H \ne \operatorname{Bot}.\operatorname{bot}) \land ((H \ne \operatorname{Top}.\operatorname{top}) \land (\forall g \in G,\; (\neg g \in H) \Rightarrow (\operatorname{Min}.\operatorname{min}\left(H, \operatorname{Subgroup}.\operatorname{map}\left(\operatorname{MulAut}.\operatorname{conj}\left(g\right), H\right)\right) = \operatorname{Bot}.\operatorname{bot}))))$$

*Formalization.* `D5/S3/FiniteGroups/BahturinCentronePereiraPeakGroups.IsFrobeniusWithComplement` (`✓ std3`).

*Citation.* Bahturin, Yuri; Centrone, Lucio; Pereira, Kauê (2026). *Quantum regularity of finite dimensional semisimple algebras*. DOI: [10.48550/arXiv.2608.21936](https://doi.org/10.48550/arXiv.2608.21936). URL: <https://arxiv.org/abs/2608.21936v1>.

*Commentary.*

A complement is a nontrivial proper subgroup with trivial intersection with each conjugate by an element outside it.

**Definition 1.4 (The Fitting subgroup).**

$$\forall H \in Type,\; [Group\left(H\right)], [Finite\left(H\right)], \operatorname{D5}.\operatorname{S3}.\operatorname{FiniteGroups}.\operatorname{BahturinCentronePereiraPeakGroups}.\operatorname{BCP31}.\operatorname{fitting}\left(H\right) = sSup\left(\{N: Subgroup\left(H\right) | ((\operatorname{Subgroup}.\operatorname{Normal}\left(N\right)) \land (\operatorname{Group}.\operatorname{IsNilpotent}\left(N\right)))\}\right)$$

*Formalization.* `D5/S3/FiniteGroups/BahturinCentronePereiraPeakGroups.fitting` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Bahturin, Yuri; Centrone, Lucio; Pereira, Kauê (2026). *Quantum regularity of finite dimensional semisimple algebras*. DOI: [10.48550/arXiv.2608.21936](https://doi.org/10.48550/arXiv.2608.21936). URL: <https://arxiv.org/abs/2608.21936v1>.

*Commentary.*

The Fitting subgroup is the supremum of the normal nilpotent subgroups.

**Theorem 1.5 (Normality of the Fitting subgroup).**

$$\forall H \in Type,\; [Group\left(H\right)], [Finite\left(H\right)], \operatorname{Subgroup}.\operatorname{Normal}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{FiniteGroups}.\operatorname{BahturinCentronePereiraPeakGroups}.\operatorname{BCP31}.\operatorname{fitting}\left(H\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/BahturinCentronePereiraPeakGroups.fitting_normal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bahturin, Yuri; Centrone, Lucio; Pereira, Kauê (2026). *Quantum regularity of finite dimensional semisimple algebras*. DOI: [10.48550/arXiv.2608.21936](https://doi.org/10.48550/arXiv.2608.21936). URL: <https://arxiv.org/abs/2608.21936v1>.

*Commentary.*

A supremum of normal subgroups is normal.

**Definition 1.6 (Cyclic Sylow subgroups).**

$$\forall T \in Type,\; [Group\left(T\right)], \operatorname{D5}.\operatorname{S3}.\operatorname{FiniteGroups}.\operatorname{BahturinCentronePereiraPeakGroups}.\operatorname{BCP31}.\operatorname{HasCyclicSylows}\left(T\right) = (\forall p \in \mathbb{N},\; [Fact\left(\operatorname{Nat}.\operatorname{Prime}\left(p\right)\right)], \forall P \in Sylow\left(p, T\right),\; IsCyclic\left(P\right))$$

*Formalization.* `D5/S3/FiniteGroups/BahturinCentronePereiraPeakGroups.HasCyclicSylows` (`✓ std3`).

*Citation.* Bahturin, Yuri; Centrone, Lucio; Pereira, Kauê (2026). *Quantum regularity of finite dimensional semisimple algebras*. DOI: [10.48550/arXiv.2608.21936](https://doi.org/10.48550/arXiv.2608.21936). URL: <https://arxiv.org/abs/2608.21936v1>.

*Commentary.*

Every Sylow subgroup, at every prime, is cyclic.

**Definition 1.7 (Excluded prime divisors).**

$$\forall T \in Type,\; \operatorname{D5}.\operatorname{S3}.\operatorname{FiniteGroups}.\operatorname{BahturinCentronePereiraPeakGroups}.\operatorname{BCP31}.\operatorname{HasAllowedOrder}\left(T\right) = ((\neg 2 \mid \operatorname{Nat}.\operatorname{card}\left(T\right)) \land ((\neg 3 \mid \operatorname{Nat}.\operatorname{card}\left(T\right)) \land (\neg 5 \mid \operatorname{Nat}.\operatorname{card}\left(T\right))))$$

*Formalization.* `D5/S3/FiniteGroups/BahturinCentronePereiraPeakGroups.HasAllowedOrder` (`✓ std3`).

*Citation.* Bahturin, Yuri; Centrone, Lucio; Pereira, Kauê (2026). *Quantum regularity of finite dimensional semisimple algebras*. DOI: [10.48550/arXiv.2608.21936](https://doi.org/10.48550/arXiv.2608.21936). URL: <https://arxiv.org/abs/2608.21936v1>.

*Commentary.*

The order is divisible by none of two, three, and five.

**Definition 1.8 (Structure of the quotient of a complement).**

$$\forall H \in Type,\; [Group\left(H\right)], [Finite\left(H\right)], \operatorname{D5}.\operatorname{S3}.\operatorname{FiniteGroups}.\operatorname{BahturinCentronePereiraPeakGroups}.\operatorname{BCP31}.\operatorname{ComplementCondition}\left(H\right) = (\exists Hzero \in Subgroup\left((H / \operatorname{D5}.\operatorname{S3}.\operatorname{FiniteGroups}.\operatorname{BahturinCentronePereiraPeakGroups}.\operatorname{BCP31}.\operatorname{fitting}\left(H\right))\right),\; (\operatorname{Subgroup}.\operatorname{Normal}\left(Hzero\right)) \land (\exists T \in Type,\; \exists [Group\left(T\right)], \exists [Finite\left(T\right)], (Nonempty\left((Hzero \equiv^{*} (\operatorname{Matrix}.\operatorname{SpecialLinearGroup}\left(Fin\left(2\right), ZMod\left(5\right)\right) \times T))\right)) \land ((\operatorname{D5}.\operatorname{S3}.\operatorname{FiniteGroups}.\operatorname{BahturinCentronePereiraPeakGroups}.\operatorname{BCP31}.\operatorname{HasCyclicSylows}\left(T\right)) \land (\operatorname{D5}.\operatorname{S3}.\operatorname{FiniteGroups}.\operatorname{BahturinCentronePereiraPeakGroups}.\operatorname{BCP31}.\operatorname{HasAllowedOrder}\left(T\right)))))$$

*Formalization.* `D5/S3/FiniteGroups/BahturinCentronePereiraPeakGroups.ComplementCondition` (`✓ std3`).

*Citation.* Bahturin, Yuri; Centrone, Lucio; Pereira, Kauê (2026). *Quantum regularity of finite dimensional semisimple algebras*. DOI: [10.48550/arXiv.2608.21936](https://doi.org/10.48550/arXiv.2608.21936). URL: <https://arxiv.org/abs/2608.21936v1>.

*Commentary.*

The quotient by the Fitting subgroup contains a normal subgroup isomorphic to the product of SL(2, ZMod 5) and a group with cyclic Sylow subgroups and the specified prime exclusions.

**Definition 1.9 (The Frobenius alternative).**

$$\forall G \in Type,\; [Group\left(G\right)], [Finite\left(G\right)], \operatorname{D5}.\operatorname{S3}.\operatorname{FiniteGroups}.\operatorname{BahturinCentronePereiraPeakGroups}.\operatorname{BCP31}.\operatorname{AlternativeTwo}\left(G\right) = (\exists H \in Subgroup\left(G\right),\; (\operatorname{D5}.\operatorname{S3}.\operatorname{FiniteGroups}.\operatorname{BahturinCentronePereiraPeakGroups}.\operatorname{BCP31}.\operatorname{IsFrobeniusWithComplement}\left(G, H\right)) \land (\operatorname{D5}.\operatorname{S3}.\operatorname{FiniteGroups}.\operatorname{BahturinCentronePereiraPeakGroups}.\operatorname{BCP31}.\operatorname{ComplementCondition}\left(H\right)))$$

*Formalization.* `D5/S3/FiniteGroups/BahturinCentronePereiraPeakGroups.AlternativeTwo` (`✓ std3`).

*Citation.* Bahturin, Yuri; Centrone, Lucio; Pereira, Kauê (2026). *Quantum regularity of finite dimensional semisimple algebras*. DOI: [10.48550/arXiv.2608.21936](https://doi.org/10.48550/arXiv.2608.21936). URL: <https://arxiv.org/abs/2608.21936v1>.

*Commentary.*

The group has a Frobenius complement satisfying the quotient condition.

**Definition 1.10 (Conjecture 31).**

$$\operatorname{D5}.\operatorname{S3}.\operatorname{FiniteGroups}.\operatorname{BahturinCentronePereiraPeakGroups}.\operatorname{BCP31}.\operatorname{claim} = (\forall G \in Type,\; [Group\left(G\right)], [Finite\left(G\right)], (\operatorname{D5}.\operatorname{S3}.\operatorname{FiniteGroups}.\operatorname{BahturinCentronePereiraPeakGroups}.\operatorname{BCP31}.\operatorname{IsPeak}\left(G\right)) \Rightarrow (((\operatorname{Group}.\operatorname{IsSolvable}\left(G\right)) \lor (\operatorname{D5}.\operatorname{S3}.\operatorname{FiniteGroups}.\operatorname{BahturinCentronePereiraPeakGroups}.\operatorname{BCP31}.\operatorname{AlternativeTwo}\left(G\right))) \land (\neg ((\operatorname{Group}.\operatorname{IsSolvable}\left(G\right)) \land (\operatorname{D5}.\operatorname{S3}.\operatorname{FiniteGroups}.\operatorname{BahturinCentronePereiraPeakGroups}.\operatorname{BCP31}.\operatorname{AlternativeTwo}\left(G\right))))))$$

*Formalization.* `D5/S3/FiniteGroups/BahturinCentronePereiraPeakGroups.claim` (`✓ std3`).

*Citation.* Bahturin, Yuri; Centrone, Lucio; Pereira, Kauê (2026). *Quantum regularity of finite dimensional semisimple algebras*. DOI: [10.48550/arXiv.2608.21936](https://doi.org/10.48550/arXiv.2608.21936). URL: <https://arxiv.org/abs/2608.21936v1>.

*Commentary.*

For every finite peak group, exactly one of solvability and the Frobenius alternative holds.

**Theorem 1.11 (The conjecture is false).**

$$\neg (\forall G \in Type,\; [Group\left(G\right)], [Finite\left(G\right)], (\operatorname{D5}.\operatorname{S3}.\operatorname{FiniteGroups}.\operatorname{BahturinCentronePereiraPeakGroups}.\operatorname{BCP31}.\operatorname{IsPeak}\left(G\right)) \Rightarrow (((\operatorname{Group}.\operatorname{IsSolvable}\left(G\right)) \lor (\operatorname{D5}.\operatorname{S3}.\operatorname{FiniteGroups}.\operatorname{BahturinCentronePereiraPeakGroups}.\operatorname{BCP31}.\operatorname{AlternativeTwo}\left(G\right))) \land (\neg ((\operatorname{Group}.\operatorname{IsSolvable}\left(G\right)) \land (\operatorname{D5}.\operatorname{S3}.\operatorname{FiniteGroups}.\operatorname{BahturinCentronePereiraPeakGroups}.\operatorname{BCP31}.\operatorname{AlternativeTwo}\left(G\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/BahturinCentronePereiraPeakGroups.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bahturin, Yuri; Centrone, Lucio; Pereira, Kauê (2026). *Quantum regularity of finite dimensional semisimple algebras*. DOI: [10.48550/arXiv.2608.21936](https://doi.org/10.48550/arXiv.2608.21936). URL: <https://arxiv.org/abs/2608.21936v1>.

*Commentary.*

The additive group of (ZMod 11) squared admits the displayed fixed-point-free SL(2, ZMod 5) action. Its semidirect product has a simple representation of dimension 120 and every simple degree divides 120. An abelian direct factor of order two preserves these degrees. The SL(2, ZMod 5) quotient prevents solvability, while the central element from the direct factor prevents every Frobenius complement.

## References

- Truth anchor: `D5/S3/FiniteGroups/BahturinCentronePereiraPeakGroups.AlternativeTwo`
- Truth anchor: `D5/S3/FiniteGroups/BahturinCentronePereiraPeakGroups.ComplementCondition`
- Truth anchor: `D5/S3/FiniteGroups/BahturinCentronePereiraPeakGroups.HasAllowedOrder`
- Truth anchor: `D5/S3/FiniteGroups/BahturinCentronePereiraPeakGroups.HasCyclicSylows`
- Truth anchor: `D5/S3/FiniteGroups/BahturinCentronePereiraPeakGroups.IsFrobeniusWithComplement`
- Truth anchor: `D5/S3/FiniteGroups/BahturinCentronePereiraPeakGroups.IsPeak`
- Truth anchor: `D5/S3/FiniteGroups/BahturinCentronePereiraPeakGroups.claim`
- Truth anchor: `D5/S3/FiniteGroups/BahturinCentronePereiraPeakGroups.degreeSet`
- Truth anchor: `D5/S3/FiniteGroups/BahturinCentronePereiraPeakGroups.fitting`
- Truth anchor: `D5/S3/FiniteGroups/BahturinCentronePereiraPeakGroups.fitting_normal`
- Truth anchor: `D5/S3/FiniteGroups/BahturinCentronePereiraPeakGroups.result`
- Dependency: [D5/S3/FiniteGroups/ComplexCharacterAbelianProducts](ComplexCharacterAbelianProducts.md)
- Dependency: [D5/S3/FiniteGroups/FiniteCharacterAlgebra](FiniteCharacterAlgebra.md)
- Dependency: [D5/S3/FiniteGroups/FrobeniusCentralObstruction](FrobeniusCentralObstruction.md)
- Dependency: [D5/S3/FiniteGroups/FrobeniusCharacterDegrees](FrobeniusCharacterDegrees.md)
- Dependency: [D5/S3/FiniteGroups/InducedCharacterFormula](InducedCharacterFormula.md)
- Dependency: [D5/S3/FiniteGroups/MackeyCharacterFormula](MackeyCharacterFormula.md)
