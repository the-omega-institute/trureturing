# Mackey Character Formula

## Abstract

Finite representation theory relates simple modules, characters, conjugation and induction.

**Definition 1.1 (Of linear character).**

$$\forall k \in Type*,\; \forall G \in Type*,\; [\operatorname{CommRing}\left(k\right)], [\operatorname{Monoid}\left(G\right)], \forall chi \in \operatorname{MonoidHom}\left(G, \operatorname{Units}\left(k\right)\right),\; \operatorname{D5}.\operatorname{S3}.\operatorname{FiniteGroups}.\operatorname{MackeyCharacterFormula}.\operatorname{FDRep}.\operatorname{ofLinearCharacter}\left(chi\right) = (\operatorname{FDRep}.\operatorname{of}\left(((\operatorname{Algebra}.\operatorname{lsmul}\left(k, k, k\right)).\operatorname{toMonoidHom}).\operatorname{comp}\left((\operatorname{Units}.\operatorname{coeHom}\left(k\right)).\operatorname{comp}\left(chi\right)\right)\right))$$

*Formalization.* `D5/S3/FiniteGroups/MackeyCharacterFormula.ofLinearCharacter` (`✓ std3`).

*Citation.* The Tau Ceti contributors; Claude (2026). *TauCeti finite representation and character theory*. URL: <https://github.com/TauCetiProject/TauCeti/tree/a780c7ad6beb23f60a17351a492d177878020ad5>.

*Commentary.*

The formula defines the displayed algebraic construction.

**Theorem 1.2 (Finrank of linear character).**

$$\forall k \in Type*,\; \forall G \in Type*,\; [\operatorname{Field}\left(k\right)], [\operatorname{Monoid}\left(G\right)], \forall chi \in \operatorname{MonoidHom}\left(G, \operatorname{Units}\left(k\right)\right),\; (\operatorname{Module}.\operatorname{finrank}\left(k, \operatorname{FGModuleCat}.\operatorname{carrier}\left(\operatorname{Action}.\operatorname{V}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{FiniteGroups}.\operatorname{MackeyCharacterFormula}.\operatorname{FDRep}.\operatorname{ofLinearCharacter}\left(chi\right)\right)\right)\right)) = (1)$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/MackeyCharacterFormula.finrank_ofLinearCharacter` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors; Claude (2026). *TauCeti finite representation and character theory*. URL: <https://github.com/TauCetiProject/TauCeti/tree/a780c7ad6beb23f60a17351a492d177878020ad5>.

*Commentary.*

The displayed conclusion holds under the stated hypotheses.

**Theorem 1.3 (Simple ind fdr ep of linear character iff).**

$$\forall k \in Type*,\; \forall G \in Type*,\; [\operatorname{Field}\left(k\right)], [\operatorname{Group}\left(G\right)], \forall N \in \operatorname{Subgroup}\left(G\right),\; [\operatorname{Subgroup}.\operatorname{Normal}\left(N\right)], [\operatorname{Finite}\left(G\right)], [\operatorname{IsAlgClosed}\left(k\right)], [\operatorname{CharZero}\left(k\right)], \forall chi \in \operatorname{MonoidHom}\left(\operatorname{Subtype}\left(\lambda (x: G) \mapsto (\operatorname{Membership}.\operatorname{mem}\left(N, x\right))\right), \operatorname{Units}\left(k\right)\right),\; (\operatorname{CategoryTheory}.\operatorname{Simple}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{FiniteGroups}.\operatorname{InducedCharacterFormula}.\operatorname{TauCeti}.\operatorname{indFDRep}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{FiniteGroups}.\operatorname{MackeyCharacterFormula}.\operatorname{FDRep}.\operatorname{ofLinearCharacter}\left(chi\right)\right)\right)) \Leftrightarrow (\forall s \in G,\; (\neg (\operatorname{Membership}.\operatorname{mem}\left(N, s\right))) \Rightarrow (\exists x \in \operatorname{Subtype}\left(\lambda (x: G) \mapsto (\operatorname{Membership}.\operatorname{mem}\left(N, x\right))\right),\; \operatorname{Ne}\left(\operatorname{DFunLike}.\operatorname{coe}\left(chi, \operatorname{DFunLike}.\operatorname{coe}\left(\operatorname{DFunLike}.\operatorname{coe}\left(\operatorname{MulAut}.\operatorname{conjNormal}, s\right), x\right)\right), \operatorname{DFunLike}.\operatorname{coe}\left(chi, x\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/MackeyCharacterFormula.simple_indFDRep_ofLinearCharacter_iff` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors; Claude (2026). *TauCeti finite representation and character theory*. URL: <https://github.com/TauCetiProject/TauCeti/tree/a780c7ad6beb23f60a17351a492d177878020ad5>.

*Commentary.*

The displayed conclusion holds under the stated hypotheses.

## References

- Truth anchor: `D5/S3/FiniteGroups/MackeyCharacterFormula.finrank_ofLinearCharacter`
- Truth anchor: `D5/S3/FiniteGroups/MackeyCharacterFormula.ofLinearCharacter`
- Truth anchor: `D5/S3/FiniteGroups/MackeyCharacterFormula.simple_indFDRep_ofLinearCharacter_iff`
- Dependency: [D5/S3/FiniteGroups/CliffordConstituents](CliffordConstituents.md)
- Dependency: [D5/S3/FiniteGroups/CliffordDecomposition](CliffordDecomposition.md)
- Dependency: [D5/S3/FiniteGroups/FiniteCharacterAlgebra](FiniteCharacterAlgebra.md)
- Dependency: [D5/S3/FiniteGroups/InducedCharacterFormula](InducedCharacterFormula.md)
