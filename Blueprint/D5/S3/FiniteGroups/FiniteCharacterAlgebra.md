# Finite Character Algebra

## Abstract

Finite representation theory relates simple modules, characters, conjugation and induction.

**Theorem 1.1 (To submodule bot).**

$$\forall A \in Type*,\; \forall G \in Type*,\; \forall W \in Type*,\; [\operatorname{Semiring}\left(A\right)], [\operatorname{Monoid}\left(G\right)], [\operatorname{AddCommMonoid}\left(W\right)], [\operatorname{Module}\left(A, W\right)], \forall rho \in \operatorname{Representation}\left(A, G, W\right),\; (\operatorname{Subrepresentation}.\operatorname{toSubmodule}\left((\operatorname{Bot}.\operatorname{bot}: \operatorname{Subrepresentation}\left(rho\right))\right)) = ((\operatorname{Bot}.\operatorname{bot}: \operatorname{Submodule}\left(A, W\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/FiniteCharacterAlgebra.toSubmodule_bot` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors; Claude (2026). *TauCeti finite representation and character theory*. URL: <https://github.com/TauCetiProject/TauCeti/tree/a780c7ad6beb23f60a17351a492d177878020ad5>.

*Commentary.*

The displayed conclusion holds under the stated hypotheses.

**Theorem 1.2 (To submodule top).**

$$\forall A \in Type*,\; \forall G \in Type*,\; \forall W \in Type*,\; [\operatorname{Semiring}\left(A\right)], [\operatorname{Monoid}\left(G\right)], [\operatorname{AddCommMonoid}\left(W\right)], [\operatorname{Module}\left(A, W\right)], \forall rho \in \operatorname{Representation}\left(A, G, W\right),\; (\operatorname{Subrepresentation}.\operatorname{toSubmodule}\left((\operatorname{Top}.\operatorname{top}: \operatorname{Subrepresentation}\left(rho\right))\right)) = ((\operatorname{Top}.\operatorname{top}: \operatorname{Submodule}\left(A, W\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/FiniteCharacterAlgebra.toSubmodule_top` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors; Claude (2026). *TauCeti finite representation and character theory*. URL: <https://github.com/TauCetiProject/TauCeti/tree/a780c7ad6beb23f60a17351a492d177878020ad5>.

*Commentary.*

The displayed conclusion holds under the stated hypotheses.

**Definition 1.3 (As module equiv as submodule).**

$$\forall A \in Type*,\; \forall G \in Type*,\; \forall W \in Type*,\; [\operatorname{CommSemiring}\left(A\right)], [\operatorname{Monoid}\left(G\right)], [\operatorname{AddCommMonoid}\left(W\right)], [\operatorname{Module}\left(A, W\right)], \forall rho \in \operatorname{Representation}\left(A, G, W\right),\; \forall sigma \in \operatorname{Subrepresentation}\left(rho\right),\; \operatorname{D5}.\operatorname{S3}.\operatorname{FiniteGroups}.\operatorname{FiniteCharacterAlgebra}.\operatorname{Subrepresentation}.\operatorname{asModuleEquivAsSubmodule}\left(sigma\right) = (\operatorname{LinearEquiv}.\operatorname{mk}\left(\operatorname{LinearMap}.\operatorname{mk}\left(\operatorname{AddHom}.\operatorname{mk}\left(\lambda (x: \operatorname{Representation}.\operatorname{asModule}\left(\operatorname{Subrepresentation}.\operatorname{toRepresentation}\left(sigma\right)\right)) \mapsto (\operatorname{Subtype}.\operatorname{mk}\left(\operatorname{DFunLike}.\operatorname{coe}\left(\operatorname{LinearEquiv}.\operatorname{symm}\left(\operatorname{Representation}.\operatorname{asModuleEquiv}\left(rho\right)\right), \operatorname{Subtype}.\operatorname{val}\left(\operatorname{DFunLike}.\operatorname{coe}\left(\operatorname{Representation}.\operatorname{asModuleEquiv}\left(\operatorname{Subrepresentation}.\operatorname{toRepresentation}\left(sigma\right)\right), x\right)\right)\right)\right))\right)\right), \lambda (x: \operatorname{Subtype}\left(\lambda (x: \operatorname{Representation}.\operatorname{asModule}\left(rho\right)) \mapsto (\operatorname{Membership}.\operatorname{mem}\left(\operatorname{Subrepresentation}.\operatorname{asSubmodule}\left(sigma\right), x\right))\right)) \mapsto (\operatorname{DFunLike}.\operatorname{coe}\left(\operatorname{LinearEquiv}.\operatorname{symm}\left(\operatorname{Representation}.\operatorname{asModuleEquiv}\left(\operatorname{Subrepresentation}.\operatorname{toRepresentation}\left(sigma\right)\right)\right), \operatorname{Subtype}.\operatorname{mk}\left(\operatorname{DFunLike}.\operatorname{coe}\left(\operatorname{Representation}.\operatorname{asModuleEquiv}\left(rho\right), \operatorname{Subtype}.\operatorname{val}\left(x\right)\right)\right)\right))\right))$$

*Formalization.* `D5/S3/FiniteGroups/FiniteCharacterAlgebra.asModuleEquivAsSubmodule` (`✓ std3`).

*Citation.* The Tau Ceti contributors; Claude (2026). *TauCeti finite representation and character theory*. URL: <https://github.com/TauCetiProject/TauCeti/tree/a780c7ad6beb23f60a17351a492d177878020ad5>.

*Commentary.*

The formula defines the displayed algebraic construction.

**Theorem 1.4 (Is simple module as submodule iff).**

$$\forall A \in Type*,\; \forall G \in Type*,\; \forall W \in Type*,\; [\operatorname{CommRing}\left(A\right)], [\operatorname{Monoid}\left(G\right)], [\operatorname{AddCommGroup}\left(W\right)], [\operatorname{Module}\left(A, W\right)], \forall rho \in \operatorname{Representation}\left(A, G, W\right),\; \forall sigma \in \operatorname{Subrepresentation}\left(rho\right),\; (\operatorname{IsSimpleModule}\left(\operatorname{MonoidAlgebra}\left(A, G\right), \operatorname{Subtype}\left(\lambda (x: \operatorname{Representation}.\operatorname{asModule}\left(rho\right)) \mapsto (\operatorname{Membership}.\operatorname{mem}\left(\operatorname{Subrepresentation}.\operatorname{asSubmodule}\left(sigma\right), x\right))\right)\right)) \Leftrightarrow (\operatorname{IsAtom}\left(sigma\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/FiniteCharacterAlgebra.isSimpleModule_asSubmodule_iff` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors; Claude (2026). *TauCeti finite representation and character theory*. URL: <https://github.com/TauCetiProject/TauCeti/tree/a780c7ad6beb23f60a17351a492d177878020ad5>.

*Commentary.*

The displayed conclusion holds under the stated hypotheses.

**Theorem 1.5 (Simple of is irreducible).**

$$\forall k \in Type*,\; \forall G \in Type*,\; [\operatorname{Field}\left(k\right)], [\operatorname{Monoid}\left(G\right)], \forall X \in \operatorname{FDRep}\left(k, G\right),\; [\operatorname{Representation}.\operatorname{IsIrreducible}\left(\operatorname{FDRep}.\rho\left(X\right)\right)], \operatorname{CategoryTheory}.\operatorname{Simple}\left(X\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/FiniteCharacterAlgebra.simple_of_isIrreducible` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors; Claude (2026). *TauCeti finite representation and character theory*. URL: <https://github.com/TauCetiProject/TauCeti/tree/a780c7ad6beb23f60a17351a492d177878020ad5>.

*Commentary.*

The displayed conclusion holds under the stated hypotheses.

**Theorem 1.6 (Is irreducible of simple).**

$$\forall k \in Type*,\; \forall G \in Type*,\; [\operatorname{Field}\left(k\right)], [\operatorname{Monoid}\left(G\right)], \forall X \in \operatorname{FDRep}\left(k, G\right),\; [\operatorname{CategoryTheory}.\operatorname{Simple}\left(X\right)], \operatorname{Representation}.\operatorname{IsIrreducible}\left(\operatorname{FDRep}.\rho\left(X\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/FiniteCharacterAlgebra.isIrreducible_of_simple` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors; Claude (2026). *TauCeti finite representation and character theory*. URL: <https://github.com/TauCetiProject/TauCeti/tree/a780c7ad6beb23f60a17351a492d177878020ad5>.

*Commentary.*

The displayed conclusion holds under the stated hypotheses.

**Theorem 1.7 (Character action res).**

$$\forall k \in Type*,\; \forall G \in Type*,\; \forall H \in Type*,\; [\operatorname{Field}\left(k\right)], [\operatorname{Monoid}\left(G\right)], [\operatorname{Monoid}\left(H\right)], \forall V \in \operatorname{FDRep}\left(k, G\right),\; \forall phi \in \operatorname{MonoidHom}\left(H, G\right),\; \forall h \in H,\; (\operatorname{FDRep}.\operatorname{character}\left(\operatorname{CategoryTheory}.\operatorname{Functor}.\operatorname{obj}\left(\operatorname{Action}.\operatorname{res}\left(\operatorname{FGModuleCat}\left(k\right), phi\right), V\right), h\right)) = (\operatorname{FDRep}.\operatorname{character}\left(V, \operatorname{DFunLike}.\operatorname{coe}\left(phi, h\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/FiniteCharacterAlgebra.character_actionRes` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors; Claude (2026). *TauCeti finite representation and character theory*. URL: <https://github.com/TauCetiProject/TauCeti/tree/a780c7ad6beb23f60a17351a492d177878020ad5>.

*Commentary.*

The displayed conclusion holds under the stated hypotheses.

**Theorem 1.8 (Module finite forget object).**

$$\forall R \in Type*,\; \forall G \in Type*,\; [\operatorname{CommRing}\left(R\right)], [\operatorname{Monoid}\left(G\right)], \forall A \in \operatorname{FDRep}\left(R, G\right),\; \operatorname{Module}.\operatorname{Finite}\left(R, \operatorname{Rep}.\operatorname{V}\left(\operatorname{CategoryTheory}.\operatorname{Functor}.\operatorname{obj}\left(\operatorname{CategoryTheory}.\operatorname{forget}_{2}\left(\operatorname{FDRep}\left(R, G\right), \operatorname{Rep}\left(R, G\right)\right), A\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/FiniteCharacterAlgebra.moduleFiniteForgetObject` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* The Tau Ceti contributors; Claude (2026). *TauCeti finite representation and character theory*. URL: <https://github.com/TauCetiProject/TauCeti/tree/a780c7ad6beb23f60a17351a492d177878020ad5>.

*Commentary.*

The displayed conclusion holds under the stated hypotheses.

**Theorem 1.9 (Finrank forget object).**

$$\forall R \in Type*,\; \forall G \in Type*,\; [\operatorname{CommRing}\left(R\right)], [\operatorname{Monoid}\left(G\right)], \forall A \in \operatorname{FDRep}\left(R, G\right),\; (\operatorname{Module}.\operatorname{finrank}\left(R, \operatorname{Rep}.\operatorname{V}\left(\operatorname{CategoryTheory}.\operatorname{Functor}.\operatorname{obj}\left(\operatorname{CategoryTheory}.\operatorname{forget}_{2}\left(\operatorname{FDRep}\left(R, G\right), \operatorname{Rep}\left(R, G\right)\right), A\right)\right)\right)) = (\operatorname{Module}.\operatorname{finrank}\left(R, \operatorname{FGModuleCat}.\operatorname{carrier}\left(\operatorname{Action}.\operatorname{V}\left(A\right)\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/FiniteCharacterAlgebra.finrankForgetObject` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors; Claude (2026). *TauCeti finite representation and character theory*. URL: <https://github.com/TauCetiProject/TauCeti/tree/a780c7ad6beb23f60a17351a492d177878020ad5>.

*Commentary.*

The displayed conclusion holds under the stated hypotheses.

**Theorem 1.10 (Character forget object).**

$$\forall k \in Type*,\; \forall G \in Type*,\; [\operatorname{Field}\left(k\right)], [\operatorname{Monoid}\left(G\right)], \forall A \in \operatorname{FDRep}\left(k, G\right),\; \forall g \in G,\; (\operatorname{Representation}.\operatorname{character}\left(\operatorname{Rep}.\rho\left(\operatorname{CategoryTheory}.\operatorname{Functor}.\operatorname{obj}\left(\operatorname{CategoryTheory}.\operatorname{forget}_{2}\left(\operatorname{FDRep}\left(k, G\right), \operatorname{Rep}\left(k, G\right)\right), A\right)\right), g\right)) = (\operatorname{FDRep}.\operatorname{character}\left(A, g\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/FiniteCharacterAlgebra.characterForgetObject` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors; Claude (2026). *TauCeti finite representation and character theory*. URL: <https://github.com/TauCetiProject/TauCeti/tree/a780c7ad6beb23f60a17351a492d177878020ad5>.

*Commentary.*

The displayed conclusion holds under the stated hypotheses.

**Theorem 1.11 (Of eq self).**

$$\forall R \in Type*,\; \forall G \in Type*,\; [\operatorname{CommRing}\left(R\right)], [\operatorname{Monoid}\left(G\right)], \forall A \in \operatorname{FDRep}\left(R, G\right),\; (\operatorname{FDRep}.\operatorname{of}\left(\operatorname{FDRep}.\rho\left(A\right)\right)) = (A)$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/FiniteCharacterAlgebra.of_ρ_eq_self` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors; Claude (2026). *TauCeti finite representation and character theory*. URL: <https://github.com/TauCetiProject/TauCeti/tree/a780c7ad6beb23f60a17351a492d177878020ad5>.

*Commentary.*

The displayed conclusion holds under the stated hypotheses.

**Definition 1.12 (Of shrink).**

$$\forall k \in Type*,\; \forall G \in Type*,\; \forall V \in Type*,\; [\operatorname{CommRing}\left(k\right)], [\operatorname{Monoid}\left(G\right)], [\operatorname{AddCommGroup}\left(V\right)], [\operatorname{Module}\left(k, V\right)], [\operatorname{Module}.\operatorname{Finite}\left(k, V\right)], \forall rho \in \operatorname{Representation}\left(k, G, V\right),\; \operatorname{D5}.\operatorname{S3}.\operatorname{FiniteGroups}.\operatorname{FiniteCharacterAlgebra}.\operatorname{FDRep}.\operatorname{ofShrink}\left(rho\right) = (\operatorname{FDRep}.\operatorname{of}\left(\operatorname{MonoidHom}.\operatorname{comp}\left(\operatorname{RingEquiv}.\operatorname{toMonoidHom}\left(\operatorname{LinearEquiv}.\operatorname{conjRingEquiv}\left(\operatorname{LinearEquiv}.\operatorname{symm}\left(\operatorname{Shrink}.\operatorname{linearEquiv}\left(k, V\right)\right)\right)\right), rho\right)\right))$$

*Formalization.* `D5/S3/FiniteGroups/FiniteCharacterAlgebra.ofShrink` (`✓ std3`).

*Citation.* The Tau Ceti contributors; Claude (2026). *TauCeti finite representation and character theory*. URL: <https://github.com/TauCetiProject/TauCeti/tree/a780c7ad6beb23f60a17351a492d177878020ad5>.

*Commentary.*

The formula defines the displayed algebraic construction.

**Definition 1.13 (Of shrink equiv).**

$$\forall k \in Type*,\; \forall G \in Type*,\; \forall V \in Type*,\; [\operatorname{CommRing}\left(k\right)], [\operatorname{Monoid}\left(G\right)], [\operatorname{AddCommGroup}\left(V\right)], [\operatorname{Module}\left(k, V\right)], [\operatorname{Module}.\operatorname{Finite}\left(k, V\right)], \forall rho \in \operatorname{Representation}\left(k, G, V\right),\; \operatorname{D5}.\operatorname{S3}.\operatorname{FiniteGroups}.\operatorname{FiniteCharacterAlgebra}.\operatorname{FDRep}.\operatorname{ofShrinkEquiv}\left(rho\right) = (\operatorname{Representation}.\operatorname{Equiv}.\operatorname{mk}\left(\operatorname{Shrink}.\operatorname{linearEquiv}\left(k, V\right)\right))$$

*Formalization.* `D5/S3/FiniteGroups/FiniteCharacterAlgebra.ofShrinkEquiv` (`✓ std3`).

*Citation.* The Tau Ceti contributors; Claude (2026). *TauCeti finite representation and character theory*. URL: <https://github.com/TauCetiProject/TauCeti/tree/a780c7ad6beb23f60a17351a492d177878020ad5>.

*Commentary.*

The formula defines the displayed algebraic construction.

**Theorem 1.14 (Finrank of shrink).**

$$\forall k \in Type*,\; \forall G \in Type*,\; \forall V \in Type*,\; [\operatorname{CommRing}\left(k\right)], [\operatorname{Monoid}\left(G\right)], [\operatorname{AddCommGroup}\left(V\right)], [\operatorname{Module}\left(k, V\right)], [\operatorname{Module}.\operatorname{Finite}\left(k, V\right)], \forall rho \in \operatorname{Representation}\left(k, G, V\right),\; (\operatorname{Module}.\operatorname{finrank}\left(k, \operatorname{FGModuleCat}.\operatorname{carrier}\left(\operatorname{Action}.\operatorname{V}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{FiniteGroups}.\operatorname{FiniteCharacterAlgebra}.\operatorname{FDRep}.\operatorname{ofShrink}\left(rho\right)\right)\right)\right)) = (\operatorname{Module}.\operatorname{finrank}\left(k, V\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/FiniteCharacterAlgebra.finrank_ofShrink` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors; Claude (2026). *TauCeti finite representation and character theory*. URL: <https://github.com/TauCetiProject/TauCeti/tree/a780c7ad6beb23f60a17351a492d177878020ad5>.

*Commentary.*

The displayed conclusion holds under the stated hypotheses.

**Theorem 1.15 (Character of shrink).**

$$\forall k \in Type*,\; \forall G \in Type*,\; \forall V \in Type*,\; [\operatorname{Field}\left(k\right)], [\operatorname{Monoid}\left(G\right)], [\operatorname{AddCommGroup}\left(V\right)], [\operatorname{Module}\left(k, V\right)], [\operatorname{FiniteDimensional}\left(k, V\right)], \forall rho \in \operatorname{Representation}\left(k, G, V\right),\; \forall g \in G,\; (\operatorname{FDRep}.\operatorname{character}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{FiniteGroups}.\operatorname{FiniteCharacterAlgebra}.\operatorname{FDRep}.\operatorname{ofShrink}\left(rho\right), g\right)) = (\operatorname{Representation}.\operatorname{character}\left(rho, g\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/FiniteCharacterAlgebra.character_ofShrink` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors; Claude (2026). *TauCeti finite representation and character theory*. URL: <https://github.com/TauCetiProject/TauCeti/tree/a780c7ad6beb23f60a17351a492d177878020ad5>.

*Commentary.*

The displayed conclusion holds under the stated hypotheses.

**Definition 1.16 (Class function).**

$$\forall k \in Type*,\; \forall G \in Type*,\; [\operatorname{Semiring}\left(k\right)], [\operatorname{Group}\left(G\right)], \operatorname{D5}.\operatorname{S3}.\operatorname{FiniteGroups}.\operatorname{FiniteCharacterAlgebra}.\operatorname{TauCeti}.\operatorname{ClassFunction}\left(k, G\right) = (\operatorname{Submodule}.\operatorname{mk}\left(\operatorname{AddSubmonoid}.\operatorname{mk}\left(\operatorname{AddSubsemigroup}.\operatorname{mk}\left(\operatorname{Set}.\operatorname{ofPred}\left(\lambda (f: (G) \to (k)) \mapsto (\forall g \in G,\; \forall h \in G,\; (f\left(\operatorname{HMul}.\operatorname{hMul}\left(\operatorname{HMul}.\operatorname{hMul}\left(h, g\right), \operatorname{Inv}.\operatorname{inv}\left(h\right)\right)\right)) = (f\left(g\right)))\right)\right)\right)\right))$$

*Formalization.* `D5/S3/FiniteGroups/FiniteCharacterAlgebra.ClassFunction` (`✓ std3`).

*Citation.* The Tau Ceti contributors; Claude (2026). *TauCeti finite representation and character theory*. URL: <https://github.com/TauCetiProject/TauCeti/tree/a780c7ad6beb23f60a17351a492d177878020ad5>.

*Commentary.*

The formula defines the displayed algebraic construction.

**Theorem 1.17 (Mem iff).**

$$\forall k \in Type*,\; \forall G \in Type*,\; [\operatorname{Semiring}\left(k\right)], [\operatorname{Group}\left(G\right)], \forall f \in (G) \to (k),\; (\operatorname{Membership}.\operatorname{mem}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{FiniteGroups}.\operatorname{FiniteCharacterAlgebra}.\operatorname{TauCeti}.\operatorname{ClassFunction}\left(k, G\right), f\right)) \Leftrightarrow (\forall g \in G,\; \forall h \in G,\; (f\left(\operatorname{HMul}.\operatorname{hMul}\left(\operatorname{HMul}.\operatorname{hMul}\left(h, g\right), \operatorname{Inv}.\operatorname{inv}\left(h\right)\right)\right)) = (f\left(g\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/FiniteCharacterAlgebra.mem_iff` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors; Claude (2026). *TauCeti finite representation and character theory*. URL: <https://github.com/TauCetiProject/TauCeti/tree/a780c7ad6beb23f60a17351a492d177878020ad5>.

*Commentary.*

The displayed conclusion holds under the stated hypotheses.

**Definition 1.18 (To conj classes).**

$$\forall k \in Type*,\; \forall G \in Type*,\; [\operatorname{Semiring}\left(k\right)], [\operatorname{Group}\left(G\right)], \forall f \in \operatorname{Subtype}\left(\lambda (x: (G) \to (k)) \mapsto (\operatorname{Membership}.\operatorname{mem}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{FiniteGroups}.\operatorname{FiniteCharacterAlgebra}.\operatorname{TauCeti}.\operatorname{ClassFunction}\left(k, G\right), x\right))\right),\; \operatorname{D5}.\operatorname{S3}.\operatorname{FiniteGroups}.\operatorname{FiniteCharacterAlgebra}.\operatorname{TauCeti}.\operatorname{ClassFunction}.\operatorname{toConjClasses}\left(f\right) = (\operatorname{Quotient}.\operatorname{lift}\left(\operatorname{Subtype}.\operatorname{val}\left(f\right)\right))$$

*Formalization.* `D5/S3/FiniteGroups/FiniteCharacterAlgebra.toConjClasses` (`✓ std3`).

*Citation.* The Tau Ceti contributors; Claude (2026). *TauCeti finite representation and character theory*. URL: <https://github.com/TauCetiProject/TauCeti/tree/a780c7ad6beb23f60a17351a492d177878020ad5>.

*Commentary.*

The formula defines the displayed algebraic construction.

**Theorem 1.19 (To conj classes mk).**

$$\forall k \in Type*,\; \forall G \in Type*,\; [\operatorname{Semiring}\left(k\right)], [\operatorname{Group}\left(G\right)], \forall f \in \operatorname{Subtype}\left(\lambda (x: (G) \to (k)) \mapsto (\operatorname{Membership}.\operatorname{mem}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{FiniteGroups}.\operatorname{FiniteCharacterAlgebra}.\operatorname{TauCeti}.\operatorname{ClassFunction}\left(k, G\right), x\right))\right),\; \forall g \in G,\; (\operatorname{D5}.\operatorname{S3}.\operatorname{FiniteGroups}.\operatorname{FiniteCharacterAlgebra}.\operatorname{TauCeti}.\operatorname{ClassFunction}.\operatorname{toConjClasses}\left(f, \operatorname{ConjClasses}.\operatorname{mk}\left(g\right)\right)) = (\operatorname{Subtype}.\operatorname{val}\left(f, g\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/FiniteCharacterAlgebra.toConjClasses_mk` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors; Claude (2026). *TauCeti finite representation and character theory*. URL: <https://github.com/TauCetiProject/TauCeti/tree/a780c7ad6beb23f60a17351a492d177878020ad5>.

*Commentary.*

The displayed conclusion holds under the stated hypotheses.

**Definition 1.20 (Comap).**

$$\forall k \in Type*,\; \forall G \in Type*,\; [\operatorname{Semiring}\left(k\right)], [\operatorname{Group}\left(G\right)], \forall H \in Type*,\; [\operatorname{Group}\left(H\right)], \forall phi \in \operatorname{MonoidHom}\left(H, G\right),\; \operatorname{D5}.\operatorname{S3}.\operatorname{FiniteGroups}.\operatorname{FiniteCharacterAlgebra}.\operatorname{TauCeti}.\operatorname{ClassFunction}.\operatorname{comap}\left(phi\right) = (\operatorname{LinearMap}.\operatorname{mk}\left(\operatorname{AddHom}.\operatorname{mk}\left(\lambda (f: \operatorname{Subtype}\left(\lambda (x: (G) \to (k)) \mapsto (\operatorname{Membership}.\operatorname{mem}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{FiniteGroups}.\operatorname{FiniteCharacterAlgebra}.\operatorname{TauCeti}.\operatorname{ClassFunction}\left(k, G\right), x\right))\right)) \mapsto (\operatorname{Subtype}.\operatorname{mk}\left(\lambda (x: H) \mapsto (\operatorname{Subtype}.\operatorname{val}\left(f, \operatorname{DFunLike}.\operatorname{coe}\left(phi, x\right)\right))\right))\right)\right))$$

*Formalization.* `D5/S3/FiniteGroups/FiniteCharacterAlgebra.comap` (`✓ std3`).

*Citation.* The Tau Ceti contributors; Claude (2026). *TauCeti finite representation and character theory*. URL: <https://github.com/TauCetiProject/TauCeti/tree/a780c7ad6beb23f60a17351a492d177878020ad5>.

*Commentary.*

The formula defines the displayed algebraic construction.

**Theorem 1.21 (Comap apply).**

$$\forall k \in Type*,\; \forall G \in Type*,\; [\operatorname{Semiring}\left(k\right)], [\operatorname{Group}\left(G\right)], \forall H \in Type*,\; [\operatorname{Group}\left(H\right)], \forall phi \in \operatorname{MonoidHom}\left(H, G\right),\; \forall f \in \operatorname{Subtype}\left(\lambda (x: (G) \to (k)) \mapsto (\operatorname{Membership}.\operatorname{mem}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{FiniteGroups}.\operatorname{FiniteCharacterAlgebra}.\operatorname{TauCeti}.\operatorname{ClassFunction}\left(k, G\right), x\right))\right),\; \forall x \in H,\; (\operatorname{Subtype}.\operatorname{val}\left(\operatorname{DFunLike}.\operatorname{coe}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{FiniteGroups}.\operatorname{FiniteCharacterAlgebra}.\operatorname{TauCeti}.\operatorname{ClassFunction}.\operatorname{comap}\left(phi\right), f\right), x\right)) = (\operatorname{Subtype}.\operatorname{val}\left(f, \operatorname{DFunLike}.\operatorname{coe}\left(phi, x\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/FiniteCharacterAlgebra.comap_apply` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors; Claude (2026). *TauCeti finite representation and character theory*. URL: <https://github.com/TauCetiProject/TauCeti/tree/a780c7ad6beb23f60a17351a492d177878020ad5>.

*Commentary.*

The displayed conclusion holds under the stated hypotheses.

**Theorem 1.22 (Sum eq sum conj classes).**

$$\forall k \in Type*,\; \forall G \in Type*,\; [\operatorname{Semiring}\left(k\right)], [\operatorname{Group}\left(G\right)], [\operatorname{Fintype}\left(G\right)], [\operatorname{Fintype}\left(\operatorname{ConjClasses}\left(G\right)\right)], \forall f \in \operatorname{Subtype}\left(\lambda (x: (G) \to (k)) \mapsto (\operatorname{Membership}.\operatorname{mem}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{FiniteGroups}.\operatorname{FiniteCharacterAlgebra}.\operatorname{TauCeti}.\operatorname{ClassFunction}\left(k, G\right), x\right))\right),\; (\operatorname{Finset}.\operatorname{sum}\left(\operatorname{Finset}.\operatorname{univ}, \lambda (g: G) \mapsto (\operatorname{Subtype}.\operatorname{val}\left(f, g\right))\right)) = (\operatorname{Finset}.\operatorname{sum}\left(\operatorname{Finset}.\operatorname{univ}, \lambda (C: \operatorname{ConjClasses}\left(G\right)) \mapsto (\operatorname{HMul}.\operatorname{hMul}\left(\operatorname{Nat}.\operatorname{cast}\left(\operatorname{Nat}.\operatorname{card}\left(\operatorname{Set}.\operatorname{Elem}\left(\operatorname{ConjClasses}.\operatorname{carrier}\left(C\right)\right)\right)\right), \operatorname{D5}.\operatorname{S3}.\operatorname{FiniteGroups}.\operatorname{FiniteCharacterAlgebra}.\operatorname{TauCeti}.\operatorname{ClassFunction}.\operatorname{toConjClasses}\left(f, C\right)\right))\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/FiniteCharacterAlgebra.sum_eq_sum_conjClasses` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors; Claude (2026). *TauCeti finite representation and character theory*. URL: <https://github.com/TauCetiProject/TauCeti/tree/a780c7ad6beb23f60a17351a492d177878020ad5>.

*Commentary.*

The displayed conclusion holds under the stated hypotheses.

**Definition 1.23 (Of character).**

$$\forall k \in Type*,\; \forall G \in Type*,\; [\operatorname{Field}\left(k\right)], [\operatorname{Group}\left(G\right)], \forall V \in Type*,\; [\operatorname{AddCommGroup}\left(V\right)], [\operatorname{Module}\left(k, V\right)], \forall rho \in \operatorname{Representation}\left(k, G, V\right),\; \operatorname{D5}.\operatorname{S3}.\operatorname{FiniteGroups}.\operatorname{FiniteCharacterAlgebra}.\operatorname{TauCeti}.\operatorname{ClassFunction}.\operatorname{ofCharacter}\left(rho\right) = (\operatorname{Subtype}.\operatorname{mk}\left(\operatorname{Representation}.\operatorname{character}\left(rho\right)\right))$$

*Formalization.* `D5/S3/FiniteGroups/FiniteCharacterAlgebra.ofCharacter` (`✓ std3`).

*Citation.* The Tau Ceti contributors; Claude (2026). *TauCeti finite representation and character theory*. URL: <https://github.com/TauCetiProject/TauCeti/tree/a780c7ad6beb23f60a17351a492d177878020ad5>.

*Commentary.*

The formula defines the displayed algebraic construction.

**Theorem 1.24 (Of character apply).**

$$\forall k \in Type*,\; \forall G \in Type*,\; [\operatorname{Field}\left(k\right)], [\operatorname{Group}\left(G\right)], \forall V \in Type*,\; [\operatorname{AddCommGroup}\left(V\right)], [\operatorname{Module}\left(k, V\right)], \forall rho \in \operatorname{Representation}\left(k, G, V\right),\; \forall g \in G,\; (\operatorname{Subtype}.\operatorname{val}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{FiniteGroups}.\operatorname{FiniteCharacterAlgebra}.\operatorname{TauCeti}.\operatorname{ClassFunction}.\operatorname{ofCharacter}\left(rho\right), g\right)) = (\operatorname{Representation}.\operatorname{character}\left(rho, g\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/FiniteCharacterAlgebra.ofCharacter_apply` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors; Claude (2026). *TauCeti finite representation and character theory*. URL: <https://github.com/TauCetiProject/TauCeti/tree/a780c7ad6beb23f60a17351a492d177878020ad5>.

*Commentary.*

The displayed conclusion holds under the stated hypotheses.

**Theorem 1.25 (Action res comp).**

$$\forall H \in Type*,\; \forall K \in Type*,\; \forall L \in Type*,\; [\operatorname{Monoid}\left(H\right)], [\operatorname{Monoid}\left(K\right)], [\operatorname{Monoid}\left(L\right)], \forall V \in Type*,\; [\operatorname{CategoryTheory}.\operatorname{Category}\left(V\right)], \forall phi \in \operatorname{MonoidHom}\left(K, L\right),\; \forall psi \in \operatorname{MonoidHom}\left(H, K\right),\; (\operatorname{Action}.\operatorname{res}\left(V, \operatorname{MonoidHom}.\operatorname{comp}\left(phi, psi\right)\right)) = (\operatorname{CategoryTheory}.\operatorname{Functor}.\operatorname{comp}\left(\operatorname{Action}.\operatorname{res}\left(V, phi\right), \operatorname{Action}.\operatorname{res}\left(V, psi\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/FiniteCharacterAlgebra.actionRes_comp` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors; Claude (2026). *TauCeti finite representation and character theory*. URL: <https://github.com/TauCetiProject/TauCeti/tree/a780c7ad6beb23f60a17351a492d177878020ad5>.

*Commentary.*

The displayed conclusion holds under the stated hypotheses.

**Theorem 1.26 (Finrank hom res mul equiv).**

$$\forall k \in Type*,\; [\operatorname{Field}\left(k\right)], \forall M \in Type*,\; \forall MPrime \in Type*,\; [\operatorname{Group}\left(M\right)], [\operatorname{Group}\left(MPrime\right)], \forall e \in \operatorname{MulEquiv}\left(M, MPrime\right),\; \forall X \in \operatorname{FDRep}\left(k, MPrime\right),\; \forall Y \in \operatorname{FDRep}\left(k, MPrime\right),\; (\operatorname{Module}.\operatorname{finrank}\left(k, \operatorname{Quiver}.\operatorname{Hom}\left(\operatorname{CategoryTheory}.\operatorname{Functor}.\operatorname{obj}\left(\operatorname{Action}.\operatorname{res}\left(\operatorname{FGModuleCat}\left(k\right), \operatorname{MonoidHom}.\operatorname{ofClass}\left(e\right)\right), X\right), \operatorname{CategoryTheory}.\operatorname{Functor}.\operatorname{obj}\left(\operatorname{Action}.\operatorname{res}\left(\operatorname{FGModuleCat}\left(k\right), \operatorname{MonoidHom}.\operatorname{ofClass}\left(e\right)\right), Y\right)\right)\right)) = (\operatorname{Module}.\operatorname{finrank}\left(k, \operatorname{Quiver}.\operatorname{Hom}\left(X, Y\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/FiniteCharacterAlgebra.finrank_hom_res_mulEquiv` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors; Claude (2026). *TauCeti finite representation and character theory*. URL: <https://github.com/TauCetiProject/TauCeti/tree/a780c7ad6beb23f60a17351a492d177878020ad5>.

*Commentary.*

The displayed conclusion holds under the stated hypotheses.

**Theorem 1.27 (Is irreducible comp surjective iff).**

$$\forall k \in Type*,\; [\operatorname{Field}\left(k\right)], \forall H \in Type*,\; \forall K \in Type*,\; [\operatorname{Monoid}\left(H\right)], [\operatorname{Monoid}\left(K\right)], \forall V \in Type*,\; [\operatorname{AddCommGroup}\left(V\right)], [\operatorname{Module}\left(k, V\right)], \forall f \in \operatorname{MonoidHom}\left(H, K\right),\; (\operatorname{Function}.\operatorname{Surjective}\left(\operatorname{DFunLike}.\operatorname{coe}\left(f\right)\right)) \Rightarrow (\forall rho \in \operatorname{Representation}\left(k, K, V\right),\; (\operatorname{Representation}.\operatorname{IsIrreducible}\left(\operatorname{MonoidHom}.\operatorname{comp}\left(rho, f\right)\right)) \Leftrightarrow (\operatorname{Representation}.\operatorname{IsIrreducible}\left(rho\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/FiniteCharacterAlgebra.isIrreducible_comp_surjective_iff` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors; Claude (2026). *TauCeti finite representation and character theory*. URL: <https://github.com/TauCetiProject/TauCeti/tree/a780c7ad6beb23f60a17351a492d177878020ad5>.

*Commentary.*

The displayed conclusion holds under the stated hypotheses.

**Theorem 1.28 (Comap subtype of fdr ep).**

$$\forall k \in Type*,\; \forall G \in Type*,\; [\operatorname{Group}\left(G\right)], [\operatorname{Field}\left(k\right)], \forall S \in \operatorname{Subgroup}\left(G\right),\; \forall B \in \operatorname{FDRep}\left(k, G\right),\; (\operatorname{DFunLike}.\operatorname{coe}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{FiniteGroups}.\operatorname{FiniteCharacterAlgebra}.\operatorname{TauCeti}.\operatorname{ClassFunction}.\operatorname{comap}\left(\operatorname{Subgroup}.\operatorname{subtype}\left(S\right)\right), \operatorname{D5}.\operatorname{S3}.\operatorname{FiniteGroups}.\operatorname{FiniteCharacterAlgebra}.\operatorname{TauCeti}.\operatorname{ClassFunction}.\operatorname{ofCharacter}\left(\operatorname{FDRep}.\rho\left(B\right)\right)\right)) = (\operatorname{D5}.\operatorname{S3}.\operatorname{FiniteGroups}.\operatorname{FiniteCharacterAlgebra}.\operatorname{TauCeti}.\operatorname{ClassFunction}.\operatorname{ofCharacter}\left(\operatorname{FDRep}.\rho\left(\operatorname{CategoryTheory}.\operatorname{Functor}.\operatorname{obj}\left(\operatorname{Action}.\operatorname{res}\left(\operatorname{FGModuleCat}\left(k\right), \operatorname{Subgroup}.\operatorname{subtype}\left(S\right)\right), B\right)\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/FiniteCharacterAlgebra.comap_subtype_ofFDRep` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors; Claude (2026). *TauCeti finite representation and character theory*. URL: <https://github.com/TauCetiProject/TauCeti/tree/a780c7ad6beb23f60a17351a492d177878020ad5>.

*Commentary.*

The displayed conclusion holds under the stated hypotheses.

**Definition 1.29 (Class sum).**

$$\forall G \in Type*,\; [\operatorname{Group}\left(G\right)], [\operatorname{Fintype}\left(G\right)], [\operatorname{DecidableEq}\left(G\right)], \forall k \in Type*,\; [\operatorname{Semiring}\left(k\right)], \forall C \in \operatorname{ConjClasses}\left(G\right),\; \operatorname{D5}.\operatorname{S3}.\operatorname{FiniteGroups}.\operatorname{FiniteCharacterAlgebra}.\operatorname{TauCeti}.\operatorname{classSum}\left(k, C\right) = (\operatorname{Finset}.\operatorname{sum}\left(\operatorname{Finset}.\operatorname{univ}, \lambda (x: \operatorname{Set}.\operatorname{Elem}\left(\operatorname{ConjClasses}.\operatorname{carrier}\left(C\right)\right)) \mapsto (\operatorname{DFunLike}.\operatorname{coe}\left(\operatorname{MonoidAlgebra}.\operatorname{of}\left(k, G\right), \operatorname{Subtype}.\operatorname{val}\left(x\right)\right))\right))$$

*Formalization.* `D5/S3/FiniteGroups/FiniteCharacterAlgebra.classSum` (`✓ std3`).

*Citation.* The Tau Ceti contributors; Claude (2026). *TauCeti finite representation and character theory*. URL: <https://github.com/TauCetiProject/TauCeti/tree/a780c7ad6beb23f60a17351a492d177878020ad5>.

*Commentary.*

The formula defines the displayed algebraic construction.

**Theorem 1.30 (Class sum eq sum).**

$$\forall G \in Type*,\; [\operatorname{Group}\left(G\right)], [\operatorname{Fintype}\left(G\right)], [\operatorname{DecidableEq}\left(G\right)], \forall k \in Type*,\; [\operatorname{Semiring}\left(k\right)], \forall C \in \operatorname{ConjClasses}\left(G\right),\; (\operatorname{D5}.\operatorname{S3}.\operatorname{FiniteGroups}.\operatorname{FiniteCharacterAlgebra}.\operatorname{TauCeti}.\operatorname{classSum}\left(k, C\right)) = (\operatorname{Finset}.\operatorname{sum}\left(\operatorname{Finset}.\operatorname{univ}, \lambda (x: \operatorname{Set}.\operatorname{Elem}\left(\operatorname{ConjClasses}.\operatorname{carrier}\left(C\right)\right)) \mapsto (\operatorname{DFunLike}.\operatorname{coe}\left(\operatorname{MonoidAlgebra}.\operatorname{of}\left(k, G\right), \operatorname{Subtype}.\operatorname{val}\left(x\right)\right))\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/FiniteCharacterAlgebra.classSum_eq_sum` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors; Claude (2026). *TauCeti finite representation and character theory*. URL: <https://github.com/TauCetiProject/TauCeti/tree/a780c7ad6beb23f60a17351a492d177878020ad5>.

*Commentary.*

The displayed conclusion holds under the stated hypotheses.

**Definition 1.31 (Class sum center).**

$$\forall G \in Type*,\; \forall k \in Type*,\; [\operatorname{Group}\left(G\right)], [\operatorname{Fintype}\left(G\right)], [\operatorname{DecidableEq}\left(G\right)], [\operatorname{CommSemiring}\left(k\right)], \forall C \in \operatorname{ConjClasses}\left(G\right),\; \operatorname{D5}.\operatorname{S3}.\operatorname{FiniteGroups}.\operatorname{FiniteCharacterAlgebra}.\operatorname{TauCeti}.\operatorname{classSumCenter}\left(C\right) = (\operatorname{Subtype}.\operatorname{mk}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{FiniteGroups}.\operatorname{FiniteCharacterAlgebra}.\operatorname{TauCeti}.\operatorname{classSum}\left(k, C\right)\right))$$

*Formalization.* `D5/S3/FiniteGroups/FiniteCharacterAlgebra.classSumCenter` (`✓ std3`).

*Citation.* The Tau Ceti contributors; Claude (2026). *TauCeti finite representation and character theory*. URL: <https://github.com/TauCetiProject/TauCeti/tree/a780c7ad6beb23f60a17351a492d177878020ad5>.

*Commentary.*

The formula defines the displayed algebraic construction.

**Theorem 1.32 (Class sum center coe).**

$$\forall G \in Type*,\; \forall k \in Type*,\; [\operatorname{Group}\left(G\right)], [\operatorname{Fintype}\left(G\right)], [\operatorname{DecidableEq}\left(G\right)], [\operatorname{CommSemiring}\left(k\right)], \forall C \in \operatorname{ConjClasses}\left(G\right),\; (\operatorname{Subtype}.\operatorname{val}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{FiniteGroups}.\operatorname{FiniteCharacterAlgebra}.\operatorname{TauCeti}.\operatorname{classSumCenter}\left(C\right)\right)) = (\operatorname{D5}.\operatorname{S3}.\operatorname{FiniteGroups}.\operatorname{FiniteCharacterAlgebra}.\operatorname{TauCeti}.\operatorname{classSum}\left(k, C\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/FiniteCharacterAlgebra.classSumCenter_coe` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors; Claude (2026). *TauCeti finite representation and character theory*. URL: <https://github.com/TauCetiProject/TauCeti/tree/a780c7ad6beb23f60a17351a492d177878020ad5>.

*Commentary.*

The displayed conclusion holds under the stated hypotheses.

**Definition 1.33 (End alg equiv self of is simple module).**

$$\forall k \in Type*,\; \forall A \in Type*,\; \forall S \in Type*,\; [\operatorname{Field}\left(k\right)], [\operatorname{IsAlgClosed}\left(k\right)], [\operatorname{Ring}\left(A\right)], [\operatorname{Algebra}\left(k, A\right)], [\operatorname{AddCommGroup}\left(S\right)], [\operatorname{Module}\left(k, S\right)], [\operatorname{Module}\left(A, S\right)], [\operatorname{IsScalarTower}\left(k, A, S\right)], [\operatorname{IsSimpleModule}\left(A, S\right)], [\operatorname{FiniteDimensional}\left(k, S\right)], \operatorname{D5}.\operatorname{S3}.\operatorname{FiniteGroups}.\operatorname{FiniteCharacterAlgebra}.\operatorname{TauCeti}.\operatorname{endAlgEquivSelfOfIsSimpleModule} = (\operatorname{AlgEquiv}.\operatorname{symm}\left(\operatorname{AlgEquiv}.\operatorname{ofBijective}\left(\operatorname{Algebra}.\operatorname{ofId}\left(k, \operatorname{Module}.\operatorname{End}\left(A, S\right)\right)\right)\right))$$

*Formalization.* `D5/S3/FiniteGroups/FiniteCharacterAlgebra.endAlgEquivSelfOfIsSimpleModule` (`✓ std3`).

*Citation.* The Tau Ceti contributors; Claude (2026). *TauCeti finite representation and character theory*. URL: <https://github.com/TauCetiProject/TauCeti/tree/a780c7ad6beb23f60a17351a492d177878020ad5>.

*Commentary.*

The formula defines the displayed algebraic construction.

**Theorem 1.34 (End alg equiv self of is simple module smul).**

$$\forall k \in Type*,\; \forall A \in Type*,\; \forall S \in Type*,\; [\operatorname{Field}\left(k\right)], [\operatorname{IsAlgClosed}\left(k\right)], [\operatorname{Ring}\left(A\right)], [\operatorname{Algebra}\left(k, A\right)], [\operatorname{AddCommGroup}\left(S\right)], [\operatorname{Module}\left(k, S\right)], [\operatorname{Module}\left(A, S\right)], [\operatorname{IsScalarTower}\left(k, A, S\right)], [\operatorname{IsSimpleModule}\left(A, S\right)], [\operatorname{FiniteDimensional}\left(k, S\right)], \forall f \in \operatorname{Module}.\operatorname{End}\left(A, S\right),\; \forall s \in S,\; (\operatorname{HSMul}.\operatorname{hSMul}\left(\operatorname{DFunLike}.\operatorname{coe}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{FiniteGroups}.\operatorname{FiniteCharacterAlgebra}.\operatorname{TauCeti}.\operatorname{endAlgEquivSelfOfIsSimpleModule}, f\right), s\right)) = (\operatorname{DFunLike}.\operatorname{coe}\left(f, s\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/FiniteCharacterAlgebra.endAlgEquivSelfOfIsSimpleModule_smul` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors; Claude (2026). *TauCeti finite representation and character theory*. URL: <https://github.com/TauCetiProject/TauCeti/tree/a780c7ad6beb23f60a17351a492d177878020ad5>.

*Commentary.*

The displayed conclusion holds under the stated hypotheses.

**Definition 1.35 (Hom congr right).**

$$\forall k \in Type*,\; \forall A \in Type*,\; [\operatorname{CommSemiring}\left(k\right)], [\operatorname{Semiring}\left(A\right)], [\operatorname{Algebra}\left(k, A\right)], \forall S \in Type*,\; [\operatorname{AddCommMonoid}\left(S\right)], [\operatorname{Module}\left(A, S\right)], \forall N \in Type*,\; [\operatorname{AddCommMonoid}\left(N\right)], [\operatorname{Module}\left(A, N\right)], [\operatorname{Module}\left(k, N\right)], [\operatorname{IsScalarTower}\left(k, A, N\right)], \forall P \in Type*,\; [\operatorname{AddCommMonoid}\left(P\right)], [\operatorname{Module}\left(A, P\right)], [\operatorname{Module}\left(k, P\right)], [\operatorname{IsScalarTower}\left(k, A, P\right)], \forall e \in \operatorname{LinearEquiv}\left(\operatorname{RingHom}.\operatorname{id}\left(A\right), N, P\right),\; \operatorname{D5}.\operatorname{S3}.\operatorname{FiniteGroups}.\operatorname{FiniteCharacterAlgebra}.\operatorname{TauCeti}.\operatorname{homCongrRight}\left(k, e\right) = (\operatorname{LinearEquiv}.\operatorname{mk}\left(\operatorname{LinearMap}.\operatorname{mk}\left(\operatorname{AddHom}.\operatorname{mk}\left(\operatorname{Equiv}.\operatorname{toFun}\left(\operatorname{AddEquiv}.\operatorname{toEquiv}\left(\operatorname{LinearEquiv}.\operatorname{arrowCongrAddEquiv}\left(\operatorname{LinearEquiv}.\operatorname{refl}\left(A, S\right), e\right)\right)\right)\right)\right), \operatorname{Equiv}.\operatorname{invFun}\left(\operatorname{AddEquiv}.\operatorname{toEquiv}\left(\operatorname{LinearEquiv}.\operatorname{arrowCongrAddEquiv}\left(\operatorname{LinearEquiv}.\operatorname{refl}\left(A, S\right), e\right)\right)\right)\right))$$

*Formalization.* `D5/S3/FiniteGroups/FiniteCharacterAlgebra.homCongrRight` (`✓ std3`).

*Citation.* The Tau Ceti contributors; Claude (2026). *TauCeti finite representation and character theory*. URL: <https://github.com/TauCetiProject/TauCeti/tree/a780c7ad6beb23f60a17351a492d177878020ad5>.

*Commentary.*

The formula defines the displayed algebraic construction.

**Theorem 1.36 (Finrank linear map eq zero of is empty linear equiv).**

$$\forall k \in Type*,\; \forall A \in Type*,\; \forall S \in Type*,\; \forall N \in Type*,\; [\operatorname{CommSemiring}\left(k\right)], [\operatorname{Nontrivial}\left(k\right)], [\operatorname{Ring}\left(A\right)], [\operatorname{Algebra}\left(k, A\right)], [\operatorname{AddCommGroup}\left(S\right)], [\operatorname{Module}\left(A, S\right)], [\operatorname{IsSimpleModule}\left(A, S\right)], [\operatorname{AddCommGroup}\left(N\right)], [\operatorname{Module}\left(k, N\right)], [\operatorname{Module}\left(A, N\right)], [\operatorname{IsScalarTower}\left(k, A, N\right)], [\operatorname{IsSimpleModule}\left(A, N\right)], (\operatorname{IsEmpty}\left(\operatorname{LinearEquiv}\left(\operatorname{RingHom}.\operatorname{id}\left(A\right), S, N\right)\right)) \Rightarrow ((\operatorname{Module}.\operatorname{finrank}\left(k, \operatorname{LinearMap}\left(\operatorname{RingHom}.\operatorname{id}\left(A\right), S, N\right)\right)) = (0))$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/FiniteCharacterAlgebra.finrank_linearMap_eq_zero_of_isEmpty_linearEquiv` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors; Claude (2026). *TauCeti finite representation and character theory*. URL: <https://github.com/TauCetiProject/TauCeti/tree/a780c7ad6beb23f60a17351a492d177878020ad5>.

*Commentary.*

The displayed conclusion holds under the stated hypotheses.

**Theorem 1.37 (Finrank linear map eq one of nonempty linear equiv).**

$$\forall k \in Type*,\; \forall A \in Type*,\; \forall S \in Type*,\; [\operatorname{Field}\left(k\right)], [\operatorname{IsAlgClosed}\left(k\right)], [\operatorname{Ring}\left(A\right)], [\operatorname{Algebra}\left(k, A\right)], [\operatorname{AddCommGroup}\left(S\right)], [\operatorname{Module}\left(k, S\right)], [\operatorname{Module}\left(A, S\right)], [\operatorname{IsScalarTower}\left(k, A, S\right)], [\operatorname{IsSimpleModule}\left(A, S\right)], [\operatorname{FiniteDimensional}\left(k, S\right)], \forall N \in Type*,\; [\operatorname{AddCommGroup}\left(N\right)], [\operatorname{Module}\left(k, N\right)], [\operatorname{Module}\left(A, N\right)], [\operatorname{IsScalarTower}\left(k, A, N\right)], (\operatorname{LinearEquiv}\left(\operatorname{RingHom}.\operatorname{id}\left(A\right), S, N\right)) \to ((\operatorname{Module}.\operatorname{finrank}\left(k, \operatorname{LinearMap}\left(\operatorname{RingHom}.\operatorname{id}\left(A\right), S, N\right)\right)) = (1))$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/FiniteCharacterAlgebra.finrank_linearMap_eq_one_of_nonempty_linearEquiv` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors; Claude (2026). *TauCeti finite representation and character theory*. URL: <https://github.com/TauCetiProject/TauCeti/tree/a780c7ad6beb23f60a17351a492d177878020ad5>.

*Commentary.*

The displayed conclusion holds under the stated hypotheses.

**Theorem 1.38 (Finite dimensional linear map of is simple module).**

$$\forall k \in Type*,\; \forall A \in Type*,\; \forall S \in Type*,\; [\operatorname{Field}\left(k\right)], [\operatorname{IsAlgClosed}\left(k\right)], [\operatorname{Ring}\left(A\right)], [\operatorname{Algebra}\left(k, A\right)], [\operatorname{AddCommGroup}\left(S\right)], [\operatorname{Module}\left(k, S\right)], [\operatorname{Module}\left(A, S\right)], [\operatorname{IsScalarTower}\left(k, A, S\right)], [\operatorname{IsSimpleModule}\left(A, S\right)], [\operatorname{FiniteDimensional}\left(k, S\right)], \forall N \in Type*,\; [\operatorname{AddCommGroup}\left(N\right)], [\operatorname{Module}\left(k, N\right)], [\operatorname{Module}\left(A, N\right)], [\operatorname{IsScalarTower}\left(k, A, N\right)], [\operatorname{IsSimpleModule}\left(A, N\right)], \operatorname{FiniteDimensional}\left(k, \operatorname{LinearMap}\left(\operatorname{RingHom}.\operatorname{id}\left(A\right), S, N\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/FiniteCharacterAlgebra.finiteDimensional_linearMap_of_isSimpleModule` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors; Claude (2026). *TauCeti finite representation and character theory*. URL: <https://github.com/TauCetiProject/TauCeti/tree/a780c7ad6beb23f60a17351a492d177878020ad5>.

*Commentary.*

The displayed conclusion holds under the stated hypotheses.

**Theorem 1.39 (Nontrivial).**

$$\forall k \in Type*,\; \forall G \in Type*,\; \forall V \in Type*,\; [\operatorname{Field}\left(k\right)], [\operatorname{Monoid}\left(G\right)], [\operatorname{AddCommGroup}\left(V\right)], [\operatorname{Module}\left(k, V\right)], \forall rho \in \operatorname{Representation}\left(k, G, V\right),\; (\operatorname{Representation}.\operatorname{IsIrreducible}\left(rho\right)) \Rightarrow (\operatorname{Nontrivial}\left(V\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/FiniteCharacterAlgebra.nontrivial` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors; Claude (2026). *TauCeti finite representation and character theory*. URL: <https://github.com/TauCetiProject/TauCeti/tree/a780c7ad6beb23f60a17351a492d177878020ad5>.

*Commentary.*

The displayed conclusion holds under the stated hypotheses.

**Theorem 1.40 (Finrank pos).**

$$\forall k \in Type*,\; \forall G \in Type*,\; \forall V \in Type*,\; [\operatorname{Field}\left(k\right)], [\operatorname{Monoid}\left(G\right)], [\operatorname{AddCommGroup}\left(V\right)], [\operatorname{Module}\left(k, V\right)], [\operatorname{FiniteDimensional}\left(k, V\right)], \forall rho \in \operatorname{Representation}\left(k, G, V\right),\; (\operatorname{Representation}.\operatorname{IsIrreducible}\left(rho\right)) \Rightarrow (\operatorname{LT}.\operatorname{lt}\left(0, \operatorname{Module}.\operatorname{finrank}\left(k, V\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/FiniteCharacterAlgebra.finrank_pos` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors; Claude (2026). *TauCeti finite representation and character theory*. URL: <https://github.com/TauCetiProject/TauCeti/tree/a780c7ad6beb23f60a17351a492d177878020ad5>.

*Commentary.*

The displayed conclusion holds under the stated hypotheses.

**Theorem 1.41 (Is irreducible of finrank eq one).**

$$\forall k \in Type*,\; \forall G \in Type*,\; \forall V \in Type*,\; [\operatorname{Field}\left(k\right)], [\operatorname{Monoid}\left(G\right)], [\operatorname{AddCommGroup}\left(V\right)], [\operatorname{Module}\left(k, V\right)], \forall rho \in \operatorname{Representation}\left(k, G, V\right),\; ((\operatorname{Module}.\operatorname{finrank}\left(k, V\right)) = (1)) \Rightarrow (\operatorname{Representation}.\operatorname{IsIrreducible}\left(rho\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/FiniteCharacterAlgebra.isIrreducible_of_finrank_eq_one` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors; Claude (2026). *TauCeti finite representation and character theory*. URL: <https://github.com/TauCetiProject/TauCeti/tree/a780c7ad6beb23f60a17351a492d177878020ad5>.

*Commentary.*

The displayed conclusion holds under the stated hypotheses.

**Theorem 1.42 (Is irreducible to representation of is atom).**

$$\forall k \in Type*,\; \forall G \in Type*,\; \forall V \in Type*,\; [\operatorname{Field}\left(k\right)], [\operatorname{Monoid}\left(G\right)], [\operatorname{AddCommGroup}\left(V\right)], [\operatorname{Module}\left(k, V\right)], \forall rho \in \operatorname{Representation}\left(k, G, V\right),\; \forall sigma \in \operatorname{Subrepresentation}\left(rho\right),\; (\operatorname{IsAtom}\left(sigma\right)) \Rightarrow (\operatorname{Representation}.\operatorname{IsIrreducible}\left(\operatorname{Subrepresentation}.\operatorname{toRepresentation}\left(sigma\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/FiniteCharacterAlgebra.isIrreducible_toRepresentation_of_isAtom` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors; Claude (2026). *TauCeti finite representation and character theory*. URL: <https://github.com/TauCetiProject/TauCeti/tree/a780c7ad6beb23f60a17351a492d177878020ad5>.

*Commentary.*

The displayed conclusion holds under the stated hypotheses.

**Theorem 1.43 (As algebra hom surjective of is irreducible).**

$$\forall k \in Type*,\; \forall G \in Type*,\; \forall V \in Type*,\; [\operatorname{Field}\left(k\right)], [\operatorname{Monoid}\left(G\right)], [\operatorname{AddCommGroup}\left(V\right)], [\operatorname{Module}\left(k, V\right)], [\operatorname{IsAlgClosed}\left(k\right)], [\operatorname{FiniteDimensional}\left(k, V\right)], \forall rho \in \operatorname{Representation}\left(k, G, V\right),\; (\operatorname{Representation}.\operatorname{IsIrreducible}\left(rho\right)) \Rightarrow (\operatorname{Function}.\operatorname{Surjective}\left(\operatorname{DFunLike}.\operatorname{coe}\left(\operatorname{Representation}.\operatorname{asAlgebraHom}\left(rho\right)\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/FiniteCharacterAlgebra.asAlgebraHom_surjective_of_isIrreducible` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors; Claude (2026). *TauCeti finite representation and character theory*. URL: <https://github.com/TauCetiProject/TauCeti/tree/a780c7ad6beb23f60a17351a492d177878020ad5>.

*Commentary.*

The displayed conclusion holds under the stated hypotheses.

**Theorem 1.44 (Exists is atom).**

$$\forall k \in Type*,\; \forall G \in Type*,\; \forall V \in Type*,\; [\operatorname{DivisionRing}\left(k\right)], [\operatorname{Monoid}\left(G\right)], [\operatorname{AddCommGroup}\left(V\right)], [\operatorname{Module}\left(k, V\right)], [\operatorname{FiniteDimensional}\left(k, V\right)], [\operatorname{Nontrivial}\left(V\right)], \forall rho \in \operatorname{Representation}\left(k, G, V\right),\; \exists sigma \in \operatorname{Subrepresentation}\left(rho\right),\; \operatorname{IsAtom}\left(sigma\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/FiniteCharacterAlgebra.exists_isAtom` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors; Claude (2026). *TauCeti finite representation and character theory*. URL: <https://github.com/TauCetiProject/TauCeti/tree/a780c7ad6beb23f60a17351a492d177878020ad5>.

*Commentary.*

The displayed conclusion holds under the stated hypotheses.

**Definition 1.45 (Character pairing).**

$$\forall k \in Type*,\; \forall G \in Type*,\; [\operatorname{Field}\left(k\right)], [\operatorname{Group}\left(G\right)], [\operatorname{Fintype}\left(G\right)], \operatorname{D5}.\operatorname{S3}.\operatorname{FiniteGroups}.\operatorname{FiniteCharacterAlgebra}.\operatorname{TauCeti}.\operatorname{ClassFunction}.\operatorname{characterPairing} = (\operatorname{LinearMap}.\operatorname{mk}_{2}\left(k, \lambda (f1: \operatorname{Subtype}\left(\lambda (x: (G) \to (k)) \mapsto (\operatorname{Membership}.\operatorname{mem}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{FiniteGroups}.\operatorname{FiniteCharacterAlgebra}.\operatorname{TauCeti}.\operatorname{ClassFunction}\left(k, G\right), x\right))\right)) \mapsto (\lambda (f2: \operatorname{Subtype}\left(\lambda (x: (G) \to (k)) \mapsto (\operatorname{Membership}.\operatorname{mem}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{FiniteGroups}.\operatorname{FiniteCharacterAlgebra}.\operatorname{TauCeti}.\operatorname{ClassFunction}\left(k, G\right), x\right))\right)) \mapsto (\operatorname{HMul}.\operatorname{hMul}\left(\operatorname{Inv}.\operatorname{inv}\left(\operatorname{Nat}.\operatorname{cast}\left(\operatorname{Nat}.\operatorname{card}\left(G\right)\right)\right), \operatorname{Finset}.\operatorname{sum}\left(\operatorname{Finset}.\operatorname{univ}, \lambda (g: G) \mapsto (\operatorname{HMul}.\operatorname{hMul}\left(\operatorname{Subtype}.\operatorname{val}\left(f1, g\right), \operatorname{Subtype}.\operatorname{val}\left(f2, \operatorname{Inv}.\operatorname{inv}\left(g\right)\right)\right))\right)\right)))\right))$$

*Formalization.* `D5/S3/FiniteGroups/FiniteCharacterAlgebra.characterPairing` (`✓ std3`).

*Citation.* The Tau Ceti contributors; Claude (2026). *TauCeti finite representation and character theory*. URL: <https://github.com/TauCetiProject/TauCeti/tree/a780c7ad6beb23f60a17351a492d177878020ad5>.

*Commentary.*

The formula defines the displayed algebraic construction.

**Theorem 1.46 (Character pairing apply).**

$$\forall k \in Type*,\; \forall G \in Type*,\; [\operatorname{Field}\left(k\right)], [\operatorname{Group}\left(G\right)], [\operatorname{Fintype}\left(G\right)], \forall f1 \in \operatorname{Subtype}\left(\lambda (x: (G) \to (k)) \mapsto (\operatorname{Membership}.\operatorname{mem}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{FiniteGroups}.\operatorname{FiniteCharacterAlgebra}.\operatorname{TauCeti}.\operatorname{ClassFunction}\left(k, G\right), x\right))\right),\; \forall f2 \in \operatorname{Subtype}\left(\lambda (x: (G) \to (k)) \mapsto (\operatorname{Membership}.\operatorname{mem}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{FiniteGroups}.\operatorname{FiniteCharacterAlgebra}.\operatorname{TauCeti}.\operatorname{ClassFunction}\left(k, G\right), x\right))\right),\; (\operatorname{DFunLike}.\operatorname{coe}\left(\operatorname{DFunLike}.\operatorname{coe}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{FiniteGroups}.\operatorname{FiniteCharacterAlgebra}.\operatorname{TauCeti}.\operatorname{ClassFunction}.\operatorname{characterPairing}, f1\right), f2\right)) = (\operatorname{HMul}.\operatorname{hMul}\left(\operatorname{Inv}.\operatorname{inv}\left(\operatorname{Nat}.\operatorname{cast}\left(\operatorname{Nat}.\operatorname{card}\left(G\right)\right)\right), \operatorname{Finset}.\operatorname{sum}\left(\operatorname{Finset}.\operatorname{univ}, \lambda (g: G) \mapsto (\operatorname{HMul}.\operatorname{hMul}\left(\operatorname{Subtype}.\operatorname{val}\left(f1, g\right), \operatorname{Subtype}.\operatorname{val}\left(f2, \operatorname{Inv}.\operatorname{inv}\left(g\right)\right)\right))\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/FiniteCharacterAlgebra.characterPairing_apply` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors; Claude (2026). *TauCeti finite representation and character theory*. URL: <https://github.com/TauCetiProject/TauCeti/tree/a780c7ad6beb23f60a17351a492d177878020ad5>.

*Commentary.*

The displayed conclusion holds under the stated hypotheses.

**Theorem 1.47 (Character pairing symm).**

$$\forall k \in Type*,\; \forall G \in Type*,\; [\operatorname{Field}\left(k\right)], [\operatorname{Group}\left(G\right)], [\operatorname{Fintype}\left(G\right)], \forall f1 \in \operatorname{Subtype}\left(\lambda (x: (G) \to (k)) \mapsto (\operatorname{Membership}.\operatorname{mem}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{FiniteGroups}.\operatorname{FiniteCharacterAlgebra}.\operatorname{TauCeti}.\operatorname{ClassFunction}\left(k, G\right), x\right))\right),\; \forall f2 \in \operatorname{Subtype}\left(\lambda (x: (G) \to (k)) \mapsto (\operatorname{Membership}.\operatorname{mem}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{FiniteGroups}.\operatorname{FiniteCharacterAlgebra}.\operatorname{TauCeti}.\operatorname{ClassFunction}\left(k, G\right), x\right))\right),\; (\operatorname{DFunLike}.\operatorname{coe}\left(\operatorname{DFunLike}.\operatorname{coe}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{FiniteGroups}.\operatorname{FiniteCharacterAlgebra}.\operatorname{TauCeti}.\operatorname{ClassFunction}.\operatorname{characterPairing}, f1\right), f2\right)) = (\operatorname{DFunLike}.\operatorname{coe}\left(\operatorname{DFunLike}.\operatorname{coe}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{FiniteGroups}.\operatorname{FiniteCharacterAlgebra}.\operatorname{TauCeti}.\operatorname{ClassFunction}.\operatorname{characterPairing}, f2\right), f1\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/FiniteCharacterAlgebra.characterPairing_symm` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors; Claude (2026). *TauCeti finite representation and character theory*. URL: <https://github.com/TauCetiProject/TauCeti/tree/a780c7ad6beb23f60a17351a492d177878020ad5>.

*Commentary.*

The displayed conclusion holds under the stated hypotheses.

**Theorem 1.48 (Character pairing of fdr ep eq finrank).**

$$\forall k \in Type*,\; \forall G \in Type*,\; [\operatorname{Field}\left(k\right)], [\operatorname{Group}\left(G\right)], [\operatorname{Fintype}\left(G\right)], [\operatorname{Invertible}\left(\operatorname{Nat}.\operatorname{cast}\left(\operatorname{Nat}.\operatorname{card}\left(G\right)\right)\right)], \forall V \in \operatorname{FDRep}\left(k, G\right),\; \forall W \in \operatorname{FDRep}\left(k, G\right),\; (\operatorname{DFunLike}.\operatorname{coe}\left(\operatorname{DFunLike}.\operatorname{coe}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{FiniteGroups}.\operatorname{FiniteCharacterAlgebra}.\operatorname{TauCeti}.\operatorname{ClassFunction}.\operatorname{characterPairing}, \operatorname{D5}.\operatorname{S3}.\operatorname{FiniteGroups}.\operatorname{FiniteCharacterAlgebra}.\operatorname{TauCeti}.\operatorname{ClassFunction}.\operatorname{ofCharacter}\left(\operatorname{FDRep}.\rho\left(V\right)\right)\right), \operatorname{D5}.\operatorname{S3}.\operatorname{FiniteGroups}.\operatorname{FiniteCharacterAlgebra}.\operatorname{TauCeti}.\operatorname{ClassFunction}.\operatorname{ofCharacter}\left(\operatorname{FDRep}.\rho\left(W\right)\right)\right)) = (\operatorname{Nat}.\operatorname{cast}\left(\operatorname{Module}.\operatorname{finrank}\left(k, \operatorname{Quiver}.\operatorname{Hom}\left(W, V\right)\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/FiniteCharacterAlgebra.characterPairing_ofFDRep_eq_finrank` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors; Claude (2026). *TauCeti finite representation and character theory*. URL: <https://github.com/TauCetiProject/TauCeti/tree/a780c7ad6beb23f60a17351a492d177878020ad5>.

*Commentary.*

The displayed conclusion holds under the stated hypotheses.

## References

- Truth anchor: `D5/S3/FiniteGroups/FiniteCharacterAlgebra.ClassFunction`
- Truth anchor: `D5/S3/FiniteGroups/FiniteCharacterAlgebra.actionRes_comp`
- Truth anchor: `D5/S3/FiniteGroups/FiniteCharacterAlgebra.asAlgebraHom_surjective_of_isIrreducible`
- Truth anchor: `D5/S3/FiniteGroups/FiniteCharacterAlgebra.asModuleEquivAsSubmodule`
- Truth anchor: `D5/S3/FiniteGroups/FiniteCharacterAlgebra.characterForgetObject`
- Truth anchor: `D5/S3/FiniteGroups/FiniteCharacterAlgebra.characterPairing`
- Truth anchor: `D5/S3/FiniteGroups/FiniteCharacterAlgebra.characterPairing_apply`
- Truth anchor: `D5/S3/FiniteGroups/FiniteCharacterAlgebra.characterPairing_ofFDRep_eq_finrank`
- Truth anchor: `D5/S3/FiniteGroups/FiniteCharacterAlgebra.characterPairing_symm`
- Truth anchor: `D5/S3/FiniteGroups/FiniteCharacterAlgebra.character_actionRes`
- Truth anchor: `D5/S3/FiniteGroups/FiniteCharacterAlgebra.character_ofShrink`
- Truth anchor: `D5/S3/FiniteGroups/FiniteCharacterAlgebra.classSum`
- Truth anchor: `D5/S3/FiniteGroups/FiniteCharacterAlgebra.classSumCenter`
- Truth anchor: `D5/S3/FiniteGroups/FiniteCharacterAlgebra.classSumCenter_coe`
- Truth anchor: `D5/S3/FiniteGroups/FiniteCharacterAlgebra.classSum_eq_sum`
- Truth anchor: `D5/S3/FiniteGroups/FiniteCharacterAlgebra.comap`
- Truth anchor: `D5/S3/FiniteGroups/FiniteCharacterAlgebra.comap_apply`
- Truth anchor: `D5/S3/FiniteGroups/FiniteCharacterAlgebra.comap_subtype_ofFDRep`
- Truth anchor: `D5/S3/FiniteGroups/FiniteCharacterAlgebra.endAlgEquivSelfOfIsSimpleModule`
- Truth anchor: `D5/S3/FiniteGroups/FiniteCharacterAlgebra.endAlgEquivSelfOfIsSimpleModule_smul`
- Truth anchor: `D5/S3/FiniteGroups/FiniteCharacterAlgebra.exists_isAtom`
- Truth anchor: `D5/S3/FiniteGroups/FiniteCharacterAlgebra.finiteDimensional_linearMap_of_isSimpleModule`
- Truth anchor: `D5/S3/FiniteGroups/FiniteCharacterAlgebra.finrankForgetObject`
- Truth anchor: `D5/S3/FiniteGroups/FiniteCharacterAlgebra.finrank_hom_res_mulEquiv`
- Truth anchor: `D5/S3/FiniteGroups/FiniteCharacterAlgebra.finrank_linearMap_eq_one_of_nonempty_linearEquiv`
- Truth anchor: `D5/S3/FiniteGroups/FiniteCharacterAlgebra.finrank_linearMap_eq_zero_of_isEmpty_linearEquiv`
- Truth anchor: `D5/S3/FiniteGroups/FiniteCharacterAlgebra.finrank_ofShrink`
- Truth anchor: `D5/S3/FiniteGroups/FiniteCharacterAlgebra.finrank_pos`
- Truth anchor: `D5/S3/FiniteGroups/FiniteCharacterAlgebra.homCongrRight`
- Truth anchor: `D5/S3/FiniteGroups/FiniteCharacterAlgebra.isIrreducible_comp_surjective_iff`
- Truth anchor: `D5/S3/FiniteGroups/FiniteCharacterAlgebra.isIrreducible_of_finrank_eq_one`
- Truth anchor: `D5/S3/FiniteGroups/FiniteCharacterAlgebra.isIrreducible_of_simple`
- Truth anchor: `D5/S3/FiniteGroups/FiniteCharacterAlgebra.isIrreducible_toRepresentation_of_isAtom`
- Truth anchor: `D5/S3/FiniteGroups/FiniteCharacterAlgebra.isSimpleModule_asSubmodule_iff`
- Truth anchor: `D5/S3/FiniteGroups/FiniteCharacterAlgebra.mem_iff`
- Truth anchor: `D5/S3/FiniteGroups/FiniteCharacterAlgebra.moduleFiniteForgetObject`
- Truth anchor: `D5/S3/FiniteGroups/FiniteCharacterAlgebra.nontrivial`
- Truth anchor: `D5/S3/FiniteGroups/FiniteCharacterAlgebra.ofCharacter`
- Truth anchor: `D5/S3/FiniteGroups/FiniteCharacterAlgebra.ofCharacter_apply`
- Truth anchor: `D5/S3/FiniteGroups/FiniteCharacterAlgebra.ofShrink`
- Truth anchor: `D5/S3/FiniteGroups/FiniteCharacterAlgebra.ofShrinkEquiv`
- Truth anchor: `D5/S3/FiniteGroups/FiniteCharacterAlgebra.of_ρ_eq_self`
- Truth anchor: `D5/S3/FiniteGroups/FiniteCharacterAlgebra.simple_of_isIrreducible`
- Truth anchor: `D5/S3/FiniteGroups/FiniteCharacterAlgebra.sum_eq_sum_conjClasses`
- Truth anchor: `D5/S3/FiniteGroups/FiniteCharacterAlgebra.toConjClasses`
- Truth anchor: `D5/S3/FiniteGroups/FiniteCharacterAlgebra.toConjClasses_mk`
- Truth anchor: `D5/S3/FiniteGroups/FiniteCharacterAlgebra.toSubmodule_bot`
- Truth anchor: `D5/S3/FiniteGroups/FiniteCharacterAlgebra.toSubmodule_top`
