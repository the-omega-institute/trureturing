# Clifford Constituents

## Abstract

Finite representation theory relates simple modules, characters, conjugation and induction.

**Theorem 1.1 (Mem conj smul).**

$$\forall G \in Type*,\; [\operatorname{Group}\left(G\right)], \forall s \in G,\; \forall H \in \operatorname{Subgroup}\left(G\right),\; \forall x \in G,\; (\operatorname{Membership}.\operatorname{mem}\left(\operatorname{HSMul}.\operatorname{hSMul}\left(\operatorname{DFunLike}.\operatorname{coe}\left(\operatorname{MulAut}.\operatorname{conj}, s\right), H\right), x\right)) \Leftrightarrow (\operatorname{Membership}.\operatorname{mem}\left(H, \operatorname{HMul}.\operatorname{hMul}\left(\operatorname{HMul}.\operatorname{hMul}\left(\operatorname{Inv}.\operatorname{inv}\left(s\right), x\right), s\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/CliffordConstituents.mem_conj_smul` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors; Claude (2026). *TauCeti finite representation and character theory*. URL: <https://github.com/TauCetiProject/TauCeti/tree/a780c7ad6beb23f60a17351a492d177878020ad5>.

*Commentary.*

The displayed conclusion holds under the stated hypotheses.

**Theorem 1.2 (Conj mul smul).**

$$\forall G \in Type*,\; [\operatorname{Group}\left(G\right)], \forall s \in G,\; \forall t \in G,\; \forall H \in \operatorname{Subgroup}\left(G\right),\; (\operatorname{HSMul}.\operatorname{hSMul}\left(\operatorname{DFunLike}.\operatorname{coe}\left(\operatorname{MulAut}.\operatorname{conj}, \operatorname{HMul}.\operatorname{hMul}\left(s, t\right)\right), H\right)) = (\operatorname{HSMul}.\operatorname{hSMul}\left(\operatorname{DFunLike}.\operatorname{coe}\left(\operatorname{MulAut}.\operatorname{conj}, s\right), \operatorname{HSMul}.\operatorname{hSMul}\left(\operatorname{DFunLike}.\operatorname{coe}\left(\operatorname{MulAut}.\operatorname{conj}, t\right), H\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/CliffordConstituents.conj_mul_smul` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors; Claude (2026). *TauCeti finite representation and character theory*. URL: <https://github.com/TauCetiProject/TauCeti/tree/a780c7ad6beb23f60a17351a492d177878020ad5>.

*Commentary.*

The displayed conclusion holds under the stated hypotheses.

**Theorem 1.3 (Coe conj subgroup equiv apply).**

$$\forall G \in Type*,\; [\operatorname{Group}\left(G\right)], \forall s \in G,\; \forall H \in \operatorname{Subgroup}\left(G\right),\; \forall x \in \operatorname{Subtype}\left(\lambda (x: G) \mapsto (\operatorname{Membership}.\operatorname{mem}\left(\operatorname{HSMul}.\operatorname{hSMul}\left(\operatorname{DFunLike}.\operatorname{coe}\left(\operatorname{MulAut}.\operatorname{conj}, s\right), H\right), x\right))\right),\; (\operatorname{Subtype}.\operatorname{val}\left(\operatorname{DFunLike}.\operatorname{coe}\left(\operatorname{MulEquiv}.\operatorname{symm}\left(\operatorname{Subgroup}.\operatorname{equivSMul}\left(\operatorname{DFunLike}.\operatorname{coe}\left(\operatorname{MulAut}.\operatorname{conj}, s\right), H\right)\right), x\right)\right)) = (\operatorname{HMul}.\operatorname{hMul}\left(\operatorname{HMul}.\operatorname{hMul}\left(\operatorname{Inv}.\operatorname{inv}\left(s\right), \operatorname{Subtype}.\operatorname{val}\left(x\right)\right), s\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/CliffordConstituents.coe_conjSubgroupEquiv_apply` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors; Claude (2026). *TauCeti finite representation and character theory*. URL: <https://github.com/TauCetiProject/TauCeti/tree/a780c7ad6beb23f60a17351a492d177878020ad5>.

*Commentary.*

The displayed conclusion holds under the stated hypotheses.

**Definition 1.4 (Conj normal fdr ep functor).**

$$\forall k \in Type*,\; \forall G \in Type*,\; [\operatorname{Group}\left(G\right)], \forall N \in \operatorname{Subgroup}\left(G\right),\; [\operatorname{Subgroup}.\operatorname{Normal}\left(N\right)], [\operatorname{Ring}\left(k\right)], \forall g \in G,\; \operatorname{D5}.\operatorname{S3}.\operatorname{FiniteGroups}.\operatorname{CliffordConstituents}.\operatorname{TauCeti}.\operatorname{conjNormalFDRepFunctor}\left(g\right) = (\operatorname{Action}.\operatorname{res}\left(\operatorname{FGModuleCat}\left(k\right), \operatorname{MulEquiv}.\operatorname{toMonoidHom}\left(\operatorname{DFunLike}.\operatorname{coe}\left(\operatorname{MulAut}.\operatorname{conjNormal}, \operatorname{Inv}.\operatorname{inv}\left(g\right)\right)\right)\right))$$

*Formalization.* `D5/S3/FiniteGroups/CliffordConstituents.conjNormalFDRepFunctor` (`✓ std3`).

*Citation.* The Tau Ceti contributors; Claude (2026). *TauCeti finite representation and character theory*. URL: <https://github.com/TauCetiProject/TauCeti/tree/a780c7ad6beb23f60a17351a492d177878020ad5>.

*Commentary.*

The formula defines the displayed algebraic construction.

**Definition 1.5 (Conj normal fdr ep equiv).**

$$\forall k \in Type*,\; \forall G \in Type*,\; [\operatorname{Group}\left(G\right)], \forall N \in \operatorname{Subgroup}\left(G\right),\; [\operatorname{Subgroup}.\operatorname{Normal}\left(N\right)], [\operatorname{Ring}\left(k\right)], \forall g \in G,\; \operatorname{D5}.\operatorname{S3}.\operatorname{FiniteGroups}.\operatorname{CliffordConstituents}.\operatorname{TauCeti}.\operatorname{conjNormalFDRepEquiv}\left(g\right) = (\operatorname{Action}.\operatorname{resEquiv}\left(\operatorname{FGModuleCat}\left(k\right), \operatorname{DFunLike}.\operatorname{coe}\left(\operatorname{MulAut}.\operatorname{conjNormal}, \operatorname{Inv}.\operatorname{inv}\left(g\right)\right)\right))$$

*Formalization.* `D5/S3/FiniteGroups/CliffordConstituents.conjNormalFDRepEquiv` (`✓ std3`).

*Citation.* The Tau Ceti contributors; Claude (2026). *TauCeti finite representation and character theory*. URL: <https://github.com/TauCetiProject/TauCeti/tree/a780c7ad6beb23f60a17351a492d177878020ad5>.

*Commentary.*

The formula defines the displayed algebraic construction.

**Theorem 1.6 (Conj normal fdr ep equiv functor).**

$$\forall k \in Type*,\; \forall G \in Type*,\; [\operatorname{Group}\left(G\right)], \forall N \in \operatorname{Subgroup}\left(G\right),\; [\operatorname{Subgroup}.\operatorname{Normal}\left(N\right)], [\operatorname{Ring}\left(k\right)], \forall g \in G,\; (\operatorname{CategoryTheory}.\operatorname{Equivalence}.\operatorname{functor}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{FiniteGroups}.\operatorname{CliffordConstituents}.\operatorname{TauCeti}.\operatorname{conjNormalFDRepEquiv}\left(g\right)\right)) = (\operatorname{D5}.\operatorname{S3}.\operatorname{FiniteGroups}.\operatorname{CliffordConstituents}.\operatorname{TauCeti}.\operatorname{conjNormalFDRepFunctor}\left(g\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/CliffordConstituents.conjNormalFDRepEquiv_functor` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors; Claude (2026). *TauCeti finite representation and character theory*. URL: <https://github.com/TauCetiProject/TauCeti/tree/a780c7ad6beb23f60a17351a492d177878020ad5>.

*Commentary.*

The displayed conclusion holds under the stated hypotheses.

**Definition 1.7 (Conj normal fdr ep skeleton sm ul).**

$$\forall k \in Type*,\; \forall G \in Type*,\; [\operatorname{Group}\left(G\right)], \forall N \in \operatorname{Subgroup}\left(G\right),\; [\operatorname{Subgroup}.\operatorname{Normal}\left(N\right)], [\operatorname{Ring}\left(k\right)], \operatorname{D5}.\operatorname{S3}.\operatorname{FiniteGroups}.\operatorname{CliffordConstituents}.\operatorname{TauCeti}.\operatorname{conjNormalFDRepSkeletonSMul} = (\operatorname{SMul}.\operatorname{mk}\left(\lambda (g: G) \mapsto (\operatorname{CategoryTheory}.\operatorname{Functor}.\operatorname{obj}\left(\operatorname{CategoryTheory}.\operatorname{Functor}.\operatorname{mapSkeleton}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{FiniteGroups}.\operatorname{CliffordConstituents}.\operatorname{TauCeti}.\operatorname{conjNormalFDRepFunctor}\left(g\right)\right)\right))\right))$$

*Formalization.* `D5/S3/FiniteGroups/CliffordConstituents.conjNormalFDRepSkeletonSMul` (`✓ std3`).

*Citation.* The Tau Ceti contributors; Claude (2026). *TauCeti finite representation and character theory*. URL: <https://github.com/TauCetiProject/TauCeti/tree/a780c7ad6beb23f60a17351a492d177878020ad5>.

*Commentary.*

The formula defines the displayed algebraic construction.

**Theorem 1.8 (Smul to skeleton).**

$$\forall k \in Type*,\; \forall G \in Type*,\; [\operatorname{Group}\left(G\right)], \forall N \in \operatorname{Subgroup}\left(G\right),\; [\operatorname{Subgroup}.\operatorname{Normal}\left(N\right)], [\operatorname{Ring}\left(k\right)], \forall g \in G,\; \forall A \in \operatorname{FDRep}\left(k, \operatorname{Subtype}\left(\lambda (x: G) \mapsto (\operatorname{Membership}.\operatorname{mem}\left(N, x\right))\right)\right),\; (\operatorname{HSMul}.\operatorname{hSMul}\left(g, \operatorname{CategoryTheory}.\operatorname{toSkeleton}\left(A\right)\right)) = (\operatorname{CategoryTheory}.\operatorname{toSkeleton}\left(\operatorname{CategoryTheory}.\operatorname{Functor}.\operatorname{obj}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{FiniteGroups}.\operatorname{CliffordConstituents}.\operatorname{TauCeti}.\operatorname{conjNormalFDRepFunctor}\left(g\right), A\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/CliffordConstituents.smul_toSkeleton` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors; Claude (2026). *TauCeti finite representation and character theory*. URL: <https://github.com/TauCetiProject/TauCeti/tree/a780c7ad6beb23f60a17351a492d177878020ad5>.

*Commentary.*

The displayed conclusion holds under the stated hypotheses.

**Definition 1.9 (Conj normal fdr ep skeleton mul action).**

$$\forall k \in Type*,\; \forall G \in Type*,\; [\operatorname{Group}\left(G\right)], \forall N \in \operatorname{Subgroup}\left(G\right),\; [\operatorname{Subgroup}.\operatorname{Normal}\left(N\right)], [\operatorname{Ring}\left(k\right)], \operatorname{D5}.\operatorname{S3}.\operatorname{FiniteGroups}.\operatorname{CliffordConstituents}.\operatorname{TauCeti}.\operatorname{conjNormalFDRepSkeletonMulAction} = (\operatorname{MulAction}.\operatorname{mk}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{FiniteGroups}.\operatorname{CliffordConstituents}.\operatorname{TauCeti}.\operatorname{conjNormalFDRepSkeletonSMul}\right))$$

*Formalization.* `D5/S3/FiniteGroups/CliffordConstituents.conjNormalFDRepSkeletonMulAction` (`✓ std3`).

*Citation.* The Tau Ceti contributors; Claude (2026). *TauCeti finite representation and character theory*. URL: <https://github.com/TauCetiProject/TauCeti/tree/a780c7ad6beb23f60a17351a492d177878020ad5>.

*Commentary.*

The formula defines the displayed algebraic construction.

**Theorem 1.10 (Char conj normal fdr ep).**

$$\forall k \in Type*,\; \forall G \in Type*,\; [\operatorname{Group}\left(G\right)], \forall N \in \operatorname{Subgroup}\left(G\right),\; [\operatorname{Subgroup}.\operatorname{Normal}\left(N\right)], [\operatorname{Field}\left(k\right)], \forall g \in G,\; \forall A \in \operatorname{FDRep}\left(k, \operatorname{Subtype}\left(\lambda (x: G) \mapsto (\operatorname{Membership}.\operatorname{mem}\left(N, x\right))\right)\right),\; \forall x \in \operatorname{Subtype}\left(\lambda (x: G) \mapsto (\operatorname{Membership}.\operatorname{mem}\left(N, x\right))\right),\; (\operatorname{FDRep}.\operatorname{character}\left(\operatorname{CategoryTheory}.\operatorname{Functor}.\operatorname{obj}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{FiniteGroups}.\operatorname{CliffordConstituents}.\operatorname{TauCeti}.\operatorname{conjNormalFDRepFunctor}\left(g\right), A\right), x\right)) = (\operatorname{FDRep}.\operatorname{character}\left(A, \operatorname{DFunLike}.\operatorname{coe}\left(\operatorname{DFunLike}.\operatorname{coe}\left(\operatorname{MulAut}.\operatorname{conjNormal}, \operatorname{Inv}.\operatorname{inv}\left(g\right)\right), x\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/CliffordConstituents.char_conjNormalFDRep` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors; Claude (2026). *TauCeti finite representation and character theory*. URL: <https://github.com/TauCetiProject/TauCeti/tree/a780c7ad6beb23f60a17351a492d177878020ad5>.

*Commentary.*

The displayed conclusion holds under the stated hypotheses.

**Definition 1.11 (Conj subrep).**

$$\forall k \in Type*,\; \forall G \in Type*,\; \forall V \in Type*,\; [\operatorname{Semiring}\left(k\right)], [\operatorname{Group}\left(G\right)], [\operatorname{AddCommMonoid}\left(V\right)], [\operatorname{Module}\left(k, V\right)], \forall N \in \operatorname{Subgroup}\left(G\right),\; [\operatorname{Subgroup}.\operatorname{Normal}\left(N\right)], \forall rho \in \operatorname{Representation}\left(k, G, V\right),\; \forall g \in G,\; \forall sigma \in \operatorname{Subrepresentation}\left(\operatorname{MonoidHom}.\operatorname{comp}\left(rho, \operatorname{Subgroup}.\operatorname{subtype}\left(N\right)\right)\right),\; \operatorname{D5}.\operatorname{S3}.\operatorname{FiniteGroups}.\operatorname{CliffordConstituents}.\operatorname{TauCeti}.\operatorname{Representation}.\operatorname{conjSubrep}\left(rho, g, sigma\right) = (\operatorname{Subrepresentation}.\operatorname{mk}\left(\operatorname{Submodule}.\operatorname{map}\left(\operatorname{DFunLike}.\operatorname{coe}\left(rho, g\right), \operatorname{Subrepresentation}.\operatorname{toSubmodule}\left(sigma\right)\right)\right))$$

*Formalization.* `D5/S3/FiniteGroups/CliffordConstituents.conjSubrep` (`✓ std3`).

*Citation.* The Tau Ceti contributors; Claude (2026). *TauCeti finite representation and character theory*. URL: <https://github.com/TauCetiProject/TauCeti/tree/a780c7ad6beb23f60a17351a492d177878020ad5>.

*Commentary.*

The formula defines the displayed algebraic construction.

**Theorem 1.12 (Is atom conj subrep iff).**

$$\forall k \in Type*,\; \forall G \in Type*,\; \forall V \in Type*,\; [\operatorname{Semiring}\left(k\right)], [\operatorname{Group}\left(G\right)], [\operatorname{AddCommMonoid}\left(V\right)], [\operatorname{Module}\left(k, V\right)], \forall N \in \operatorname{Subgroup}\left(G\right),\; [\operatorname{Subgroup}.\operatorname{Normal}\left(N\right)], \forall rho \in \operatorname{Representation}\left(k, G, V\right),\; \forall g \in G,\; \forall sigma \in \operatorname{Subrepresentation}\left(\operatorname{MonoidHom}.\operatorname{comp}\left(rho, \operatorname{Subgroup}.\operatorname{subtype}\left(N\right)\right)\right),\; (\operatorname{IsAtom}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{FiniteGroups}.\operatorname{CliffordConstituents}.\operatorname{TauCeti}.\operatorname{Representation}.\operatorname{conjSubrep}\left(rho, g, sigma\right)\right)) \Leftrightarrow (\operatorname{IsAtom}\left(sigma\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/CliffordConstituents.isAtom_conjSubrep_iff` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors; Claude (2026). *TauCeti finite representation and character theory*. URL: <https://github.com/TauCetiProject/TauCeti/tree/a780c7ad6beb23f60a17351a492d177878020ad5>.

*Commentary.*

The displayed conclusion holds under the stated hypotheses.

**Definition 1.13 (Conj subrep equiv).**

$$\forall k \in Type*,\; \forall G \in Type*,\; \forall V \in Type*,\; [\operatorname{Semiring}\left(k\right)], [\operatorname{Group}\left(G\right)], [\operatorname{AddCommMonoid}\left(V\right)], [\operatorname{Module}\left(k, V\right)], \forall N \in \operatorname{Subgroup}\left(G\right),\; [\operatorname{Subgroup}.\operatorname{Normal}\left(N\right)], \forall rho \in \operatorname{Representation}\left(k, G, V\right),\; \forall g \in G,\; \forall sigma \in \operatorname{Subrepresentation}\left(\operatorname{MonoidHom}.\operatorname{comp}\left(rho, \operatorname{Subgroup}.\operatorname{subtype}\left(N\right)\right)\right),\; \operatorname{D5}.\operatorname{S3}.\operatorname{FiniteGroups}.\operatorname{CliffordConstituents}.\operatorname{TauCeti}.\operatorname{Representation}.\operatorname{conjSubrepEquiv}\left(rho, g, sigma\right) = (\operatorname{Representation}.\operatorname{Equiv}.\operatorname{mk}\left(\operatorname{Submodule}.\operatorname{equivMapOfInjective}\left(\operatorname{DFunLike}.\operatorname{coe}\left(rho, g\right), \operatorname{Subrepresentation}.\operatorname{toSubmodule}\left(sigma\right)\right)\right))$$

*Formalization.* `D5/S3/FiniteGroups/CliffordConstituents.conjSubrepEquiv` (`✓ std3`).

*Citation.* The Tau Ceti contributors; Claude (2026). *TauCeti finite representation and character theory*. URL: <https://github.com/TauCetiProject/TauCeti/tree/a780c7ad6beb23f60a17351a492d177878020ad5>.

*Commentary.*

The formula defines the displayed algebraic construction.

**Theorem 1.14 (Is semisimple representation comp subtype).**

$$\forall k \in Type*,\; \forall G \in Type*,\; \forall V \in Type*,\; [\operatorname{Field}\left(k\right)], [\operatorname{Group}\left(G\right)], [\operatorname{AddCommGroup}\left(V\right)], [\operatorname{Module}\left(k, V\right)], \forall N \in \operatorname{Subgroup}\left(G\right),\; [\operatorname{Subgroup}.\operatorname{Normal}\left(N\right)], \forall rho \in \operatorname{Representation}\left(k, G, V\right),\; [\operatorname{Representation}.\operatorname{IsIrreducible}\left(rho\right)], [\operatorname{FiniteDimensional}\left(k, V\right)], \operatorname{Representation}.\operatorname{IsSemisimpleRepresentation}\left(\operatorname{MonoidHom}.\operatorname{comp}\left(rho, \operatorname{Subgroup}.\operatorname{subtype}\left(N\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/CliffordConstituents.isSemisimpleRepresentation_comp_subtype` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors; Claude (2026). *TauCeti finite representation and character theory*. URL: <https://github.com/TauCetiProject/TauCeti/tree/a780c7ad6beb23f60a17351a492d177878020ad5>.

*Commentary.*

The displayed conclusion holds under the stated hypotheses.

**Theorem 1.15 (Exists nonempty linear equiv as submodule conj subrep).**

$$\forall k \in Type*,\; \forall G \in Type*,\; \forall V \in Type*,\; [\operatorname{Field}\left(k\right)], [\operatorname{Group}\left(G\right)], [\operatorname{AddCommGroup}\left(V\right)], [\operatorname{Module}\left(k, V\right)], \forall N \in \operatorname{Subgroup}\left(G\right),\; [\operatorname{Subgroup}.\operatorname{Normal}\left(N\right)], \forall rho \in \operatorname{Representation}\left(k, G, V\right),\; [\operatorname{Representation}.\operatorname{IsIrreducible}\left(rho\right)], \forall sigma \in \operatorname{Subrepresentation}\left(\operatorname{MonoidHom}.\operatorname{comp}\left(rho, \operatorname{Subgroup}.\operatorname{subtype}\left(N\right)\right)\right),\; (\operatorname{IsAtom}\left(sigma\right)) \Rightarrow (\forall T \in \operatorname{Submodule}\left(\operatorname{MonoidAlgebra}\left(k, \operatorname{Subtype}\left(\lambda (x: G) \mapsto (\operatorname{Membership}.\operatorname{mem}\left(N, x\right))\right)\right), \operatorname{Representation}.\operatorname{asModule}\left(\operatorname{MonoidHom}.\operatorname{comp}\left(rho, \operatorname{Subgroup}.\operatorname{subtype}\left(N\right)\right)\right)\right),\; [\operatorname{IsSimpleModule}\left(\operatorname{MonoidAlgebra}\left(k, \operatorname{Subtype}\left(\lambda (x: G) \mapsto (\operatorname{Membership}.\operatorname{mem}\left(N, x\right))\right)\right), \operatorname{Subtype}\left(\lambda (x: \operatorname{Representation}.\operatorname{asModule}\left(\operatorname{MonoidHom}.\operatorname{comp}\left(rho, \operatorname{Subgroup}.\operatorname{subtype}\left(N\right)\right)\right)) \mapsto (\operatorname{Membership}.\operatorname{mem}\left(T, x\right))\right)\right)], \exists g \in G,\; \operatorname{Nonempty}\left(\operatorname{LinearEquiv}\left(\operatorname{RingHom}.\operatorname{id}\left(\operatorname{MonoidAlgebra}\left(k, \operatorname{Subtype}\left(\lambda (x: G) \mapsto (\operatorname{Membership}.\operatorname{mem}\left(N, x\right))\right)\right)\right), \operatorname{Subtype}\left(\lambda (x: \operatorname{Representation}.\operatorname{asModule}\left(\operatorname{MonoidHom}.\operatorname{comp}\left(rho, \operatorname{Subgroup}.\operatorname{subtype}\left(N\right)\right)\right)) \mapsto (\operatorname{Membership}.\operatorname{mem}\left(T, x\right))\right), \operatorname{Subtype}\left(\lambda (x: \operatorname{Representation}.\operatorname{asModule}\left(\operatorname{MonoidHom}.\operatorname{comp}\left(rho, \operatorname{Subgroup}.\operatorname{subtype}\left(N\right)\right)\right)) \mapsto (\operatorname{Membership}.\operatorname{mem}\left(\operatorname{Subrepresentation}.\operatorname{asSubmodule}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{FiniteGroups}.\operatorname{CliffordConstituents}.\operatorname{TauCeti}.\operatorname{Representation}.\operatorname{conjSubrep}\left(rho, g, sigma\right)\right), x\right))\right)\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/CliffordConstituents.exists_nonempty_linearEquiv_asSubmodule_conjSubrep` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors; Claude (2026). *TauCeti finite representation and character theory*. URL: <https://github.com/TauCetiProject/TauCeti/tree/a780c7ad6beb23f60a17351a492d177878020ad5>.

*Commentary.*

The displayed conclusion holds under the stated hypotheses.

**Theorem 1.16 (Exists is atom forall nonempty linear equiv conj subrep).**

$$\forall k \in Type*,\; \forall G \in Type*,\; \forall V \in Type*,\; [\operatorname{Field}\left(k\right)], [\operatorname{Group}\left(G\right)], [\operatorname{AddCommGroup}\left(V\right)], [\operatorname{Module}\left(k, V\right)], \forall N \in \operatorname{Subgroup}\left(G\right),\; [\operatorname{Subgroup}.\operatorname{Normal}\left(N\right)], \forall rho \in \operatorname{Representation}\left(k, G, V\right),\; [\operatorname{Representation}.\operatorname{IsIrreducible}\left(rho\right)], [\operatorname{FiniteDimensional}\left(k, V\right)], \exists sigma \in \operatorname{Subrepresentation}\left(\operatorname{MonoidHom}.\operatorname{comp}\left(rho, \operatorname{Subgroup}.\operatorname{subtype}\left(N\right)\right)\right),\; (\operatorname{IsAtom}\left(sigma\right)) \land (\forall tau \in \operatorname{Subrepresentation}\left(\operatorname{MonoidHom}.\operatorname{comp}\left(rho, \operatorname{Subgroup}.\operatorname{subtype}\left(N\right)\right)\right),\; (\operatorname{IsAtom}\left(tau\right)) \Rightarrow (\exists g \in G,\; \operatorname{Nonempty}\left(\operatorname{LinearEquiv}\left(\operatorname{RingHom}.\operatorname{id}\left(\operatorname{MonoidAlgebra}\left(k, \operatorname{Subtype}\left(\lambda (x: G) \mapsto (\operatorname{Membership}.\operatorname{mem}\left(N, x\right))\right)\right)\right), \operatorname{Subtype}\left(\lambda (x: \operatorname{Representation}.\operatorname{asModule}\left(\operatorname{MonoidHom}.\operatorname{comp}\left(rho, \operatorname{Subgroup}.\operatorname{subtype}\left(N\right)\right)\right)) \mapsto (\operatorname{Membership}.\operatorname{mem}\left(\operatorname{Subrepresentation}.\operatorname{asSubmodule}\left(tau\right), x\right))\right), \operatorname{Subtype}\left(\lambda (x: \operatorname{Representation}.\operatorname{asModule}\left(\operatorname{MonoidHom}.\operatorname{comp}\left(rho, \operatorname{Subgroup}.\operatorname{subtype}\left(N\right)\right)\right)) \mapsto (\operatorname{Membership}.\operatorname{mem}\left(\operatorname{Subrepresentation}.\operatorname{asSubmodule}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{FiniteGroups}.\operatorname{CliffordConstituents}.\operatorname{TauCeti}.\operatorname{Representation}.\operatorname{conjSubrep}\left(rho, g, sigma\right)\right), x\right))\right)\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/CliffordConstituents.exists_isAtom_forall_nonempty_linearEquiv_conjSubrep` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors; Claude (2026). *TauCeti finite representation and character theory*. URL: <https://github.com/TauCetiProject/TauCeti/tree/a780c7ad6beb23f60a17351a492d177878020ad5>.

*Commentary.*

The displayed conclusion holds under the stated hypotheses.

**Definition 1.17 (Conj subrep isotypic component).**

$$\forall k \in Type*,\; \forall G \in Type*,\; \forall V \in Type*,\; [\operatorname{Field}\left(k\right)], [\operatorname{Group}\left(G\right)], [\operatorname{AddCommGroup}\left(V\right)], [\operatorname{Module}\left(k, V\right)], \forall N \in \operatorname{Subgroup}\left(G\right),\; [\operatorname{Subgroup}.\operatorname{Normal}\left(N\right)], \forall rho \in \operatorname{Representation}\left(k, G, V\right),\; [\operatorname{Representation}.\operatorname{IsIrreducible}\left(rho\right)], \forall sigma \in \operatorname{Subrepresentation}\left(\operatorname{MonoidHom}.\operatorname{comp}\left(rho, \operatorname{Subgroup}.\operatorname{subtype}\left(N\right)\right)\right),\; \forall hsigma \in \operatorname{IsAtom}\left(sigma\right),\; \forall g \in G,\; \operatorname{D5}.\operatorname{S3}.\operatorname{FiniteGroups}.\operatorname{CliffordConstituents}.\operatorname{Representation}.\operatorname{conjSubrepIsotypicComponent}\left(rho, sigma, hsigma, g\right) = (\operatorname{Subtype}.\operatorname{mk}\left(\operatorname{isotypicComponent}\left(\operatorname{MonoidAlgebra}\left(k, \operatorname{Subtype}\left(\lambda (x: G) \mapsto (\operatorname{Membership}.\operatorname{mem}\left(N, x\right))\right)\right), \operatorname{Representation}.\operatorname{asModule}\left(\operatorname{MonoidHom}.\operatorname{comp}\left(rho, \operatorname{Subgroup}.\operatorname{subtype}\left(N\right)\right)\right), \operatorname{Subtype}\left(\lambda (x: \operatorname{Representation}.\operatorname{asModule}\left(\operatorname{MonoidHom}.\operatorname{comp}\left(rho, \operatorname{Subgroup}.\operatorname{subtype}\left(N\right)\right)\right)) \mapsto (\operatorname{Membership}.\operatorname{mem}\left(\operatorname{Subrepresentation}.\operatorname{asSubmodule}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{FiniteGroups}.\operatorname{CliffordConstituents}.\operatorname{TauCeti}.\operatorname{Representation}.\operatorname{conjSubrep}\left(rho, g, sigma\right)\right), x\right))\right)\right)\right))$$

*Formalization.* `D5/S3/FiniteGroups/CliffordConstituents.conjSubrepIsotypicComponent` (`✓ std3`).

*Citation.* The Tau Ceti contributors; Claude (2026). *TauCeti finite representation and character theory*. URL: <https://github.com/TauCetiProject/TauCeti/tree/a780c7ad6beb23f60a17351a492d177878020ad5>.

*Commentary.*

The formula defines the displayed algebraic construction.

**Theorem 1.18 (Coe conj subrep isotypic component).**

$$\forall k \in Type*,\; \forall G \in Type*,\; \forall V \in Type*,\; [\operatorname{Field}\left(k\right)], [\operatorname{Group}\left(G\right)], [\operatorname{AddCommGroup}\left(V\right)], [\operatorname{Module}\left(k, V\right)], \forall N \in \operatorname{Subgroup}\left(G\right),\; [\operatorname{Subgroup}.\operatorname{Normal}\left(N\right)], \forall rho \in \operatorname{Representation}\left(k, G, V\right),\; [\operatorname{Representation}.\operatorname{IsIrreducible}\left(rho\right)], \forall sigma \in \operatorname{Subrepresentation}\left(\operatorname{MonoidHom}.\operatorname{comp}\left(rho, \operatorname{Subgroup}.\operatorname{subtype}\left(N\right)\right)\right),\; (\operatorname{IsAtom}\left(sigma\right)) \Rightarrow (\forall g \in G,\; (\operatorname{Subtype}.\operatorname{val}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{FiniteGroups}.\operatorname{CliffordConstituents}.\operatorname{Representation}.\operatorname{conjSubrepIsotypicComponent}\left(rho, sigma, g\right)\right)) = (\operatorname{isotypicComponent}\left(\operatorname{MonoidAlgebra}\left(k, \operatorname{Subtype}\left(\lambda (x: G) \mapsto (\operatorname{Membership}.\operatorname{mem}\left(N, x\right))\right)\right), \operatorname{Representation}.\operatorname{asModule}\left(\operatorname{MonoidHom}.\operatorname{comp}\left(rho, \operatorname{Subgroup}.\operatorname{subtype}\left(N\right)\right)\right), \operatorname{Subtype}\left(\lambda (x: \operatorname{Representation}.\operatorname{asModule}\left(\operatorname{MonoidHom}.\operatorname{comp}\left(rho, \operatorname{Subgroup}.\operatorname{subtype}\left(N\right)\right)\right)) \mapsto (\operatorname{Membership}.\operatorname{mem}\left(\operatorname{Subrepresentation}.\operatorname{asSubmodule}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{FiniteGroups}.\operatorname{CliffordConstituents}.\operatorname{TauCeti}.\operatorname{Representation}.\operatorname{conjSubrep}\left(rho, g, sigma\right)\right), x\right))\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/CliffordConstituents.coe_conjSubrepIsotypicComponent` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors; Claude (2026). *TauCeti finite representation and character theory*. URL: <https://github.com/TauCetiProject/TauCeti/tree/a780c7ad6beb23f60a17351a492d177878020ad5>.

*Commentary.*

The displayed conclusion holds under the stated hypotheses.

**Definition 1.19 (Simple submodule classes).**

$$\forall R \in Type*,\; [\operatorname{Ring}\left(R\right)], \forall M \in Type*,\; [\operatorname{AddCommGroup}\left(M\right)], [\operatorname{Module}\left(R, M\right)], \operatorname{D5}.\operatorname{S3}.\operatorname{FiniteGroups}.\operatorname{CliffordConstituents}.\operatorname{TauCeti}.\operatorname{SimpleSubmoduleClasses}\left(R, M\right) = (\operatorname{Quot}\left(\lambda (N: \operatorname{Subtype}\left(\lambda (N: \operatorname{Submodule}\left(R, M\right)) \mapsto (\operatorname{IsSimpleModule}\left(R, \operatorname{Subtype}\left(\lambda (x: M) \mapsto (\operatorname{Membership}.\operatorname{mem}\left(N, x\right))\right)\right))\right)) \mapsto (\lambda (NPrime: \operatorname{Subtype}\left(\lambda (N: \operatorname{Submodule}\left(R, M\right)) \mapsto (\operatorname{IsSimpleModule}\left(R, \operatorname{Subtype}\left(\lambda (x: M) \mapsto (\operatorname{Membership}.\operatorname{mem}\left(N, x\right))\right)\right))\right)) \mapsto (\operatorname{Nonempty}\left(\operatorname{LinearEquiv}\left(\operatorname{RingHom}.\operatorname{id}\left(R\right), \operatorname{Subtype}\left(\lambda (x: M) \mapsto (\operatorname{Membership}.\operatorname{mem}\left(\operatorname{Subtype}.\operatorname{val}\left(N\right), x\right))\right), \operatorname{Subtype}\left(\lambda (x: M) \mapsto (\operatorname{Membership}.\operatorname{mem}\left(\operatorname{Subtype}.\operatorname{val}\left(NPrime\right), x\right))\right)\right)\right)))\right))$$

*Formalization.* `D5/S3/FiniteGroups/CliffordConstituents.SimpleSubmoduleClasses` (`✓ std3`).

*Citation.* The Tau Ceti contributors; Claude (2026). *TauCeti finite representation and character theory*. URL: <https://github.com/TauCetiProject/TauCeti/tree/a780c7ad6beb23f60a17351a492d177878020ad5>.

*Commentary.*

The formula defines the displayed algebraic construction.

**Definition 1.20 (Mk).**

$$\forall R \in Type*,\; [\operatorname{Ring}\left(R\right)], \forall M \in Type*,\; [\operatorname{AddCommGroup}\left(M\right)], [\operatorname{Module}\left(R, M\right)], \forall N \in \operatorname{Submodule}\left(R, M\right),\; [\operatorname{IsSimpleModule}\left(R, \operatorname{Subtype}\left(\lambda (x: M) \mapsto (\operatorname{Membership}.\operatorname{mem}\left(N, x\right))\right)\right)], \operatorname{D5}.\operatorname{S3}.\operatorname{FiniteGroups}.\operatorname{CliffordConstituents}.\operatorname{TauCeti}.\operatorname{SimpleSubmoduleClasses}.\operatorname{mk}\left(N\right) = (\operatorname{Quot}.\operatorname{mk}\left(\lambda (N: \operatorname{Subtype}\left(\lambda (N: \operatorname{Submodule}\left(R, M\right)) \mapsto (\operatorname{IsSimpleModule}\left(R, \operatorname{Subtype}\left(\lambda (x: M) \mapsto (\operatorname{Membership}.\operatorname{mem}\left(N, x\right))\right)\right))\right)) \mapsto (\lambda (NPrime: \operatorname{Subtype}\left(\lambda (N: \operatorname{Submodule}\left(R, M\right)) \mapsto (\operatorname{IsSimpleModule}\left(R, \operatorname{Subtype}\left(\lambda (x: M) \mapsto (\operatorname{Membership}.\operatorname{mem}\left(N, x\right))\right)\right))\right)) \mapsto (\operatorname{Nonempty}\left(\operatorname{LinearEquiv}\left(\operatorname{RingHom}.\operatorname{id}\left(R\right), \operatorname{Subtype}\left(\lambda (x: M) \mapsto (\operatorname{Membership}.\operatorname{mem}\left(\operatorname{Subtype}.\operatorname{val}\left(N\right), x\right))\right), \operatorname{Subtype}\left(\lambda (x: M) \mapsto (\operatorname{Membership}.\operatorname{mem}\left(\operatorname{Subtype}.\operatorname{val}\left(NPrime\right), x\right))\right)\right)\right))), \operatorname{Subtype}.\operatorname{mk}\left(N\right)\right))$$

*Formalization.* `D5/S3/FiniteGroups/CliffordConstituents.mk` (`✓ std3`).

*Citation.* The Tau Ceti contributors; Claude (2026). *TauCeti finite representation and character theory*. URL: <https://github.com/TauCetiProject/TauCeti/tree/a780c7ad6beb23f60a17351a492d177878020ad5>.

*Commentary.*

The formula defines the displayed algebraic construction.

**Theorem 1.21 (Mk eq mk iff).**

$$\forall R \in Type*,\; [\operatorname{Ring}\left(R\right)], \forall M \in Type*,\; [\operatorname{AddCommGroup}\left(M\right)], [\operatorname{Module}\left(R, M\right)], \forall N \in \operatorname{Submodule}\left(R, M\right),\; \forall NPrime \in \operatorname{Submodule}\left(R, M\right),\; [\operatorname{IsSimpleModule}\left(R, \operatorname{Subtype}\left(\lambda (x: M) \mapsto (\operatorname{Membership}.\operatorname{mem}\left(N, x\right))\right)\right)], [\operatorname{IsSimpleModule}\left(R, \operatorname{Subtype}\left(\lambda (x: M) \mapsto (\operatorname{Membership}.\operatorname{mem}\left(NPrime, x\right))\right)\right)], ((\operatorname{D5}.\operatorname{S3}.\operatorname{FiniteGroups}.\operatorname{CliffordConstituents}.\operatorname{TauCeti}.\operatorname{SimpleSubmoduleClasses}.\operatorname{mk}\left(N\right)) = (\operatorname{D5}.\operatorname{S3}.\operatorname{FiniteGroups}.\operatorname{CliffordConstituents}.\operatorname{TauCeti}.\operatorname{SimpleSubmoduleClasses}.\operatorname{mk}\left(NPrime\right))) \Leftrightarrow (\operatorname{Nonempty}\left(\operatorname{LinearEquiv}\left(\operatorname{RingHom}.\operatorname{id}\left(R\right), \operatorname{Subtype}\left(\lambda (x: M) \mapsto (\operatorname{Membership}.\operatorname{mem}\left(N, x\right))\right), \operatorname{Subtype}\left(\lambda (x: M) \mapsto (\operatorname{Membership}.\operatorname{mem}\left(NPrime, x\right))\right)\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/CliffordConstituents.mk_eq_mk_iff` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors; Claude (2026). *TauCeti finite representation and character theory*. URL: <https://github.com/TauCetiProject/TauCeti/tree/a780c7ad6beb23f60a17351a492d177878020ad5>.

*Commentary.*

The displayed conclusion holds under the stated hypotheses.

**Theorem 1.22 (Ind).**

$$\forall R \in Type*,\; [\operatorname{Ring}\left(R\right)], \forall M \in Type*,\; [\operatorname{AddCommGroup}\left(M\right)], [\operatorname{Module}\left(R, M\right)], \forall motive \in (\operatorname{D5}.\operatorname{S3}.\operatorname{FiniteGroups}.\operatorname{CliffordConstituents}.\operatorname{TauCeti}.\operatorname{SimpleSubmoduleClasses}\left(R, M\right)) \to (Prop),\; (\forall N \in \operatorname{Submodule}\left(R, M\right),\; (\operatorname{IsSimpleModule}\left(R, \operatorname{Subtype}\left(\lambda (x: M) \mapsto (\operatorname{Membership}.\operatorname{mem}\left(N, x\right))\right)\right)) \Rightarrow (motive\left(\operatorname{D5}.\operatorname{S3}.\operatorname{FiniteGroups}.\operatorname{CliffordConstituents}.\operatorname{TauCeti}.\operatorname{SimpleSubmoduleClasses}.\operatorname{mk}\left(N\right)\right))) \Rightarrow (\forall c \in \operatorname{D5}.\operatorname{S3}.\operatorname{FiniteGroups}.\operatorname{CliffordConstituents}.\operatorname{TauCeti}.\operatorname{SimpleSubmoduleClasses}\left(R, M\right),\; motive\left(c\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/CliffordConstituents.ind` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors; Claude (2026). *TauCeti finite representation and character theory*. URL: <https://github.com/TauCetiProject/TauCeti/tree/a780c7ad6beb23f60a17351a492d177878020ad5>.

*Commentary.*

The displayed conclusion holds under the stated hypotheses.

**Definition 1.23 (Lift).**

$$\forall R \in Type*,\; [\operatorname{Ring}\left(R\right)], \forall M \in Type*,\; [\operatorname{AddCommGroup}\left(M\right)], [\operatorname{Module}\left(R, M\right)], \forall alpha \in Sort*,\; \forall f \in \left(\forall N \in \operatorname{Submodule}\left(R, M\right),\; [\operatorname{IsSimpleModule}\left(R, \operatorname{Subtype}\left(\lambda (x: M) \mapsto (\operatorname{Membership}.\operatorname{mem}\left(N, x\right))\right)\right)], alpha\right),\; \forall hf \in \left(\forall N \in \operatorname{Submodule}\left(R, M\right),\; \forall NPrime \in \operatorname{Submodule}\left(R, M\right),\; [\operatorname{IsSimpleModule}\left(R, \operatorname{Subtype}\left(\lambda (x: M) \mapsto (\operatorname{Membership}.\operatorname{mem}\left(N, x\right))\right)\right)], [\operatorname{IsSimpleModule}\left(R, \operatorname{Subtype}\left(\lambda (x: M) \mapsto (\operatorname{Membership}.\operatorname{mem}\left(NPrime, x\right))\right)\right)], (\operatorname{Nonempty}\left(\operatorname{LinearEquiv}\left(\operatorname{RingHom}.\operatorname{id}\left(R\right), \operatorname{Subtype}\left(\lambda (x: M) \mapsto (\operatorname{Membership}.\operatorname{mem}\left(N, x\right))\right), \operatorname{Subtype}\left(\lambda (x: M) \mapsto (\operatorname{Membership}.\operatorname{mem}\left(NPrime, x\right))\right)\right)\right)) \Rightarrow ((f\left(N\right)) = (f\left(NPrime\right)))\right),\; \forall c \in \operatorname{D5}.\operatorname{S3}.\operatorname{FiniteGroups}.\operatorname{CliffordConstituents}.\operatorname{TauCeti}.\operatorname{SimpleSubmoduleClasses}\left(R, M\right),\; \operatorname{D5}.\operatorname{S3}.\operatorname{FiniteGroups}.\operatorname{CliffordConstituents}.\operatorname{TauCeti}.\operatorname{SimpleSubmoduleClasses}.\operatorname{lift}\left(f, hf, c\right) = (\operatorname{Quot}.\operatorname{lift}\left(\lambda (N: \operatorname{Subtype}\left(\lambda (N: \operatorname{Submodule}\left(R, M\right)) \mapsto (\operatorname{IsSimpleModule}\left(R, \operatorname{Subtype}\left(\lambda (x: M) \mapsto (\operatorname{Membership}.\operatorname{mem}\left(N, x\right))\right)\right))\right)) \mapsto (f\left(\operatorname{Subtype}.\operatorname{val}\left(N\right)\right)), c\right))$$

*Formalization.* `D5/S3/FiniteGroups/CliffordConstituents.lift` (`✓ std3`).

*Citation.* The Tau Ceti contributors; Claude (2026). *TauCeti finite representation and character theory*. URL: <https://github.com/TauCetiProject/TauCeti/tree/a780c7ad6beb23f60a17351a492d177878020ad5>.

*Commentary.*

The formula defines the displayed algebraic construction.

**Theorem 1.24 (Lift mk).**

$$\forall R \in Type*,\; [\operatorname{Ring}\left(R\right)], \forall M \in Type*,\; [\operatorname{AddCommGroup}\left(M\right)], [\operatorname{Module}\left(R, M\right)], \forall alpha \in Sort*,\; \forall f \in \left(\forall N \in \operatorname{Submodule}\left(R, M\right),\; [\operatorname{IsSimpleModule}\left(R, \operatorname{Subtype}\left(\lambda (x: M) \mapsto (\operatorname{Membership}.\operatorname{mem}\left(N, x\right))\right)\right)], alpha\right),\; (\forall N \in \operatorname{Submodule}\left(R, M\right),\; \forall NPrime \in \operatorname{Submodule}\left(R, M\right),\; [\operatorname{IsSimpleModule}\left(R, \operatorname{Subtype}\left(\lambda (x: M) \mapsto (\operatorname{Membership}.\operatorname{mem}\left(N, x\right))\right)\right)], [\operatorname{IsSimpleModule}\left(R, \operatorname{Subtype}\left(\lambda (x: M) \mapsto (\operatorname{Membership}.\operatorname{mem}\left(NPrime, x\right))\right)\right)], (\operatorname{Nonempty}\left(\operatorname{LinearEquiv}\left(\operatorname{RingHom}.\operatorname{id}\left(R\right), \operatorname{Subtype}\left(\lambda (x: M) \mapsto (\operatorname{Membership}.\operatorname{mem}\left(N, x\right))\right), \operatorname{Subtype}\left(\lambda (x: M) \mapsto (\operatorname{Membership}.\operatorname{mem}\left(NPrime, x\right))\right)\right)\right)) \Rightarrow ((f\left(N\right)) = (f\left(NPrime\right)))) \Rightarrow (\forall N \in \operatorname{Submodule}\left(R, M\right),\; [\operatorname{IsSimpleModule}\left(R, \operatorname{Subtype}\left(\lambda (x: M) \mapsto (\operatorname{Membership}.\operatorname{mem}\left(N, x\right))\right)\right)], (\operatorname{D5}.\operatorname{S3}.\operatorname{FiniteGroups}.\operatorname{CliffordConstituents}.\operatorname{TauCeti}.\operatorname{SimpleSubmoduleClasses}.\operatorname{lift}\left(f, \operatorname{D5}.\operatorname{S3}.\operatorname{FiniteGroups}.\operatorname{CliffordConstituents}.\operatorname{TauCeti}.\operatorname{SimpleSubmoduleClasses}.\operatorname{mk}\left(N\right)\right)) = (f\left(N\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/CliffordConstituents.lift_mk` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors; Claude (2026). *TauCeti finite representation and character theory*. URL: <https://github.com/TauCetiProject/TauCeti/tree/a780c7ad6beb23f60a17351a492d177878020ad5>.

*Commentary.*

The displayed conclusion holds under the stated hypotheses.

**Definition 1.25 (Simple submodule classes equiv).**

$$\forall R \in Type*,\; [\operatorname{Ring}\left(R\right)], \forall M \in Type*,\; [\operatorname{AddCommGroup}\left(M\right)], [\operatorname{Module}\left(R, M\right)], \operatorname{D5}.\operatorname{S3}.\operatorname{FiniteGroups}.\operatorname{CliffordConstituents}.\operatorname{TauCeti}.\operatorname{simpleSubmoduleClassesEquiv}\left(R, M\right) = (\operatorname{Equiv}.\operatorname{ofBijective}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{FiniteGroups}.\operatorname{CliffordConstituents}.\operatorname{TauCeti}.\operatorname{SimpleSubmoduleClasses}.\operatorname{lift}\left(\lambda (N: \operatorname{Submodule}\left(R, M\right)) \mapsto (\operatorname{Function}.\operatorname{const}\left(\operatorname{IsSimpleModule}\left(R, \operatorname{Subtype}\left(\lambda (x: M) \mapsto (\operatorname{Membership}.\operatorname{mem}\left(N, x\right))\right)\right), \operatorname{Subtype}.\operatorname{mk}\left(\operatorname{isotypicComponent}\left(R, M, \operatorname{Subtype}\left(\lambda (x: M) \mapsto (\operatorname{Membership}.\operatorname{mem}\left(N, x\right))\right)\right)\right)\right))\right)\right))$$

*Formalization.* `D5/S3/FiniteGroups/CliffordConstituents.simpleSubmoduleClassesEquiv` (`✓ std3`).

*Citation.* The Tau Ceti contributors; Claude (2026). *TauCeti finite representation and character theory*. URL: <https://github.com/TauCetiProject/TauCeti/tree/a780c7ad6beb23f60a17351a492d177878020ad5>.

*Commentary.*

The formula defines the displayed algebraic construction.

**Theorem 1.26 (Nonempty linear equiv isotypic component).**

$$\forall k \in Type*,\; \forall A \in Type*,\; \forall M \in Type*,\; \forall S \in Type*,\; [\operatorname{Field}\left(k\right)], [\operatorname{Ring}\left(A\right)], [\operatorname{Algebra}\left(k, A\right)], [\operatorname{AddCommGroup}\left(M\right)], [\operatorname{Module}\left(k, M\right)], [\operatorname{Module}\left(A, M\right)], [\operatorname{IsScalarTower}\left(k, A, M\right)], [\operatorname{AddCommGroup}\left(S\right)], [\operatorname{Module}\left(k, S\right)], [\operatorname{Module}\left(A, S\right)], [\operatorname{IsScalarTower}\left(k, A, S\right)], [\operatorname{IsSimpleModule}\left(A, S\right)], [\operatorname{IsAlgClosed}\left(k\right)], [\operatorname{FiniteDimensional}\left(k, S\right)], [\operatorname{FiniteDimensional}\left(k, M\right)], \operatorname{Nonempty}\left(\operatorname{LinearEquiv}\left(\operatorname{RingHom}.\operatorname{id}\left(A\right), \operatorname{Subtype}\left(\lambda (x: M) \mapsto (\operatorname{Membership}.\operatorname{mem}\left(\operatorname{isotypicComponent}\left(A, M, S\right), x\right))\right), (\operatorname{Fin}\left(\operatorname{Module}.\operatorname{finrank}\left(k, \operatorname{LinearMap}\left(\operatorname{RingHom}.\operatorname{id}\left(A\right), S, M\right)\right)\right)) \to (S)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/CliffordConstituents.nonempty_linearEquiv_isotypicComponent` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors; Claude (2026). *TauCeti finite representation and character theory*. URL: <https://github.com/TauCetiProject/TauCeti/tree/a780c7ad6beb23f60a17351a492d177878020ad5>.

*Commentary.*

The displayed conclusion holds under the stated hypotheses.

**Theorem 1.27 (Exists forall finrank linear map eq).**

$$\forall k \in Type*,\; \forall G \in Type*,\; \forall V \in Type*,\; [\operatorname{Field}\left(k\right)], [\operatorname{Group}\left(G\right)], [\operatorname{AddCommGroup}\left(V\right)], [\operatorname{Module}\left(k, V\right)], \forall N \in \operatorname{Subgroup}\left(G\right),\; [\operatorname{Subgroup}.\operatorname{Normal}\left(N\right)], \forall rho \in \operatorname{Representation}\left(k, G, V\right),\; [\operatorname{Representation}.\operatorname{IsIrreducible}\left(rho\right)], [\operatorname{FiniteDimensional}\left(k, V\right)], \exists e \in \operatorname{Nat},\; (\operatorname{LT}.\operatorname{lt}\left(0, e\right)) \land (\forall sigma \in \operatorname{Subrepresentation}\left(\operatorname{MonoidHom}.\operatorname{comp}\left(rho, \operatorname{Subgroup}.\operatorname{subtype}\left(N\right)\right)\right),\; (\operatorname{IsAtom}\left(sigma\right)) \Rightarrow ((\operatorname{Module}.\operatorname{finrank}\left(k, \operatorname{LinearMap}\left(\operatorname{RingHom}.\operatorname{id}\left(\operatorname{MonoidAlgebra}\left(k, \operatorname{Subtype}\left(\lambda (x: G) \mapsto (\operatorname{Membership}.\operatorname{mem}\left(N, x\right))\right)\right)\right), \operatorname{Subtype}\left(\lambda (x: \operatorname{Representation}.\operatorname{asModule}\left(\operatorname{MonoidHom}.\operatorname{comp}\left(rho, \operatorname{Subgroup}.\operatorname{subtype}\left(N\right)\right)\right)) \mapsto (\operatorname{Membership}.\operatorname{mem}\left(\operatorname{Subrepresentation}.\operatorname{asSubmodule}\left(sigma\right), x\right))\right), \operatorname{Representation}.\operatorname{asModule}\left(\operatorname{MonoidHom}.\operatorname{comp}\left(rho, \operatorname{Subgroup}.\operatorname{subtype}\left(N\right)\right)\right)\right)\right)) = (e)))$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/CliffordConstituents.exists_forall_finrank_linearMap_eq` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors; Claude (2026). *TauCeti finite representation and character theory*. URL: <https://github.com/TauCetiProject/TauCeti/tree/a780c7ad6beb23f60a17351a492d177878020ad5>.

*Commentary.*

The displayed conclusion holds under the stated hypotheses.

**Definition 1.28 (Equiv of as module linear equiv).**

$$\forall k \in Type*,\; \forall G \in Type*,\; \forall V \in Type*,\; \forall W \in Type*,\; [\operatorname{CommSemiring}\left(k\right)], [\operatorname{Monoid}\left(G\right)], [\operatorname{AddCommMonoid}\left(V\right)], [\operatorname{Module}\left(k, V\right)], [\operatorname{AddCommMonoid}\left(W\right)], [\operatorname{Module}\left(k, W\right)], \forall rho \in \operatorname{Representation}\left(k, G, V\right),\; \forall sigma \in \operatorname{Representation}\left(k, G, W\right),\; \forall f \in \operatorname{LinearEquiv}\left(\operatorname{RingHom}.\operatorname{id}\left(\operatorname{MonoidAlgebra}\left(k, G\right)\right), \operatorname{Representation}.\operatorname{asModule}\left(rho\right), \operatorname{Representation}.\operatorname{asModule}\left(sigma\right)\right),\; \operatorname{D5}.\operatorname{S3}.\operatorname{FiniteGroups}.\operatorname{CliffordConstituents}.\operatorname{TauCeti}.\operatorname{Representation}.\operatorname{equivOfAsModuleLinearEquiv}\left(f\right) = (\operatorname{Representation}.\operatorname{IntertwiningMap}.\operatorname{ofBijective}\left(\operatorname{DFunLike}.\operatorname{coe}\left(\operatorname{LinearEquiv}.\operatorname{symm}\left(\operatorname{Representation}.\operatorname{IntertwiningMap}.\operatorname{equivLinearMapAsModule}\left(rho, sigma\right)\right), \operatorname{LinearEquiv}.\operatorname{toLinearMap}\left(f\right)\right)\right))$$

*Formalization.* `D5/S3/FiniteGroups/CliffordConstituents.equivOfAsModuleLinearEquiv` (`✓ std3`).

*Citation.* The Tau Ceti contributors; Claude (2026). *TauCeti finite representation and character theory*. URL: <https://github.com/TauCetiProject/TauCeti/tree/a780c7ad6beb23f60a17351a492d177878020ad5>.

*Commentary.*

The formula defines the displayed algebraic construction.

**Definition 1.29 (As module linear equiv of equiv).**

$$\forall k \in Type*,\; \forall G \in Type*,\; \forall V \in Type*,\; \forall W \in Type*,\; [\operatorname{CommSemiring}\left(k\right)], [\operatorname{Monoid}\left(G\right)], [\operatorname{AddCommMonoid}\left(V\right)], [\operatorname{Module}\left(k, V\right)], [\operatorname{AddCommMonoid}\left(W\right)], [\operatorname{Module}\left(k, W\right)], \forall rho \in \operatorname{Representation}\left(k, G, V\right),\; \forall sigma \in \operatorname{Representation}\left(k, G, W\right),\; \forall phi \in \operatorname{Representation}.\operatorname{Equiv}\left(rho, sigma\right),\; \operatorname{D5}.\operatorname{S3}.\operatorname{FiniteGroups}.\operatorname{CliffordConstituents}.\operatorname{TauCeti}.\operatorname{Representation}.\operatorname{asModuleLinearEquivOfEquiv}\left(phi\right) = (\operatorname{LinearEquiv}.\operatorname{ofBijective}\left(\operatorname{DFunLike}.\operatorname{coe}\left(\operatorname{Representation}.\operatorname{IntertwiningMap}.\operatorname{equivLinearMapAsModule}\left(rho, sigma\right), \operatorname{Representation}.\operatorname{Equiv}.\operatorname{toIntertwiningMap}\left(phi\right)\right)\right))$$

*Formalization.* `D5/S3/FiniteGroups/CliffordConstituents.asModuleLinearEquivOfEquiv` (`✓ std3`).

*Citation.* The Tau Ceti contributors; Claude (2026). *TauCeti finite representation and character theory*. URL: <https://github.com/TauCetiProject/TauCeti/tree/a780c7ad6beb23f60a17351a492d177878020ad5>.

*Commentary.*

The formula defines the displayed algebraic construction.

**Definition 1.30 (Fd rep iso of as module linear equiv).**

$$\forall k \in Type*,\; \forall V \in Type*,\; \forall W \in Type*,\; \forall G \in Type*,\; [\operatorname{CommRing}\left(k\right)], [\operatorname{Monoid}\left(G\right)], [\operatorname{AddCommGroup}\left(V\right)], [\operatorname{Module}\left(k, V\right)], [\operatorname{Module}.\operatorname{Finite}\left(k, V\right)], [\operatorname{AddCommGroup}\left(W\right)], [\operatorname{Module}\left(k, W\right)], [\operatorname{Module}.\operatorname{Finite}\left(k, W\right)], \forall rho \in \operatorname{Representation}\left(k, G, V\right),\; \forall sigma \in \operatorname{Representation}\left(k, G, W\right),\; \forall f \in \operatorname{LinearEquiv}\left(\operatorname{RingHom}.\operatorname{id}\left(\operatorname{MonoidAlgebra}\left(k, G\right)\right), \operatorname{Representation}.\operatorname{asModule}\left(rho\right), \operatorname{Representation}.\operatorname{asModule}\left(sigma\right)\right),\; \operatorname{D5}.\operatorname{S3}.\operatorname{FiniteGroups}.\operatorname{CliffordConstituents}.\operatorname{TauCeti}.\operatorname{fdRepIsoOfAsModuleLinearEquiv}\left(f\right) = (\operatorname{CategoryTheory}.\operatorname{Functor}.\operatorname{preimageIso}\left(\operatorname{CategoryTheory}.\operatorname{forget}_{2}\left(\operatorname{FDRep}\left(k, G\right), \operatorname{Rep}\left(k, G\right)\right), \operatorname{Rep}.\operatorname{mkIso}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{FiniteGroups}.\operatorname{CliffordConstituents}.\operatorname{TauCeti}.\operatorname{Representation}.\operatorname{equivOfAsModuleLinearEquiv}\left(f\right)\right)\right))$$

*Formalization.* `D5/S3/FiniteGroups/CliffordConstituents.fdRepIsoOfAsModuleLinearEquiv` (`✓ std3`).

*Citation.* The Tau Ceti contributors; Claude (2026). *TauCeti finite representation and character theory*. URL: <https://github.com/TauCetiProject/TauCeti/tree/a780c7ad6beb23f60a17351a492d177878020ad5>.

*Commentary.*

The formula defines the displayed algebraic construction.

**Theorem 1.31 (Nonempty fd rep iso iff).**

$$\forall k \in Type*,\; \forall G \in Type*,\; [\operatorname{CommRing}\left(k\right)], [\operatorname{Monoid}\left(G\right)], \forall X \in \operatorname{FDRep}\left(k, G\right),\; \forall Y \in \operatorname{FDRep}\left(k, G\right),\; (\operatorname{Nonempty}\left(\operatorname{CategoryTheory}.\operatorname{Iso}\left(X, Y\right)\right)) \Leftrightarrow (\operatorname{Nonempty}\left(\operatorname{Representation}.\operatorname{Equiv}\left(\operatorname{FDRep}.\rho\left(X\right), \operatorname{FDRep}.\rho\left(Y\right)\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/CliffordConstituents.nonempty_fdRepIso_iff` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors; Claude (2026). *TauCeti finite representation and character theory*. URL: <https://github.com/TauCetiProject/TauCeti/tree/a780c7ad6beb23f60a17351a492d177878020ad5>.

*Commentary.*

The displayed conclusion holds under the stated hypotheses.

**Theorem 1.32 (To skeleton fd rep of to representation eq iff).**

$$\forall G \in Type*,\; [\operatorname{Monoid}\left(G\right)], \forall K \in Type*,\; \forall X \in Type*,\; [\operatorname{CommRing}\left(K\right)], [\operatorname{AddCommGroup}\left(X\right)], [\operatorname{Module}\left(K, X\right)], \forall pi \in \operatorname{Representation}\left(K, G, X\right),\; \forall S \in \operatorname{Subrepresentation}\left(pi\right),\; \forall T \in \operatorname{Subrepresentation}\left(pi\right),\; [\operatorname{Module}.\operatorname{Finite}\left(K, \operatorname{Subtype}\left(\lambda (x: X) \mapsto (\operatorname{Membership}.\operatorname{mem}\left(\operatorname{Subrepresentation}.\operatorname{toSubmodule}\left(S\right), x\right))\right)\right)], [\operatorname{Module}.\operatorname{Finite}\left(K, \operatorname{Subtype}\left(\lambda (x: X) \mapsto (\operatorname{Membership}.\operatorname{mem}\left(\operatorname{Subrepresentation}.\operatorname{toSubmodule}\left(T\right), x\right))\right)\right)], ((\operatorname{CategoryTheory}.\operatorname{toSkeleton}\left(\operatorname{FDRep}.\operatorname{of}\left(\operatorname{Subrepresentation}.\operatorname{toRepresentation}\left(S\right)\right)\right)) = (\operatorname{CategoryTheory}.\operatorname{toSkeleton}\left(\operatorname{FDRep}.\operatorname{of}\left(\operatorname{Subrepresentation}.\operatorname{toRepresentation}\left(T\right)\right)\right))) \Leftrightarrow (\operatorname{Nonempty}\left(\operatorname{LinearEquiv}\left(\operatorname{RingHom}.\operatorname{id}\left(\operatorname{MonoidAlgebra}\left(K, G\right)\right), \operatorname{Subtype}\left(\lambda (x: \operatorname{Representation}.\operatorname{asModule}\left(pi\right)) \mapsto (\operatorname{Membership}.\operatorname{mem}\left(\operatorname{Subrepresentation}.\operatorname{asSubmodule}\left(S\right), x\right))\right), \operatorname{Subtype}\left(\lambda (x: \operatorname{Representation}.\operatorname{asModule}\left(pi\right)) \mapsto (\operatorname{Membership}.\operatorname{mem}\left(\operatorname{Subrepresentation}.\operatorname{asSubmodule}\left(T\right), x\right))\right)\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/CliffordConstituents.toSkeleton_fdRepOf_toRepresentation_eq_iff` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors; Claude (2026). *TauCeti finite representation and character theory*. URL: <https://github.com/TauCetiProject/TauCeti/tree/a780c7ad6beb23f60a17351a492d177878020ad5>.

*Commentary.*

The displayed conclusion holds under the stated hypotheses.

**Theorem 1.33 (Mem inertia iff).**

$$\forall k \in Type*,\; \forall G \in Type*,\; [\operatorname{Group}\left(G\right)], \forall N \in \operatorname{Subgroup}\left(G\right),\; [\operatorname{Subgroup}.\operatorname{Normal}\left(N\right)], [\operatorname{Ring}\left(k\right)], \forall A \in \operatorname{FDRep}\left(k, \operatorname{Subtype}\left(\lambda (x: G) \mapsto (\operatorname{Membership}.\operatorname{mem}\left(N, x\right))\right)\right),\; \forall g \in G,\; (\operatorname{Membership}.\operatorname{mem}\left(\operatorname{MulAction}.\operatorname{stabilizer}\left(G, \operatorname{CategoryTheory}.\operatorname{toSkeleton}\left(A\right)\right), g\right)) \Leftrightarrow (\operatorname{Nonempty}\left(\operatorname{CategoryTheory}.\operatorname{Iso}\left(\operatorname{CategoryTheory}.\operatorname{Functor}.\operatorname{obj}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{FiniteGroups}.\operatorname{CliffordConstituents}.\operatorname{TauCeti}.\operatorname{conjNormalFDRepFunctor}\left(g\right), A\right), A\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/CliffordConstituents.mem_inertia_iff` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors; Claude (2026). *TauCeti finite representation and character theory*. URL: <https://github.com/TauCetiProject/TauCeti/tree/a780c7ad6beb23f60a17351a492d177878020ad5>.

*Commentary.*

The displayed conclusion holds under the stated hypotheses.

**Theorem 1.34 (Le inertia).**

$$\forall k \in Type*,\; \forall G \in Type*,\; [\operatorname{Group}\left(G\right)], \forall N \in \operatorname{Subgroup}\left(G\right),\; [\operatorname{Subgroup}.\operatorname{Normal}\left(N\right)], [\operatorname{Ring}\left(k\right)], \forall A \in \operatorname{FDRep}\left(k, \operatorname{Subtype}\left(\lambda (x: G) \mapsto (\operatorname{Membership}.\operatorname{mem}\left(N, x\right))\right)\right),\; \operatorname{LE}.\operatorname{le}\left(N, \operatorname{MulAction}.\operatorname{stabilizer}\left(G, \operatorname{CategoryTheory}.\operatorname{toSkeleton}\left(A\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/CliffordConstituents.le_inertia` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors; Claude (2026). *TauCeti finite representation and character theory*. URL: <https://github.com/TauCetiProject/TauCeti/tree/a780c7ad6beb23f60a17351a492d177878020ad5>.

*Commentary.*

The displayed conclusion holds under the stated hypotheses.

**Theorem 1.35 (Char conj eq of mem inertia).**

$$\forall k \in Type*,\; \forall G \in Type*,\; [\operatorname{Group}\left(G\right)], \forall N \in \operatorname{Subgroup}\left(G\right),\; [\operatorname{Subgroup}.\operatorname{Normal}\left(N\right)], [\operatorname{Field}\left(k\right)], \forall A \in \operatorname{FDRep}\left(k, \operatorname{Subtype}\left(\lambda (x: G) \mapsto (\operatorname{Membership}.\operatorname{mem}\left(N, x\right))\right)\right),\; \forall g \in G,\; (\operatorname{Membership}.\operatorname{mem}\left(\operatorname{MulAction}.\operatorname{stabilizer}\left(G, \operatorname{CategoryTheory}.\operatorname{toSkeleton}\left(A\right)\right), g\right)) \Rightarrow (\forall x \in \operatorname{Subtype}\left(\lambda (x: G) \mapsto (\operatorname{Membership}.\operatorname{mem}\left(N, x\right))\right),\; (\operatorname{FDRep}.\operatorname{character}\left(A, \operatorname{Subtype}.\operatorname{mk}\left(\operatorname{HMul}.\operatorname{hMul}\left(\operatorname{HMul}.\operatorname{hMul}\left(\operatorname{Inv}.\operatorname{inv}\left(g\right), \operatorname{Subtype}.\operatorname{val}\left(x\right)\right), g\right)\right)\right)) = (\operatorname{FDRep}.\operatorname{character}\left(A, x\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/CliffordConstituents.char_conj_eq_of_mem_inertia` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors; Claude (2026). *TauCeti finite representation and character theory*. URL: <https://github.com/TauCetiProject/TauCeti/tree/a780c7ad6beb23f60a17351a492d177878020ad5>.

*Commentary.*

The displayed conclusion holds under the stated hypotheses.

## References

- Truth anchor: `D5/S3/FiniteGroups/CliffordConstituents.SimpleSubmoduleClasses`
- Truth anchor: `D5/S3/FiniteGroups/CliffordConstituents.asModuleLinearEquivOfEquiv`
- Truth anchor: `D5/S3/FiniteGroups/CliffordConstituents.char_conjNormalFDRep`
- Truth anchor: `D5/S3/FiniteGroups/CliffordConstituents.char_conj_eq_of_mem_inertia`
- Truth anchor: `D5/S3/FiniteGroups/CliffordConstituents.coe_conjSubgroupEquiv_apply`
- Truth anchor: `D5/S3/FiniteGroups/CliffordConstituents.coe_conjSubrepIsotypicComponent`
- Truth anchor: `D5/S3/FiniteGroups/CliffordConstituents.conjNormalFDRepEquiv`
- Truth anchor: `D5/S3/FiniteGroups/CliffordConstituents.conjNormalFDRepEquiv_functor`
- Truth anchor: `D5/S3/FiniteGroups/CliffordConstituents.conjNormalFDRepFunctor`
- Truth anchor: `D5/S3/FiniteGroups/CliffordConstituents.conjNormalFDRepSkeletonMulAction`
- Truth anchor: `D5/S3/FiniteGroups/CliffordConstituents.conjNormalFDRepSkeletonSMul`
- Truth anchor: `D5/S3/FiniteGroups/CliffordConstituents.conjSubrep`
- Truth anchor: `D5/S3/FiniteGroups/CliffordConstituents.conjSubrepEquiv`
- Truth anchor: `D5/S3/FiniteGroups/CliffordConstituents.conjSubrepIsotypicComponent`
- Truth anchor: `D5/S3/FiniteGroups/CliffordConstituents.conj_mul_smul`
- Truth anchor: `D5/S3/FiniteGroups/CliffordConstituents.equivOfAsModuleLinearEquiv`
- Truth anchor: `D5/S3/FiniteGroups/CliffordConstituents.exists_forall_finrank_linearMap_eq`
- Truth anchor: `D5/S3/FiniteGroups/CliffordConstituents.exists_isAtom_forall_nonempty_linearEquiv_conjSubrep`
- Truth anchor: `D5/S3/FiniteGroups/CliffordConstituents.exists_nonempty_linearEquiv_asSubmodule_conjSubrep`
- Truth anchor: `D5/S3/FiniteGroups/CliffordConstituents.fdRepIsoOfAsModuleLinearEquiv`
- Truth anchor: `D5/S3/FiniteGroups/CliffordConstituents.ind`
- Truth anchor: `D5/S3/FiniteGroups/CliffordConstituents.isAtom_conjSubrep_iff`
- Truth anchor: `D5/S3/FiniteGroups/CliffordConstituents.isSemisimpleRepresentation_comp_subtype`
- Truth anchor: `D5/S3/FiniteGroups/CliffordConstituents.le_inertia`
- Truth anchor: `D5/S3/FiniteGroups/CliffordConstituents.lift`
- Truth anchor: `D5/S3/FiniteGroups/CliffordConstituents.lift_mk`
- Truth anchor: `D5/S3/FiniteGroups/CliffordConstituents.mem_conj_smul`
- Truth anchor: `D5/S3/FiniteGroups/CliffordConstituents.mem_inertia_iff`
- Truth anchor: `D5/S3/FiniteGroups/CliffordConstituents.mk`
- Truth anchor: `D5/S3/FiniteGroups/CliffordConstituents.mk_eq_mk_iff`
- Truth anchor: `D5/S3/FiniteGroups/CliffordConstituents.nonempty_fdRepIso_iff`
- Truth anchor: `D5/S3/FiniteGroups/CliffordConstituents.nonempty_linearEquiv_isotypicComponent`
- Truth anchor: `D5/S3/FiniteGroups/CliffordConstituents.simpleSubmoduleClassesEquiv`
- Truth anchor: `D5/S3/FiniteGroups/CliffordConstituents.smul_toSkeleton`
- Truth anchor: `D5/S3/FiniteGroups/CliffordConstituents.toSkeleton_fdRepOf_toRepresentation_eq_iff`
- Dependency: [D5/S3/FiniteGroups/FiniteCharacterAlgebra](FiniteCharacterAlgebra.md)
