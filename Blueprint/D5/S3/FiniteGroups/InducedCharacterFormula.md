# Induced Character Formula

## Abstract

Finite representation theory relates simple modules, characters, conjugation and induction.

**Theorem 1.1 (Clifford restrict finrank).**

$$\forall k \in Type*,\; \forall G \in Type*,\; [\operatorname{Field}\left(k\right)], [\operatorname{Group}\left(G\right)], \forall N \in \operatorname{Subgroup}\left(G\right),\; [\operatorname{Subgroup}.\operatorname{Normal}\left(N\right)], [\operatorname{IsAlgClosed}\left(k\right)], \forall W \in \operatorname{FDRep}\left(k, G\right),\; [\operatorname{CategoryTheory}.\operatorname{Simple}\left(W\right)], \exists V \in \operatorname{FDRep}\left(k, \operatorname{Subtype}\left(\lambda (x: G) \mapsto (\operatorname{Membership}.\operatorname{mem}\left(N, x\right))\right)\right),\; \exists [\operatorname{CategoryTheory}.\operatorname{Simple}\left(V\right)], \exists [\operatorname{Finite}\left(\operatorname{HasQuotient}.\operatorname{Quotient}\left(G, \operatorname{MulAction}.\operatorname{stabilizer}\left(G, \operatorname{CategoryTheory}.\operatorname{toSkeleton}\left(V\right)\right)\right)\right)], \exists e \in \operatorname{Nat},\; (\operatorname{Ne}\left(e, 0\right)) \land ((\operatorname{Nonempty}\left(\operatorname{CategoryTheory}.\operatorname{Iso}\left(\operatorname{CategoryTheory}.\operatorname{Functor}.\operatorname{obj}\left(\operatorname{Action}.\operatorname{res}\left(\operatorname{FGModuleCat}\left(k\right), \operatorname{Subgroup}.\operatorname{subtype}\left(N\right)\right), W\right), \operatorname{D5}.\operatorname{S3}.\operatorname{FiniteGroups}.\operatorname{CliffordDecomposition}.\operatorname{FDRep}.\operatorname{cliffordSum}\left(V, e\right)\right)\right)) \land ((\operatorname{Module}.\operatorname{finrank}\left(k, \operatorname{FGModuleCat}.\operatorname{carrier}\left(\operatorname{Action}.\operatorname{V}\left(W\right)\right)\right)) = (\operatorname{HMul}.\operatorname{hMul}\left(\operatorname{HMul}.\operatorname{hMul}\left(e, \operatorname{Subgroup}.\operatorname{index}\left(\operatorname{MulAction}.\operatorname{stabilizer}\left(G, \operatorname{CategoryTheory}.\operatorname{toSkeleton}\left(V\right)\right)\right)\right), \operatorname{Module}.\operatorname{finrank}\left(k, \operatorname{FGModuleCat}.\operatorname{carrier}\left(\operatorname{Action}.\operatorname{V}\left(V\right)\right)\right)\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/InducedCharacterFormula.clifford_restrict_finrank` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors; Claude (2026). *TauCeti finite representation and character theory*. URL: <https://github.com/TauCetiProject/TauCeti/tree/a780c7ad6beb23f60a17351a492d177878020ad5>.

*Commentary.*

The displayed conclusion holds under the stated hypotheses.

**Theorem 1.2 (Char eq finrank iff).**

$$\forall G \in Type*,\; \forall V \in Type*,\; [\operatorname{Monoid}\left(G\right)], [\operatorname{AddCommGroup}\left(V\right)], [\operatorname{Module}\left(\operatorname{Complex}, V\right)], [\operatorname{FiniteDimensional}\left(\operatorname{Complex}, V\right)], \forall rho \in \operatorname{Representation}\left(\operatorname{Complex}, G, V\right),\; \forall g \in G,\; (\operatorname{IsOfFinOrder}\left(g\right)) \Rightarrow (((\operatorname{Representation}.\operatorname{character}\left(rho, g\right)) = (\operatorname{Nat}.\operatorname{cast}\left(\operatorname{Module}.\operatorname{finrank}\left(\operatorname{Complex}, V\right)\right))) \Leftrightarrow ((\operatorname{DFunLike}.\operatorname{coe}\left(rho, g\right)) = (1)))$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/InducedCharacterFormula.char_eq_finrank_iff` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors; Claude (2026). *TauCeti finite representation and character theory*. URL: <https://github.com/TauCetiProject/TauCeti/tree/a780c7ad6beb23f60a17351a492d177878020ad5>.

*Commentary.*

The displayed conclusion holds under the stated hypotheses.

**Theorem 1.3 (Stabilizer quotient group mk).**

$$\forall G \in Type*,\; [\operatorname{Group}\left(G\right)], \forall H \in \operatorname{Subgroup}\left(G\right),\; \forall s \in G,\; (\operatorname{MulAction}.\operatorname{stabilizer}\left(G, \operatorname{QuotientGroup}.\operatorname{mk}\left(s\right)\right)) = (\operatorname{HSMul}.\operatorname{hSMul}\left(\operatorname{DFunLike}.\operatorname{coe}\left(\operatorname{MulAut}.\operatorname{conj}, s\right), H\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/InducedCharacterFormula.stabilizer_quotientGroup_mk` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors; Claude (2026). *TauCeti finite representation and character theory*. URL: <https://github.com/TauCetiProject/TauCeti/tree/a780c7ad6beb23f60a17351a492d177878020ad5>.

*Commentary.*

The displayed conclusion holds under the stated hypotheses.

**Theorem 1.4 (Double coset mk eq mk one iff mem).**

$$\forall G \in Type*,\; [\operatorname{Group}\left(G\right)], \forall H \in \operatorname{Subgroup}\left(G\right),\; \forall s \in G,\; ((\operatorname{DoubleCoset}.\operatorname{mk}\left(H, H, s\right)) = (\operatorname{DoubleCoset}.\operatorname{mk}\left(H, H, 1\right))) \Leftrightarrow (\operatorname{Membership}.\operatorname{mem}\left(H, s\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/InducedCharacterFormula.doubleCosetMk_eq_mk_one_iff_mem` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors; Claude (2026). *TauCeti finite representation and character theory*. URL: <https://github.com/TauCetiProject/TauCeti/tree/a780c7ad6beb23f60a17351a492d177878020ad5>.

*Commentary.*

The displayed conclusion holds under the stated hypotheses.

**Definition 1.5 (Ind term).**

$$\forall k \in Type*,\; \forall G \in Type*,\; [\operatorname{Group}\left(G\right)], \forall S \in \operatorname{Subgroup}\left(G\right),\; [\operatorname{AddCommMonoid}\left(k\right)], \forall f \in (\operatorname{Subtype}\left(\lambda (x: G) \mapsto (\operatorname{Membership}.\operatorname{mem}\left(S, x\right))\right)) \to (k),\; \forall g \in G,\; \forall x \in G,\; \operatorname{D5}.\operatorname{S3}.\operatorname{FiniteGroups}.\operatorname{InducedCharacterFormula}.\operatorname{TauCeti}.\operatorname{indTerm}\left(f, g, x\right) = (\operatorname{dite}\left(\operatorname{Membership}.\operatorname{mem}\left(S, \operatorname{HMul}.\operatorname{hMul}\left(\operatorname{HMul}.\operatorname{hMul}\left(\operatorname{Inv}.\operatorname{inv}\left(x\right), g\right), x\right)\right), \operatorname{Function}.\operatorname{const}\left(\operatorname{Membership}.\operatorname{mem}\left(S, \operatorname{HMul}.\operatorname{hMul}\left(\operatorname{HMul}.\operatorname{hMul}\left(\operatorname{Inv}.\operatorname{inv}\left(x\right), g\right), x\right)\right), f\left(\operatorname{Subtype}.\operatorname{mk}\left(\operatorname{HMul}.\operatorname{hMul}\left(\operatorname{HMul}.\operatorname{hMul}\left(\operatorname{Inv}.\operatorname{inv}\left(x\right), g\right), x\right)\right)\right)\right), \operatorname{Function}.\operatorname{const}\left(\neg (\operatorname{Membership}.\operatorname{mem}\left(S, \operatorname{HMul}.\operatorname{hMul}\left(\operatorname{HMul}.\operatorname{hMul}\left(\operatorname{Inv}.\operatorname{inv}\left(x\right), g\right), x\right)\right)), 0\right)\right))$$

*Formalization.* `D5/S3/FiniteGroups/InducedCharacterFormula.indTerm` (`✓ std3`).

*Citation.* The Tau Ceti contributors; Claude (2026). *TauCeti finite representation and character theory*. URL: <https://github.com/TauCetiProject/TauCeti/tree/a780c7ad6beb23f60a17351a492d177878020ad5>.

*Commentary.*

The formula defines the displayed algebraic construction.

**Theorem 1.6 (Ind term apply).**

$$\forall k \in Type*,\; \forall G \in Type*,\; [\operatorname{Group}\left(G\right)], \forall S \in \operatorname{Subgroup}\left(G\right),\; [\operatorname{AddCommMonoid}\left(k\right)], \forall f \in (\operatorname{Subtype}\left(\lambda (x: G) \mapsto (\operatorname{Membership}.\operatorname{mem}\left(S, x\right))\right)) \to (k),\; \forall g \in G,\; \forall x \in G,\; (\operatorname{D5}.\operatorname{S3}.\operatorname{FiniteGroups}.\operatorname{InducedCharacterFormula}.\operatorname{TauCeti}.\operatorname{indTerm}\left(f, g, x\right)) = (\operatorname{dite}\left(\operatorname{Membership}.\operatorname{mem}\left(S, \operatorname{HMul}.\operatorname{hMul}\left(\operatorname{HMul}.\operatorname{hMul}\left(\operatorname{Inv}.\operatorname{inv}\left(x\right), g\right), x\right)\right), \operatorname{Function}.\operatorname{const}\left(\operatorname{Membership}.\operatorname{mem}\left(S, \operatorname{HMul}.\operatorname{hMul}\left(\operatorname{HMul}.\operatorname{hMul}\left(\operatorname{Inv}.\operatorname{inv}\left(x\right), g\right), x\right)\right), f\left(\operatorname{Subtype}.\operatorname{mk}\left(\operatorname{HMul}.\operatorname{hMul}\left(\operatorname{HMul}.\operatorname{hMul}\left(\operatorname{Inv}.\operatorname{inv}\left(x\right), g\right), x\right)\right)\right)\right), \operatorname{Function}.\operatorname{const}\left(\neg (\operatorname{Membership}.\operatorname{mem}\left(S, \operatorname{HMul}.\operatorname{hMul}\left(\operatorname{HMul}.\operatorname{hMul}\left(\operatorname{Inv}.\operatorname{inv}\left(x\right), g\right), x\right)\right)), 0\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/InducedCharacterFormula.indTerm_apply` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors; Claude (2026). *TauCeti finite representation and character theory*. URL: <https://github.com/TauCetiProject/TauCeti/tree/a780c7ad6beb23f60a17351a492d177878020ad5>.

*Commentary.*

The displayed conclusion holds under the stated hypotheses.

**Definition 1.7 (Ind class fun).**

$$\forall k \in Type*,\; \forall G \in Type*,\; [\operatorname{Group}\left(G\right)], [\operatorname{AddCommMonoid}\left(k\right)], \forall S \in \operatorname{Subgroup}\left(G\right),\; [\operatorname{Subgroup}.\operatorname{FiniteIndex}\left(S\right)], \forall f \in (\operatorname{Subtype}\left(\lambda (x: G) \mapsto (\operatorname{Membership}.\operatorname{mem}\left(S, x\right))\right)) \to (k),\; \forall g \in G,\; \operatorname{D5}.\operatorname{S3}.\operatorname{FiniteGroups}.\operatorname{InducedCharacterFormula}.\operatorname{TauCeti}.\operatorname{indClassFun}\left(S, f, g\right) = (\operatorname{Finset}.\operatorname{sum}\left(\operatorname{Finset}.\operatorname{univ}, \lambda (t: \operatorname{HasQuotient}.\operatorname{Quotient}\left(G, S\right)) \mapsto (\operatorname{D5}.\operatorname{S3}.\operatorname{FiniteGroups}.\operatorname{InducedCharacterFormula}.\operatorname{TauCeti}.\operatorname{indTerm}\left(f, g, \operatorname{Quotient}.\operatorname{out}\left(t\right)\right))\right))$$

*Formalization.* `D5/S3/FiniteGroups/InducedCharacterFormula.indClassFun` (`✓ std3`).

*Citation.* The Tau Ceti contributors; Claude (2026). *TauCeti finite representation and character theory*. URL: <https://github.com/TauCetiProject/TauCeti/tree/a780c7ad6beb23f60a17351a492d177878020ad5>.

*Commentary.*

The formula defines the displayed algebraic construction.

**Theorem 1.8 (Ind class fun apply).**

$$\forall k \in Type*,\; \forall G \in Type*,\; [\operatorname{Group}\left(G\right)], \forall S \in \operatorname{Subgroup}\left(G\right),\; [\operatorname{AddCommMonoid}\left(k\right)], [\operatorname{Subgroup}.\operatorname{FiniteIndex}\left(S\right)], \forall f \in (\operatorname{Subtype}\left(\lambda (x: G) \mapsto (\operatorname{Membership}.\operatorname{mem}\left(S, x\right))\right)) \to (k),\; \forall g \in G,\; (\operatorname{D5}.\operatorname{S3}.\operatorname{FiniteGroups}.\operatorname{InducedCharacterFormula}.\operatorname{TauCeti}.\operatorname{indClassFun}\left(S, f, g\right)) = (\operatorname{Finset}.\operatorname{sum}\left(\operatorname{Finset}.\operatorname{univ}, \lambda (t: \operatorname{HasQuotient}.\operatorname{Quotient}\left(G, S\right)) \mapsto (\operatorname{dite}\left(\operatorname{Membership}.\operatorname{mem}\left(S, \operatorname{HMul}.\operatorname{hMul}\left(\operatorname{HMul}.\operatorname{hMul}\left(\operatorname{Inv}.\operatorname{inv}\left(\operatorname{Quotient}.\operatorname{out}\left(t\right)\right), g\right), \operatorname{Quotient}.\operatorname{out}\left(t\right)\right)\right), \operatorname{Function}.\operatorname{const}\left(\operatorname{Membership}.\operatorname{mem}\left(S, \operatorname{HMul}.\operatorname{hMul}\left(\operatorname{HMul}.\operatorname{hMul}\left(\operatorname{Inv}.\operatorname{inv}\left(\operatorname{Quotient}.\operatorname{out}\left(t\right)\right), g\right), \operatorname{Quotient}.\operatorname{out}\left(t\right)\right)\right), f\left(\operatorname{Subtype}.\operatorname{mk}\left(\operatorname{HMul}.\operatorname{hMul}\left(\operatorname{HMul}.\operatorname{hMul}\left(\operatorname{Inv}.\operatorname{inv}\left(\operatorname{Quotient}.\operatorname{out}\left(t\right)\right), g\right), \operatorname{Quotient}.\operatorname{out}\left(t\right)\right)\right)\right)\right), \operatorname{Function}.\operatorname{const}\left(\neg (\operatorname{Membership}.\operatorname{mem}\left(S, \operatorname{HMul}.\operatorname{hMul}\left(\operatorname{HMul}.\operatorname{hMul}\left(\operatorname{Inv}.\operatorname{inv}\left(\operatorname{Quotient}.\operatorname{out}\left(t\right)\right), g\right), \operatorname{Quotient}.\operatorname{out}\left(t\right)\right)\right)), 0\right)\right))\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/InducedCharacterFormula.indClassFun_apply` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors; Claude (2026). *TauCeti finite representation and character theory*. URL: <https://github.com/TauCetiProject/TauCeti/tree/a780c7ad6beb23f60a17351a492d177878020ad5>.

*Commentary.*

The displayed conclusion holds under the stated hypotheses.

**Theorem 1.9 (Ind term eq of mk eq).**

$$\forall k \in Type*,\; \forall G \in Type*,\; [\operatorname{Group}\left(G\right)], \forall S \in \operatorname{Subgroup}\left(G\right),\; [\operatorname{Semiring}\left(k\right)], \forall f \in (\operatorname{Subtype}\left(\lambda (x: G) \mapsto (\operatorname{Membership}.\operatorname{mem}\left(S, x\right))\right)) \to (k),\; (\operatorname{Membership}.\operatorname{mem}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{FiniteGroups}.\operatorname{FiniteCharacterAlgebra}.\operatorname{TauCeti}.\operatorname{ClassFunction}\left(k, \operatorname{Subtype}\left(\lambda (x: G) \mapsto (\operatorname{Membership}.\operatorname{mem}\left(S, x\right))\right)\right), f\right)) \Rightarrow (\forall g \in G,\; \forall x \in G,\; \forall y \in G,\; ((\operatorname{QuotientGroup}.\operatorname{mk}\left(x\right)) = (\operatorname{QuotientGroup}.\operatorname{mk}\left(y\right))) \Rightarrow ((\operatorname{D5}.\operatorname{S3}.\operatorname{FiniteGroups}.\operatorname{InducedCharacterFormula}.\operatorname{TauCeti}.\operatorname{indTerm}\left(f, g, x\right)) = (\operatorname{D5}.\operatorname{S3}.\operatorname{FiniteGroups}.\operatorname{InducedCharacterFormula}.\operatorname{TauCeti}.\operatorname{indTerm}\left(f, g, y\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/InducedCharacterFormula.indTerm_eq_of_mk_eq` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors; Claude (2026). *TauCeti finite representation and character theory*. URL: <https://github.com/TauCetiProject/TauCeti/tree/a780c7ad6beb23f60a17351a492d177878020ad5>.

*Commentary.*

The displayed conclusion holds under the stated hypotheses.

**Definition 1.10 (Ind).**

$$\forall k \in Type*,\; \forall G \in Type*,\; [\operatorname{Group}\left(G\right)], [\operatorname{Semiring}\left(k\right)], \forall S \in \operatorname{Subgroup}\left(G\right),\; [\operatorname{Subgroup}.\operatorname{FiniteIndex}\left(S\right)], \operatorname{D5}.\operatorname{S3}.\operatorname{FiniteGroups}.\operatorname{InducedCharacterFormula}.\operatorname{TauCeti}.\operatorname{ClassFunction}.\operatorname{ind}\left(S\right) = (\operatorname{LinearMap}.\operatorname{mk}\left(\operatorname{AddHom}.\operatorname{mk}\left(\lambda (f: \operatorname{Subtype}\left(\lambda (x: (\operatorname{Subtype}\left(\lambda (x: G) \mapsto (\operatorname{Membership}.\operatorname{mem}\left(S, x\right))\right)) \to (k)) \mapsto (\operatorname{Membership}.\operatorname{mem}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{FiniteGroups}.\operatorname{FiniteCharacterAlgebra}.\operatorname{TauCeti}.\operatorname{ClassFunction}\left(k, \operatorname{Subtype}\left(\lambda (x: G) \mapsto (\operatorname{Membership}.\operatorname{mem}\left(S, x\right))\right)\right), x\right))\right)) \mapsto (\operatorname{Subtype}.\operatorname{mk}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{FiniteGroups}.\operatorname{InducedCharacterFormula}.\operatorname{TauCeti}.\operatorname{indClassFun}\left(S, \operatorname{Subtype}.\operatorname{val}\left(f\right)\right)\right))\right)\right))$$

*Formalization.* `D5/S3/FiniteGroups/InducedCharacterFormula.ind` (`✓ std3`).

*Citation.* The Tau Ceti contributors; Claude (2026). *TauCeti finite representation and character theory*. URL: <https://github.com/TauCetiProject/TauCeti/tree/a780c7ad6beb23f60a17351a492d177878020ad5>.

*Commentary.*

The formula defines the displayed algebraic construction.

**Theorem 1.11 (Ind apply).**

$$\forall k \in Type*,\; \forall G \in Type*,\; [\operatorname{Group}\left(G\right)], \forall S \in \operatorname{Subgroup}\left(G\right),\; [\operatorname{Semiring}\left(k\right)], [\operatorname{Subgroup}.\operatorname{FiniteIndex}\left(S\right)], \forall f \in \operatorname{Subtype}\left(\lambda (x: (\operatorname{Subtype}\left(\lambda (x: G) \mapsto (\operatorname{Membership}.\operatorname{mem}\left(S, x\right))\right)) \to (k)) \mapsto (\operatorname{Membership}.\operatorname{mem}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{FiniteGroups}.\operatorname{FiniteCharacterAlgebra}.\operatorname{TauCeti}.\operatorname{ClassFunction}\left(k, \operatorname{Subtype}\left(\lambda (x: G) \mapsto (\operatorname{Membership}.\operatorname{mem}\left(S, x\right))\right)\right), x\right))\right),\; \forall g \in G,\; (\operatorname{Subtype}.\operatorname{val}\left(\operatorname{DFunLike}.\operatorname{coe}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{FiniteGroups}.\operatorname{InducedCharacterFormula}.\operatorname{TauCeti}.\operatorname{ClassFunction}.\operatorname{ind}\left(S\right), f\right), g\right)) = (\operatorname{D5}.\operatorname{S3}.\operatorname{FiniteGroups}.\operatorname{InducedCharacterFormula}.\operatorname{TauCeti}.\operatorname{indClassFun}\left(S, \operatorname{Subtype}.\operatorname{val}\left(f\right), g\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/InducedCharacterFormula.ind_apply` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors; Claude (2026). *TauCeti finite representation and character theory*. URL: <https://github.com/TauCetiProject/TauCeti/tree/a780c7ad6beb23f60a17351a492d177878020ad5>.

*Commentary.*

The displayed conclusion holds under the stated hypotheses.

**Definition 1.12 (Ind fdr ep).**

$$\forall k \in Type*,\; \forall G \in Type*,\; [\operatorname{Field}\left(k\right)], [\operatorname{Group}\left(G\right)], \forall S \in \operatorname{Subgroup}\left(G\right),\; [\operatorname{Subgroup}.\operatorname{FiniteIndex}\left(S\right)], \forall A \in \operatorname{FDRep}\left(k, \operatorname{Subtype}\left(\lambda (x: G) \mapsto (\operatorname{Membership}.\operatorname{mem}\left(S, x\right))\right)\right),\; \operatorname{D5}.\operatorname{S3}.\operatorname{FiniteGroups}.\operatorname{InducedCharacterFormula}.\operatorname{TauCeti}.\operatorname{indFDRep}\left(A\right) = (\operatorname{D5}.\operatorname{S3}.\operatorname{FiniteGroups}.\operatorname{FiniteCharacterAlgebra}.\operatorname{FDRep}.\operatorname{ofShrink}\left(\operatorname{Rep}.\rho\left(\operatorname{Rep}.\operatorname{ind}\left(\operatorname{Subgroup}.\operatorname{subtype}\left(S\right), \operatorname{CategoryTheory}.\operatorname{Functor}.\operatorname{obj}\left(\operatorname{CategoryTheory}.\operatorname{forget}_{2}\left(\operatorname{FDRep}\left(k, \operatorname{Subtype}\left(\lambda (x: G) \mapsto (\operatorname{Membership}.\operatorname{mem}\left(S, x\right))\right)\right), \operatorname{Rep}\left(k, \operatorname{Subtype}\left(\lambda (x: G) \mapsto (\operatorname{Membership}.\operatorname{mem}\left(S, x\right))\right)\right)\right), A\right)\right)\right)\right))$$

*Formalization.* `D5/S3/FiniteGroups/InducedCharacterFormula.indFDRep` (`✓ std3`).

*Citation.* The Tau Ceti contributors; Claude (2026). *TauCeti finite representation and character theory*. URL: <https://github.com/TauCetiProject/TauCeti/tree/a780c7ad6beb23f60a17351a492d177878020ad5>.

*Commentary.*

The formula defines the displayed algebraic construction.

**Theorem 1.13 (Finrank ind fdr ep).**

$$\forall k \in Type*,\; \forall G \in Type*,\; [\operatorname{Field}\left(k\right)], [\operatorname{Group}\left(G\right)], \forall S \in \operatorname{Subgroup}\left(G\right),\; [\operatorname{Subgroup}.\operatorname{FiniteIndex}\left(S\right)], \forall A \in \operatorname{FDRep}\left(k, \operatorname{Subtype}\left(\lambda (x: G) \mapsto (\operatorname{Membership}.\operatorname{mem}\left(S, x\right))\right)\right),\; (\operatorname{Module}.\operatorname{finrank}\left(k, \operatorname{FGModuleCat}.\operatorname{carrier}\left(\operatorname{Action}.\operatorname{V}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{FiniteGroups}.\operatorname{InducedCharacterFormula}.\operatorname{TauCeti}.\operatorname{indFDRep}\left(A\right)\right)\right)\right)) = (\operatorname{HMul}.\operatorname{hMul}\left(\operatorname{Subgroup}.\operatorname{index}\left(S\right), \operatorname{Module}.\operatorname{finrank}\left(k, \operatorname{FGModuleCat}.\operatorname{carrier}\left(\operatorname{Action}.\operatorname{V}\left(A\right)\right)\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/InducedCharacterFormula.finrank_indFDRep` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors; Claude (2026). *TauCeti finite representation and character theory*. URL: <https://github.com/TauCetiProject/TauCeti/tree/a780c7ad6beb23f60a17351a492d177878020ad5>.

*Commentary.*

The displayed conclusion holds under the stated hypotheses.

**Theorem 1.14 (Character pairing ind).**

$$\forall k \in Type*,\; \forall G \in Type*,\; [\operatorname{Group}\left(G\right)], \forall S \in \operatorname{Subgroup}\left(G\right),\; [\operatorname{Field}\left(k\right)], [\operatorname{Fintype}\left(G\right)], (\operatorname{IsUnit}\left(\operatorname{Nat}.\operatorname{cast}\left(\operatorname{Nat}.\operatorname{card}\left(G\right)\right)\right)) \Rightarrow (\forall f \in \operatorname{Subtype}\left(\lambda (x: (\operatorname{Subtype}\left(\lambda (x: G) \mapsto (\operatorname{Membership}.\operatorname{mem}\left(S, x\right))\right)) \to (k)) \mapsto (\operatorname{Membership}.\operatorname{mem}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{FiniteGroups}.\operatorname{FiniteCharacterAlgebra}.\operatorname{TauCeti}.\operatorname{ClassFunction}\left(k, \operatorname{Subtype}\left(\lambda (x: G) \mapsto (\operatorname{Membership}.\operatorname{mem}\left(S, x\right))\right)\right), x\right))\right),\; \forall h \in \operatorname{Subtype}\left(\lambda (x: (G) \to (k)) \mapsto (\operatorname{Membership}.\operatorname{mem}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{FiniteGroups}.\operatorname{FiniteCharacterAlgebra}.\operatorname{TauCeti}.\operatorname{ClassFunction}\left(k, G\right), x\right))\right),\; (\operatorname{DFunLike}.\operatorname{coe}\left(\operatorname{DFunLike}.\operatorname{coe}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{FiniteGroups}.\operatorname{FiniteCharacterAlgebra}.\operatorname{TauCeti}.\operatorname{ClassFunction}.\operatorname{characterPairing}, \operatorname{DFunLike}.\operatorname{coe}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{FiniteGroups}.\operatorname{InducedCharacterFormula}.\operatorname{TauCeti}.\operatorname{ClassFunction}.\operatorname{ind}\left(S\right), f\right)\right), h\right)) = (\operatorname{DFunLike}.\operatorname{coe}\left(\operatorname{DFunLike}.\operatorname{coe}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{FiniteGroups}.\operatorname{FiniteCharacterAlgebra}.\operatorname{TauCeti}.\operatorname{ClassFunction}.\operatorname{characterPairing}, f\right), \operatorname{DFunLike}.\operatorname{coe}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{FiniteGroups}.\operatorname{FiniteCharacterAlgebra}.\operatorname{TauCeti}.\operatorname{ClassFunction}.\operatorname{comap}\left(\operatorname{Subgroup}.\operatorname{subtype}\left(S\right)\right), h\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/InducedCharacterFormula.characterPairing_ind` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors; Claude (2026). *TauCeti finite representation and character theory*. URL: <https://github.com/TauCetiProject/TauCeti/tree/a780c7ad6beb23f60a17351a492d177878020ad5>.

*Commentary.*

The displayed conclusion holds under the stated hypotheses.

**Theorem 1.15 (Finite double coset quotient).**

$$\forall G \in Type*,\; [\operatorname{Group}\left(G\right)], \forall H \in \operatorname{Subgroup}\left(G\right),\; \forall K \in \operatorname{Subgroup}\left(G\right),\; [\operatorname{Subgroup}.\operatorname{FiniteIndex}\left(K\right)], \operatorname{Finite}\left(\operatorname{DoubleCoset}.\operatorname{Quotient}\left(\operatorname{SetLike}.\operatorname{coe}\left(H\right), \operatorname{SetLike}.\operatorname{coe}\left(K\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/InducedCharacterFormula.finite_doubleCosetQuotient` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors; Claude (2026). *TauCeti finite representation and character theory*. URL: <https://github.com/TauCetiProject/TauCeti/tree/a780c7ad6beb23f60a17351a492d177878020ad5>.

*Commentary.*

The displayed conclusion holds under the stated hypotheses.

**Theorem 1.16 (Ind of fdr ep).**

$$\forall k \in Type*,\; \forall G \in Type*,\; [\operatorname{Field}\left(k\right)], [\operatorname{Group}\left(G\right)], \forall S \in \operatorname{Subgroup}\left(G\right),\; [\operatorname{Subgroup}.\operatorname{FiniteIndex}\left(S\right)], \forall A \in \operatorname{FDRep}\left(k, \operatorname{Subtype}\left(\lambda (x: G) \mapsto (\operatorname{Membership}.\operatorname{mem}\left(S, x\right))\right)\right),\; (\operatorname{DFunLike}.\operatorname{coe}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{FiniteGroups}.\operatorname{InducedCharacterFormula}.\operatorname{TauCeti}.\operatorname{ClassFunction}.\operatorname{ind}\left(S\right), \operatorname{D5}.\operatorname{S3}.\operatorname{FiniteGroups}.\operatorname{FiniteCharacterAlgebra}.\operatorname{TauCeti}.\operatorname{ClassFunction}.\operatorname{ofCharacter}\left(\operatorname{FDRep}.\rho\left(A\right)\right)\right)) = (\operatorname{D5}.\operatorname{S3}.\operatorname{FiniteGroups}.\operatorname{FiniteCharacterAlgebra}.\operatorname{TauCeti}.\operatorname{ClassFunction}.\operatorname{ofCharacter}\left(\operatorname{FDRep}.\rho\left(\operatorname{D5}.\operatorname{S3}.\operatorname{FiniteGroups}.\operatorname{InducedCharacterFormula}.\operatorname{TauCeti}.\operatorname{indFDRep}\left(A\right)\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/InducedCharacterFormula.ind_ofFDRep` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors; Claude (2026). *TauCeti finite representation and character theory*. URL: <https://github.com/TauCetiProject/TauCeti/tree/a780c7ad6beb23f60a17351a492d177878020ad5>.

*Commentary.*

The displayed conclusion holds under the stated hypotheses.

## References

- Truth anchor: `D5/S3/FiniteGroups/InducedCharacterFormula.char_eq_finrank_iff`
- Truth anchor: `D5/S3/FiniteGroups/InducedCharacterFormula.characterPairing_ind`
- Truth anchor: `D5/S3/FiniteGroups/InducedCharacterFormula.clifford_restrict_finrank`
- Truth anchor: `D5/S3/FiniteGroups/InducedCharacterFormula.doubleCosetMk_eq_mk_one_iff_mem`
- Truth anchor: `D5/S3/FiniteGroups/InducedCharacterFormula.finite_doubleCosetQuotient`
- Truth anchor: `D5/S3/FiniteGroups/InducedCharacterFormula.finrank_indFDRep`
- Truth anchor: `D5/S3/FiniteGroups/InducedCharacterFormula.ind`
- Truth anchor: `D5/S3/FiniteGroups/InducedCharacterFormula.indClassFun`
- Truth anchor: `D5/S3/FiniteGroups/InducedCharacterFormula.indClassFun_apply`
- Truth anchor: `D5/S3/FiniteGroups/InducedCharacterFormula.indFDRep`
- Truth anchor: `D5/S3/FiniteGroups/InducedCharacterFormula.indTerm`
- Truth anchor: `D5/S3/FiniteGroups/InducedCharacterFormula.indTerm_apply`
- Truth anchor: `D5/S3/FiniteGroups/InducedCharacterFormula.indTerm_eq_of_mk_eq`
- Truth anchor: `D5/S3/FiniteGroups/InducedCharacterFormula.ind_apply`
- Truth anchor: `D5/S3/FiniteGroups/InducedCharacterFormula.ind_ofFDRep`
- Truth anchor: `D5/S3/FiniteGroups/InducedCharacterFormula.stabilizer_quotientGroup_mk`
- Dependency: [D5/S3/FiniteGroups/CharacterDegreeDivisibility](CharacterDegreeDivisibility.md)
- Dependency: [D5/S3/FiniteGroups/CliffordConstituents](CliffordConstituents.md)
- Dependency: [D5/S3/FiniteGroups/CliffordDecomposition](CliffordDecomposition.md)
- Dependency: [D5/S3/FiniteGroups/FiniteCharacterAlgebra](FiniteCharacterAlgebra.md)
