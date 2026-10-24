# Clifford Decomposition

## Abstract

Finite representation theory relates simple modules, characters, conjugation and induction.

**Theorem 1.1 (Is unit nat card subgroup).**

$$\forall k \in Type*,\; \forall G \in Type*,\; [\operatorname{Semiring}\left(k\right)], [\operatorname{Group}\left(G\right)], \forall S \in \operatorname{Subgroup}\left(G\right),\; (\operatorname{IsUnit}\left(\operatorname{Nat}.\operatorname{cast}\left(\operatorname{Nat}.\operatorname{card}\left(G\right)\right)\right)) \Rightarrow (\operatorname{IsUnit}\left(\operatorname{Nat}.\operatorname{cast}\left(\operatorname{Nat}.\operatorname{card}\left(\operatorname{Subtype}\left(\lambda (x: G) \mapsto (\operatorname{Membership}.\operatorname{mem}\left(S, x\right))\right)\right)\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/CliffordDecomposition.isUnit_natCard_subgroup` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors; Claude (2026). *TauCeti finite representation and character theory*. URL: <https://github.com/TauCetiProject/TauCeti/tree/a780c7ad6beb23f60a17351a492d177878020ad5>.

*Commentary.*

The displayed conclusion holds under the stated hypotheses.

**Theorem 1.2 (Trace pi of apply eq).**

$$\forall k \in Type*,\; \forall iota \in Type*,\; \forall M \in Type*,\; [\operatorname{CommRing}\left(k\right)], [\operatorname{Fintype}\left(iota\right)], [\operatorname{AddCommGroup}\left(M\right)], [\operatorname{Module}\left(k, M\right)], [\operatorname{Module}.\operatorname{Free}\left(k, M\right)], [\operatorname{Module}.\operatorname{Finite}\left(k, M\right)], \forall T \in \operatorname{LinearMap}\left(\operatorname{RingHom}.\operatorname{id}\left(k\right), (iota) \to (M), (iota) \to (M)\right),\; \forall sigma \in (iota) \to (iota),\; \forall f \in (iota) \to (\operatorname{LinearMap}\left(\operatorname{RingHom}.\operatorname{id}\left(k\right), M, M\right)),\; (\forall x \in (iota) \to (M),\; \forall i \in iota,\; (\operatorname{DFunLike}.\operatorname{coe}\left(T, x, i\right)) = (\operatorname{DFunLike}.\operatorname{coe}\left(f\left(i\right), x\left(sigma\left(i\right)\right)\right))) \Rightarrow ((\operatorname{DFunLike}.\operatorname{coe}\left(\operatorname{LinearMap}.\operatorname{trace}\left(k, (iota) \to (M)\right), T\right)) = (\operatorname{Finset}.\operatorname{sum}\left(\operatorname{Finset}.\operatorname{univ}, \lambda (i: iota) \mapsto (\operatorname{ite}\left((sigma\left(i\right)) = (i), \operatorname{DFunLike}.\operatorname{coe}\left(\operatorname{LinearMap}.\operatorname{trace}\left(k, M\right), f\left(i\right)\right), 0\right))\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/CliffordDecomposition.trace_pi_of_apply_eq` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors; Claude (2026). *TauCeti finite representation and character theory*. URL: <https://github.com/TauCetiProject/TauCeti/tree/a780c7ad6beb23f60a17351a492d177878020ad5>.

*Commentary.*

The displayed conclusion holds under the stated hypotheses.

**Definition 1.3 (Clifford sum).**

$$\forall k \in Type*,\; \forall G \in Type*,\; [\operatorname{Field}\left(k\right)], [\operatorname{Group}\left(G\right)], \forall N \in \operatorname{Subgroup}\left(G\right),\; [\operatorname{Subgroup}.\operatorname{Normal}\left(N\right)], \forall V \in \operatorname{FDRep}\left(k, \operatorname{Subtype}\left(\lambda (x: G) \mapsto (\operatorname{Membership}.\operatorname{mem}\left(N, x\right))\right)\right),\; [\operatorname{Finite}\left(\operatorname{HasQuotient}.\operatorname{Quotient}\left(G, \operatorname{MulAction}.\operatorname{stabilizer}\left(G, \operatorname{CategoryTheory}.\operatorname{toSkeleton}\left(V\right)\right)\right)\right)], \forall e \in \operatorname{Nat},\; \operatorname{D5}.\operatorname{S3}.\operatorname{FiniteGroups}.\operatorname{CliffordDecomposition}.\operatorname{FDRep}.\operatorname{cliffordSum}\left(V, e\right) = (\operatorname{D5}.\operatorname{S3}.\operatorname{FiniteGroups}.\operatorname{FiniteCharacterAlgebra}.\operatorname{FDRep}.\operatorname{ofShrink}\left(\operatorname{Representation}.\operatorname{ofModule}'\left(\forall q \in \operatorname{HasQuotient}.\operatorname{Quotient}\left(G, \operatorname{MulAction}.\operatorname{stabilizer}\left(G, \operatorname{CategoryTheory}.\operatorname{toSkeleton}\left(V\right)\right)\right),\; (\operatorname{Fin}\left(e\right)) \to (\operatorname{Representation}.\operatorname{asModule}\left(\operatorname{FDRep}.\rho\left(\operatorname{CategoryTheory}.\operatorname{Functor}.\operatorname{obj}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{FiniteGroups}.\operatorname{CliffordConstituents}.\operatorname{TauCeti}.\operatorname{conjNormalFDRepFunctor}\left(\operatorname{Quotient}.\operatorname{out}\left(q\right)\right), V\right)\right)\right))\right)\right))$$

*Formalization.* `D5/S3/FiniteGroups/CliffordDecomposition.cliffordSum` (`✓ std3`).

*Citation.* The Tau Ceti contributors; Claude (2026). *TauCeti finite representation and character theory*. URL: <https://github.com/TauCetiProject/TauCeti/tree/a780c7ad6beb23f60a17351a492d177878020ad5>.

*Commentary.*

The formula defines the displayed algebraic construction.

**Theorem 1.4 (Finrank clifford sum).**

$$\forall k \in Type*,\; \forall G \in Type*,\; [\operatorname{Field}\left(k\right)], [\operatorname{Group}\left(G\right)], \forall N \in \operatorname{Subgroup}\left(G\right),\; [\operatorname{Subgroup}.\operatorname{Normal}\left(N\right)], \forall V \in \operatorname{FDRep}\left(k, \operatorname{Subtype}\left(\lambda (x: G) \mapsto (\operatorname{Membership}.\operatorname{mem}\left(N, x\right))\right)\right),\; [\operatorname{Finite}\left(\operatorname{HasQuotient}.\operatorname{Quotient}\left(G, \operatorname{MulAction}.\operatorname{stabilizer}\left(G, \operatorname{CategoryTheory}.\operatorname{toSkeleton}\left(V\right)\right)\right)\right)], \forall e \in \operatorname{Nat},\; (\operatorname{Module}.\operatorname{finrank}\left(k, \operatorname{FGModuleCat}.\operatorname{carrier}\left(\operatorname{Action}.\operatorname{V}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{FiniteGroups}.\operatorname{CliffordDecomposition}.\operatorname{FDRep}.\operatorname{cliffordSum}\left(V, e\right)\right)\right)\right)) = (\operatorname{HMul}.\operatorname{hMul}\left(\operatorname{HMul}.\operatorname{hMul}\left(\operatorname{Nat}.\operatorname{card}\left(\operatorname{HasQuotient}.\operatorname{Quotient}\left(G, \operatorname{MulAction}.\operatorname{stabilizer}\left(G, \operatorname{CategoryTheory}.\operatorname{toSkeleton}\left(V\right)\right)\right)\right), e\right), \operatorname{Module}.\operatorname{finrank}\left(k, \operatorname{FGModuleCat}.\operatorname{carrier}\left(\operatorname{Action}.\operatorname{V}\left(V\right)\right)\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/CliffordDecomposition.finrank_cliffordSum` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors; Claude (2026). *TauCeti finite representation and character theory*. URL: <https://github.com/TauCetiProject/TauCeti/tree/a780c7ad6beb23f60a17351a492d177878020ad5>.

*Commentary.*

The displayed conclusion holds under the stated hypotheses.

**Theorem 1.5 (Character clifford sum).**

$$\forall k \in Type*,\; \forall G \in Type*,\; [\operatorname{Field}\left(k\right)], [\operatorname{Group}\left(G\right)], \forall N \in \operatorname{Subgroup}\left(G\right),\; [\operatorname{Subgroup}.\operatorname{Normal}\left(N\right)], \forall V \in \operatorname{FDRep}\left(k, \operatorname{Subtype}\left(\lambda (x: G) \mapsto (\operatorname{Membership}.\operatorname{mem}\left(N, x\right))\right)\right),\; [\operatorname{Finite}\left(\operatorname{HasQuotient}.\operatorname{Quotient}\left(G, \operatorname{MulAction}.\operatorname{stabilizer}\left(G, \operatorname{CategoryTheory}.\operatorname{toSkeleton}\left(V\right)\right)\right)\right)], \forall e \in \operatorname{Nat},\; \forall x \in \operatorname{Subtype}\left(\lambda (x: G) \mapsto (\operatorname{Membership}.\operatorname{mem}\left(N, x\right))\right),\; (\operatorname{FDRep}.\operatorname{character}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{FiniteGroups}.\operatorname{CliffordDecomposition}.\operatorname{FDRep}.\operatorname{cliffordSum}\left(V, e\right), x\right)) = (\operatorname{HMul}.\operatorname{hMul}\left(\operatorname{Nat}.\operatorname{cast}\left(e\right), \operatorname{finsum}\left(\lambda (q: \operatorname{HasQuotient}.\operatorname{Quotient}\left(G, \operatorname{MulAction}.\operatorname{stabilizer}\left(G, \operatorname{CategoryTheory}.\operatorname{toSkeleton}\left(V\right)\right)\right)) \mapsto (\operatorname{FDRep}.\operatorname{character}\left(\operatorname{CategoryTheory}.\operatorname{Functor}.\operatorname{obj}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{FiniteGroups}.\operatorname{CliffordConstituents}.\operatorname{TauCeti}.\operatorname{conjNormalFDRepFunctor}\left(\operatorname{Quotient}.\operatorname{out}\left(q\right)\right), V\right), x\right))\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/CliffordDecomposition.character_cliffordSum` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors; Claude (2026). *TauCeti finite representation and character theory*. URL: <https://github.com/TauCetiProject/TauCeti/tree/a780c7ad6beb23f60a17351a492d177878020ad5>.

*Commentary.*

The displayed conclusion holds under the stated hypotheses.

**Theorem 1.6 (Clifford restrict iso).**

$$\forall k \in Type*,\; \forall G \in Type*,\; [\operatorname{Field}\left(k\right)], [\operatorname{Group}\left(G\right)], \forall N \in \operatorname{Subgroup}\left(G\right),\; [\operatorname{Subgroup}.\operatorname{Normal}\left(N\right)], [\operatorname{IsAlgClosed}\left(k\right)], \forall W \in \operatorname{FDRep}\left(k, G\right),\; [\operatorname{CategoryTheory}.\operatorname{Simple}\left(W\right)], \exists V \in \operatorname{FDRep}\left(k, \operatorname{Subtype}\left(\lambda (x: G) \mapsto (\operatorname{Membership}.\operatorname{mem}\left(N, x\right))\right)\right),\; \exists [\operatorname{CategoryTheory}.\operatorname{Simple}\left(V\right)], \exists [\operatorname{Finite}\left(\operatorname{HasQuotient}.\operatorname{Quotient}\left(G, \operatorname{MulAction}.\operatorname{stabilizer}\left(G, \operatorname{CategoryTheory}.\operatorname{toSkeleton}\left(V\right)\right)\right)\right)], \exists e \in \operatorname{Nat},\; (\operatorname{Ne}\left(e, 0\right)) \land (\operatorname{Nonempty}\left(\operatorname{CategoryTheory}.\operatorname{Iso}\left(\operatorname{CategoryTheory}.\operatorname{Functor}.\operatorname{obj}\left(\operatorname{Action}.\operatorname{res}\left(\operatorname{FGModuleCat}\left(k\right), \operatorname{Subgroup}.\operatorname{subtype}\left(N\right)\right), W\right), \operatorname{D5}.\operatorname{S3}.\operatorname{FiniteGroups}.\operatorname{CliffordDecomposition}.\operatorname{FDRep}.\operatorname{cliffordSum}\left(V, e\right)\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/CliffordDecomposition.clifford_restrict_iso` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors; Claude (2026). *TauCeti finite representation and character theory*. URL: <https://github.com/TauCetiProject/TauCeti/tree/a780c7ad6beb23f60a17351a492d177878020ad5>.

*Commentary.*

The displayed conclusion holds under the stated hypotheses.

## References

- Truth anchor: `D5/S3/FiniteGroups/CliffordDecomposition.character_cliffordSum`
- Truth anchor: `D5/S3/FiniteGroups/CliffordDecomposition.cliffordSum`
- Truth anchor: `D5/S3/FiniteGroups/CliffordDecomposition.clifford_restrict_iso`
- Truth anchor: `D5/S3/FiniteGroups/CliffordDecomposition.finrank_cliffordSum`
- Truth anchor: `D5/S3/FiniteGroups/CliffordDecomposition.isUnit_natCard_subgroup`
- Truth anchor: `D5/S3/FiniteGroups/CliffordDecomposition.trace_pi_of_apply_eq`
- Dependency: [D5/S3/FiniteGroups/CliffordConstituents](CliffordConstituents.md)
- Dependency: [D5/S3/FiniteGroups/FiniteCharacterAlgebra](FiniteCharacterAlgebra.md)
