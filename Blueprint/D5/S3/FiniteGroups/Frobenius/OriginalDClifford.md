# OriginalDClifford

## Abstract

Original D Clifford

Constituent conjugacy is reused from CliffordConstituents; direct sums and isotypic decomposition are from Mathlib. The integration retains the original endomorphism ring and constructs component transport and the inertia-coset correspondence. It requires no commutative replacement of D or additional decomposition assumption.

Fully invariant isotypic submodules are stable under every commuting scalar action. The direct-sum map is consequently linear over the independent commuting scalar semiring.

A semilinear automorphism of a module transports its isotypic component to the component of the transported submodule. Transport the defining family and use the inverse for the reverse inclusion.

The actual group operator is linear over the original Schur division ring, because endomorphisms of the group-algebra module commute with it. Semilinear transport identifies its image component.

The actual inertia subgroup is the stabilizer of the chosen isotypic component. Its cosets correspond bijectively to the components. The resulting product equivalence is linear over D = Module.End k[G] rho.asModule. Taking dimensions gives the original-D Clifford product formula, with independent field, group and carrier universes.

The ambient group need not be finite for this formula: finite dimension and irreducibility give finitely many isotypic components and hence finite actual inertia index. The component and inertia are constructed, not supplied as additional hypotheses. All field, group and carrier universes are independent.

**Theorem 1.1 (originalD finrank independent universes).**

$$\forall k \in Type*,\; \forall G \in Type*,\; \forall V \in Type*,\; [Field\left(k\right)], [Group\left(G\right)], [AddCommGroup\left(V\right)], [Module\left(k, V\right)], \forall N \in Subgroup\left(G\right),\; [\operatorname{Subgroup}.\operatorname{Normal}\left(N\right)], \forall rho \in Representation\left(k, G, V\right),\; [\operatorname{Module}.\operatorname{Finite}\left(k, V\right)], [\operatorname{Representation}.\operatorname{IsIrreducible}\left(rho\right)], \forall sigma \in Subrepresentation\left(\operatorname{MonoidHom}.\operatorname{comp}\left(rho, \operatorname{Subgroup}.\operatorname{subtype}\left(N\right)\right)\right),\; \forall hsigma \in IsAtom\left(sigma\right),\; \operatorname{Module}.\operatorname{finrank}\left(\operatorname{Module}.\operatorname{End}\left(MonoidAlgebra\left(k, G\right), \operatorname{Representation}.\operatorname{asModule}\left(rho\right)\right), \operatorname{Representation}.\operatorname{asModule}\left(rho\right)\right) = \operatorname{Subgroup}.\operatorname{index}\left(\operatorname{CliffordDecomposition}.\operatorname{Representation}.\operatorname{originalDActualInertia}\left(rho, sigma, hsigma\right)\right) \cdot \operatorname{Module}.\operatorname{finrank}\left(\operatorname{Module}.\operatorname{End}\left(MonoidAlgebra\left(k, G\right), \operatorname{Representation}.\operatorname{asModule}\left(rho\right)\right), \operatorname{OriginalDCliffordCandidate}.\operatorname{originalDBaseComponent}\left(rho, sigma, hsigma\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/Frobenius/OriginalDClifford.originalD_finrank_independent_universes` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The original endomorphism ring acts on each transported isotypic component, and dimensions multiply by the actual inertia index.

## References

- Truth anchor: `D5/S3/FiniteGroups/Frobenius/OriginalDClifford.originalD_finrank_independent_universes`
- Dependency: [D5/S3/FiniteGroups/CliffordConstituents](../CliffordConstituents.md)
