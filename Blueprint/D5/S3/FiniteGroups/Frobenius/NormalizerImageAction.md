# NormalizerImageAction

## Abstract

NormalizerImageAction

The representation, image, image automorphisms and center action are constructed from the same operators on the original carrier. Semisimplicity and isotypy refer to the actual restricted group-algebra module. The algebra proof of Skolem-Noether is reused from AxiomMath/Stacks at revision 5ed82d14634e8d9576bb844c7bd4e3da66d450e7, Apache-2.0. Neither faithfulness on the center nor an inner implementer is assumed.

Conjugating an actual operator agrees with applying normal-subgroup conjugation to its group-algebra input. The identity follows by group-algebra induction.

An element of the normal subgroup acts on the image by conjugation by its actual representation unit.

The normal subgroup therefore acts trivially on the center.

The simple image center is a field. If an element fixes it, Skolem-Noether supplies an inner implementer in the actual image. The Frobenius inner-action obstruction then forces that element into the normal subgroup. A complement intersects this kernel trivially, giving a faithful action on the actual center.

The notation with actualModule in each of the two module hypotheses installs exactly the representation-induced k[N]-action on U. The group H need not be finite; only N is required finite here. The scalar field, group and carrier universes are independent.

**Theorem 1.1 (complement center kernel eq bot).**

$$\forall k \in Type*,\; \forall H \in Type*,\; \forall U \in Type*,\; [Field\left(k\right)], [Group\left(H\right)], [AddCommGroup\left(U\right)], [Module\left(k, U\right)], \forall rho \in MonoidHom\left(H, LinearEquiv\left(\operatorname{RingHom}.\operatorname{id}\left(k\right), U, U\right)\right),\; \forall N \in Subgroup\left(H\right),\; [\operatorname{Subgroup}.\operatorname{Normal}\left(N\right)], [Finite\left(N\right)], [\operatorname{Module}.\operatorname{Finite}\left(k, U\right)], [Nontrivial\left(U\right)], \forall hsemi \in \operatorname{with} \operatorname{NormalizerImageAction}.\operatorname{actualModule}\left(rho, N\right), IsSemisimpleModule\left(MonoidAlgebra\left(k, N\right), U\right),\; \forall hiso \in \operatorname{with} \operatorname{NormalizerImageAction}.\operatorname{actualModule}\left(rho, N\right), IsIsotypic\left(MonoidAlgebra\left(k, N\right), U\right),\; \forall hfix \in \left(\forall h \in H,\; \left(\neg h \in N\right) \Rightarrow \left(\forall n \in N,\; \operatorname{MulAut}.\operatorname{conjNormal}\left(h\right)\left(n\right) = n \Rightarrow n = 1\right)\right),\; \forall hnt \in \left(\neg \operatorname{Representation}.\operatorname{IsTrivial}\left(\operatorname{MonoidHom}.\operatorname{comp}\left(\operatorname{NormalizerImageAction}.\operatorname{representation}\left(rho\right), \operatorname{Subgroup}.\operatorname{subtype}\left(N\right)\right)\right)\right),\; \forall J \in Subgroup\left(H\right),\; \forall hJ \in \operatorname{Subgroup}.\operatorname{IsComplement}'\left(N, J\right),\; \operatorname{MonoidHom}.\operatorname{ker}\left(\operatorname{MonoidHom}.\operatorname{comp}\left(\operatorname{NormalizerImageAction}.\operatorname{centerAction}\left(rho, N\right), \operatorname{Subgroup}.\operatorname{subtype}\left(J\right)\right)\right) = \operatorname{Bot}.\operatorname{bot}$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/Frobenius/NormalizerImageAction.complement_center_kernel_eq_bot` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A complement element acting trivially on the actual component center must lie in N and hence must be the identity.

## References

- Truth anchor: `D5/S3/FiniteGroups/Frobenius/NormalizerImageAction.complement_center_kernel_eq_bot`
- Dependency: [D5/S3/FiniteGroups/Frobenius/FiniteIsotypicImageSimple](FiniteIsotypicImageSimple.md)
- Dependency: [D5/S3/FiniteGroups/FrobeniusInnerActionObstruction](../FrobeniusInnerActionObstruction.md)
- Dependency: [D5/S3/FiniteGroups/GroupAlgebra/SkolemNoether](../GroupAlgebra/SkolemNoether.md)
