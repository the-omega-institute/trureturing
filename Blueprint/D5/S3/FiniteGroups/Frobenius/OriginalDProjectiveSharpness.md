# Original-D modular projectivity counterexample

## Abstract

A modular dihedral representation separates conjugation freeness from a trivial subgroup action.

**Theorem 1.1 (Nonprojectivity with full original-D hypotheses over F7).**

$$\neg (\operatorname{Module}.\operatorname{Projective}\left(MonoidAlgebra\left(k, G\right), \operatorname{Representation}.\operatorname{asModule}\left(rho\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/Frobenius/OriginalDProjectiveSharpness.originalD_counterexample` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The closed proposition projectivity_claim asserts that the actual group-algebra module rho.asModule is projective over k[G]. Here k is ZMod 7, G is DihedralGroup 21, and V is the two-dimensional coordinate space Fin 2 to k. The refutation consumes a single constructed countermodel carrying all thirteen facts displayed below; its final clause contradicts precisely that positive projectivity assertion.

$Finite\left(G\right) \land \left(\operatorname{Nat}.\operatorname{card}\left(G\right) = 42 \land \left(FiniteDimensional\left(k, V\right) \land \left(\operatorname{Representation}.\operatorname{IsIrreducible}\left(rho\right) \land \left(\operatorname{Subgroup}.\operatorname{Normal}\left(N\right) \land \left(\left(\forall g \in G,\; \neg (\operatorname{Membership}.\operatorname{mem}\left(N, g\right)) \Rightarrow \left(\forall n \in N,\; \operatorname{MulAut}.\operatorname{conjNormal}\left(g\right)\left(n\right) = n \Rightarrow n = 1\right)\right) \land \left(\neg (\operatorname{Representation}.\operatorname{IsTrivial}\left(\operatorname{MonoidHom}.\operatorname{comp}\left(rho, \operatorname{Subgroup}.\operatorname{subtype}\left(N\right)\right)\right)) \land \left(Finite\left(H\right) \land \left(\operatorname{Nat}.\operatorname{card}\left(H\right) = 7 \land \left(\operatorname{Representation}.\operatorname{IsTrivial}\left(\operatorname{MonoidHom}.\operatorname{comp}\left(rho, \operatorname{Subgroup}.\operatorname{subtype}\left(H\right)\right)\right) \land \left(\operatorname{Nat}.\operatorname{card}\left(N\right) = 21 \land \left(\neg (IsUnit\left((\operatorname{Nat}.\operatorname{card}\left(N\right) : k)\right)) \land \neg (\operatorname{Module}.\operatorname{Projective}\left(MonoidAlgebra\left(k, G\right), \operatorname{Representation}.\operatorname{asModule}\left(rho\right)\right))\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$

This is the classical two-dimensional dihedral construction over the field F7. Let G be the dihedral group with 42 elements and N its cyclic rotation subgroup of order 21. Send one rotation to A = diag(2,4), and one reflection to the coordinate exchange S. The identities A cubed equals the identity, S squared equals the identity, and SAS equals the inverse of A define an action factoring through the dihedral group with six elements. For the convention sr(i) = s times r to the i, its matrix is S times A to the i; reversing this order changes the reflection matrices.

Every element outside N is a reflection, and conjugates each rotation to its inverse. A fixed rotation therefore has square equal to the identity. Since N has odd order 21, that rotation is the identity. This is precisely the original condition quantified over all g outside N and all n in N; it is not restricted to a chosen complement or to a chosen generator.

For irreducibility, let W be a nonzero invariant subspace and choose a nonzero vector (x,y) in W. Applying S when necessary makes x nonzero. Applying A minus four times the identity gives (5x,0). Division by 5x puts the first coordinate vector in W, and S puts the second coordinate vector in W. Hence W is the full space. The rotation restriction is nontrivial because A moves the first coordinate vector. This proof uses only the two distinct eigenvalues and the exchange of the coordinate axes; it does not use Maschke's theorem, an algebraic closure, or invertibility of the group order.

The tag-preserving projection from G to the dihedral group with six elements reduces rotation coordinates modulo three. Its kernel H consists of the seven rotations with coordinates divisible by three. The representation factors through this projection, so H acts trivially. H has order seven, while the Frobenius rotation subgroup N has order 21: these are different roles and different subgroups.

The mathematical distinction exposed here is between conjugation on N and the linear action on the representation space. Conjugation is fixed-point-free outside N, yet a subgroup of characteristic order acts trivially on an irreducible representation whose restriction to N is nontrivial.

To prove nonprojectivity of the actual full group-algebra module, apply ProjectiveKernelOrder.isUnit_natCard_of_projective_of_isTrivial with the field k = F7, group G = DihedralGroup 21, nonzero space V = Fin 2 to k, representation rho, and finite subgroup H. Its two proof premises are the supposed projectivity of this exact rho.asModule and the proved triviality of rho restricted to H. The theorem forces Nat.card H to be a unit in k. The proved order Nat.card H = 7 makes that scalar zero in F7, contradicting that zero is not a unit. This directly reuses the general obstruction, including its restriction and augmentation argument, without a second private augmentation proof or an assumed homological premise.

The full rotation order is 21, whose image in F7 is zero and hence not a unit. Thus OriginalDFrobenius.projective_originalD, the sufficient theorem in OriginalDProjective, cannot simply drop its invertibility assumption. Conjugation freeness and regular complement data do not prevent a characteristic-order subgroup from being invisible to the representation. This single counterexample gives an existential limit on that sufficient theorem; it does not assert that invertibility of the order of N is universally necessary. The example and the augmentation argument are classical, without a literature novelty claim.

## References

- Truth anchor: `D5/S3/FiniteGroups/Frobenius/OriginalDProjectiveSharpness.originalD_counterexample`
- Dependency: [D5/S3/FiniteGroups/GroupAlgebra/ProjectiveKernelOrder](../GroupAlgebra/ProjectiveKernelOrder.md)
