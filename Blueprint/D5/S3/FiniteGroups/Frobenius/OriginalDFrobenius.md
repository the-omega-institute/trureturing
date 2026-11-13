# The original division ring

## Abstract

Frobenius divisibility and actual regular coordinates over the original Schur division ring.

**Theorem 1.1 (index dvd originalD finrank).**

$$\forall k \in Type*,\; \forall G \in Type*,\; \forall V \in Type*,\; [Group\left(G\right)], [Finite\left(G\right)], [Field\left(k\right)], [AddCommGroup\left(V\right)], [Module\left(k, V\right)], \forall N \in Subgroup\left(G\right),\; [\operatorname{Subgroup}.\operatorname{Normal}\left(N\right)], \forall rho \in Representation\left(k, G, V\right),\; [\operatorname{Module}.\operatorname{Finite}\left(k, V\right)], [\operatorname{Representation}.\operatorname{IsIrreducible}\left(rho\right)], \forall hfix \in \left(\forall g \in G,\; \neg (\operatorname{Membership}.\operatorname{mem}\left(N, g\right)) \Rightarrow \left(\forall n \in N,\; \operatorname{MulAut}.\operatorname{conjNormal}\left(g\right)\left(n\right) = n \Rightarrow n = 1\right)\right),\; \forall hnt \in \neg (\operatorname{Representation}.\operatorname{IsTrivial}\left(\operatorname{MonoidHom}.\operatorname{comp}\left(rho, \operatorname{Subgroup}.\operatorname{subtype}\left(N\right)\right)\right)),\; \operatorname{Dvd}.\operatorname{dvd}\left(\operatorname{Subgroup}.\operatorname{index}\left(N\right), \operatorname{Module}.\operatorname{finrank}\left(\operatorname{Module}.\operatorname{End}\left(MonoidAlgebra\left(k, G\right), \operatorname{Representation}.\operatorname{asModule}\left(rho\right)\right), \operatorname{Representation}.\operatorname{asModule}\left(rho\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/Frobenius/OriginalDFrobenius.index_dvd_originalD_finrank` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let G be finite, N normal, and suppose that every conjugation by g outside N fixes only the identity in N. Let rho be a finite-dimensional irreducible representation over an arbitrary field k, whose restriction to N is nontrivial. Set W = rho.asModule and D = Module.End k[G] W, acting on the left by evaluation. Then N.index divides Module.finrank D W. The scalar, group and carrier universes are independent.

Choose a simple restricted constituent and its actual isotypic component U. The original-D Clifford theorem gives dim_D W = [G:H] dim_D U for its actual inertia H. The Hall argument from Yawara Ishida's KernelComplement, revision ba8ec35982ceecbd31ca987cbe0cee30477f4883, derives an actual complement C from the fixed-point-free hypothesis; pinned Mathlib supplies Schur-Zassenhaus. Restrict C to J = C intersect H. Then N is contained in H, N and J complement each other in H, and |J| = [H:N].

The actual image of k[N] on U is simple because U is semisimple and isotypic. Its center F is a field. Actual original-D endomorphisms commute with this image, so the center acts by D-linear operators. Actual J operators act covariantly on these center operators. The checked center-kernel theorem proves that J acts faithfully on F. Taking K = F^J, the fixed-field Galois instance and the actual equivalence J = Gal(F/K) are supplied by Mathlib. Descent and a normal basis give dim_D U = |J| dim_D S, with no K-to-D embedding or F/D scalar tower. Index multiplication yields the asserted divisibility.

Normal-N invariants are a G-subrepresentation. Global irreducibility and nontrivial N action force them to be zero; consequently the nonzero actual component has nontrivial restricted action. No complement, faithfulness, semisimplicity, decomposition, normal basis, characteristic condition, splitting field, or commutativity of D is assumed.

**Theorem 1.2 (exists complement originalD regular).**

$$\forall k \in Type*,\; \forall G \in Type*,\; \forall V \in Type*,\; [Group\left(G\right)], [Finite\left(G\right)], [Field\left(k\right)], [AddCommGroup\left(V\right)], [Module\left(k, V\right)], \forall N \in Subgroup\left(G\right),\; [\operatorname{Subgroup}.\operatorname{Normal}\left(N\right)], \forall rho \in Representation\left(k, G, V\right),\; [\operatorname{Module}.\operatorname{Finite}\left(k, V\right)], [\operatorname{Representation}.\operatorname{IsIrreducible}\left(rho\right)], \forall hfix \in \left(\forall g \in G,\; \neg (\operatorname{Membership}.\operatorname{mem}\left(N, g\right)) \Rightarrow \left(\forall n \in N,\; \operatorname{MulAut}.\operatorname{conjNormal}\left(g\right)\left(n\right) = n \Rightarrow n = 1\right)\right),\; \forall hnt \in \neg (\operatorname{Representation}.\operatorname{IsTrivial}\left(\operatorname{MonoidHom}.\operatorname{comp}\left(rho, \operatorname{Subgroup}.\operatorname{subtype}\left(N\right)\right)\right)),\; \exists C \in Subgroup\left(G\right),\; \operatorname{Subgroup}.\operatorname{IsComplement}'\left(N, C\right) \land \left(\exists S \in Submodule\left(\operatorname{Module}.\operatorname{End}\left(MonoidAlgebra\left(k, G\right), \operatorname{Representation}.\operatorname{asModule}\left(rho\right)\right), \operatorname{Representation}.\operatorname{asModule}\left(rho\right)\right),\; \exists E \in LinearEquiv\left(\operatorname{RingHom}.\operatorname{id}\left(\operatorname{Module}.\operatorname{End}\left(MonoidAlgebra\left(k, G\right), \operatorname{Representation}.\operatorname{asModule}\left(rho\right)\right)\right), \operatorname{Representation}.\operatorname{asModule}\left(rho\right), C \to S\right),\; \forall c \in C,\; \forall v \in \operatorname{Representation}.\operatorname{asModule}\left(rho\right),\; \forall x \in C,\; E\left(\operatorname{OriginalDCliffordCandidate}.\operatorname{originalDTranslate}\left(rho, c, v\right), x\right) = E\left(v, \operatorname{Inv}.\operatorname{inv}\left(c\right) \cdot x\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/Frobenius/OriginalDFrobenius.exists_complement_originalD_regular` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the same hypotheses there exist an actual complement C, a D-submodule S of W, and a D-linear equivalence E : W -> (C -> S) satisfying E(rho(c)v)(x) = E(v)(c^(-1)x). This is an equivalence for the actual complement operators, with inverse on the left of the index.

First construct equivariant regular coordinates on U for J by normal-basis descent over the faithful actual center. The vector associated with the identity coordinate generates the J-coordinate blocks. Sum its actual translates over C to obtain a D-linear map from C -> S to W. The actual complement factorization and inertia stability show that its image contains every G-translate of U. This image is a k[G]-submodule; irreducibility makes it all of W. The original-D Clifford rank identity gives equality of domain and codomain dimensions, proving bijectivity. Reindexing the actual operator sum proves C-equivariance directly. Thus equality of dimensions is used only after constructing the map, proving surjectivity, and identifying its action.

The equivalence uses the original Schur division ring throughout, without replacing it by the coefficient field or by a commutative division ring. The useful passage from group action to arithmetic is that a faithful action on the actual component center supplies fixed-field Galois descent and normal-basis coordinates. These coordinates are linear for the original D-action because the center operators commute with D. Clifford induction assembles them into full-complement regular coordinates; each complement coordinate has the same D-dimension, so its order, equal to N.index, divides the total dimension. Hall coprimality, Schur-Zassenhaus, Skolem-Noether, semilinear descent and normal bases are classical results or reused proofs. The formal integration constructs the actual centers, inertia components and equivariant maps together; it makes no global novelty claim.

## References

- Truth anchor: `D5/S3/FiniteGroups/Frobenius/OriginalDFrobenius.exists_complement_originalD_regular`
- Truth anchor: `D5/S3/FiniteGroups/Frobenius/OriginalDFrobenius.index_dvd_originalD_finrank`
- Dependency: [D5/S3/FiniteGroups/Frobenius/NormalizerImageAction](NormalizerImageAction.md)
- Dependency: [D5/S3/FiniteGroups/Frobenius/OriginalDClifford](OriginalDClifford.md)
- Dependency: [D5/S3/FiniteGroups/Frobenius/OriginalDRegularAction](OriginalDRegularAction.md)
