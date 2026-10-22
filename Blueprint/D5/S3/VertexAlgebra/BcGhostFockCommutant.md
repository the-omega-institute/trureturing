# The Original Infinite Ghost Kernel and Scalar Commutant

## Abstract

The common signed-deletion kernel is the vacuum line, and the actual ghost-mode commutant consists of scalars over every commutative ring.

Fix any universe u and any K : Type u with [CommRing K]. There is no field, nontriviality, characteristic, irreducibility or finite-dimensionality assumption. Fock(K) is (Finset Nat) ->0 K: finite superpositions of arbitrary finite subsets of the unbounded natural site set. Omega(K) denotes exactly BcGhostFockSupport.vacuum, namely Finsupp.single emptyset 1. coeff(v,S) denotes the actual Finsupp coefficient v S, not an inner product or a chosen functional.

At site i, annihilate deletes an occupied i with coefficient sign(i,S)=(-1)^(card {s in S | s<i}) and vanishes when i is absent. The actual integer b and c modes are the signed insertion/deletion operators from BcGhostFockSupport. Composition is written with circ; End(K,Fock(K)) means Module.End K (Fock K), and id means its LinearMap.id. Scalar multiplication in the formulas is K-module scalar multiplication.

**Theorem 1.1 (The simultaneous deletion kernel is exactly the original vacuum line).**

$$\forall K:Type^{u}, [\operatorname{CommRing}\left(K\right)],\ \forall v:\operatorname{Fock}\left(K\right),\ (\forall i:\mathbb{N}, \operatorname{annihilate}\left(K, i, v\right)=0) \iff v=\operatorname{coeff}\left(v, \emptyset\right)\cdot\operatorname{Omega}\left(K\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/BcGhostFockCommutant.annihilator_kernel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* W. Eholzer, L. Feher, A. Honecker (1997). *Ghost Systems: A Vertex Algebra Point of View*. DOI: [10.1016/S0550-3213(98)00061-3](https://doi.org/10.1016/S0550-3213(98)00061-3). URL: <https://arxiv.org/abs/hep-th/9708160>.

*Commentary.*

The complete original telescope is {K : Type u} [CommRing K] (v : Fock K). Its conclusion is (forall i : Nat, annihilate i v = 0) iff v = v emptyset smul vacuum. Both directions concern this same v and the actual original vacuum.

The live proof first establishes the coefficient identity (annihilate i v)(S.erase i)=sign(i,S)*v(S) whenever i belongs to S. Linear Finsupp induction reduces it to basis states. Among states containing i, equality after erasing i forces equality before erasing, by reinserting i. Thus no other basis coefficient contributes to that coordinate.

For a nonempty S, choose an occupied i. Common annihilation makes sign(i,S)*v(S) zero. The sign squares to one over every commutative ring, so multiplying by it gives v(S)=0 without cancellation by an arbitrary nonzero element. Finsupp extensionality leaves exactly the empty-subset coefficient. Conversely, signed deletion annihilates the empty-subset vacuum; linearity annihilates each scalar multiple.

**Theorem 1.2 (Commuting with every original b and c mode forces a scalar ghost endomorphism).**

$$\forall K:Type^{u}, [\operatorname{CommRing}\left(K\right)],\ \forall T:\operatorname{End}\left(K, \operatorname{Fock}\left(K\right)\right),\ \forall (hb:{\forall m:\mathbb{Z}, T\circ\operatorname{b}\left(K, m\right)=\operatorname{b}\left(K, m\right)\circ T}),\ \forall (hc:{\forall n:\mathbb{Z}, T\circ\operatorname{c}\left(K, n\right)=\operatorname{c}\left(K, n\right)\circ T}),\ T=\operatorname{coeff}\left(\operatorname{T}\left(\operatorname{Omega}\left(K\right)\right), \emptyset\right)\cdot id$$

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/BcGhostFockCommutant.mode_commutant_scalar` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* W. Eholzer, L. Feher, A. Honecker (1997). *Ghost Systems: A Vertex Algebra Point of View*. DOI: [10.1016/S0550-3213(98)00061-3](https://doi.org/10.1016/S0550-3213(98)00061-3). URL: <https://arxiv.org/abs/hep-th/9708160>.

*Commentary.*

The complete original telescope is {K : Type u} [CommRing K] (T : Module.End K (Fock K)), (hb : forall m : Int, T.comp (b m) = (b m).comp T), (hc : forall n : Int, T.comp (c n) = (c n).comp T). The exact conclusion is T = (T vacuum) emptyset smul LinearMap.id. Each commutation hypothesis ranges over all integers, not only creators, annihilators or a finite interval.

For an even natural site i the proof identifies annihilate i with c at integer index (i/2)+2; for an odd site it identifies annihilate i with b at integer index (i/2)-1. Here i/2 is natural-number division before the integer mode index is formed. These branch and parity identities show that T commutes with every deletion. Applying that commutation to vacuum and then annihilator_kernel gives T vacuum = (T vacuum) emptyset smul vacuum.

Set a=(T vacuum) emptyset and W=ker(T-a smul id). The vacuum belongs to W. The original hb and hc hypotheses and K-linearity make W stable under every b creator at m<=-2 and every c creator at n<=1. The original creation_cyclic theorem makes W the top submodule. Extensionality gives the endomorphism equality on every finite-support state.

This is a statement in the endomorphism algebra of the ghost carrier itself. It neither supplies nor assumes a bridge from endomorphisms of a matter tensor ghost carrier to tensor products of endomorphism algebras. In particular it does not claim that a ghost-commuting total-state operator must be a scalar on the matter factor.

The existing eholzer1997ghost library note supplies background for the ghost Fock and shifted mode conventions. It is acknowledged, not used as a claim that the paper proves these exact ring-parametric signed-Finsupp implementation theorems. Both derivations above are assessed as repository-derived. They are algebraic infrastructure reused by the original ghost suppliers, not literature novelty, BRST cohomology, a no-ghost theorem, complete string physics or an AdS result.

## References

- Truth anchor: `D5/S3/VertexAlgebra/BcGhostFockCommutant.annihilator_kernel`
- Truth anchor: `D5/S3/VertexAlgebra/BcGhostFockCommutant.mode_commutant_scalar`
- Dependency: [D5/S3/VertexAlgebra/BcGhostFockSupport](BcGhostFockSupport.md)
