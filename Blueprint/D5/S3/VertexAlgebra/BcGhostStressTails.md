# Actual Ghost Stress Tails

## Abstract

Actual ghost stress modes have a state-dependent positive tail, making the outer ghost-stress normal ordering finite on every state.

Let K be any commutative ring and Fock(K)=Finset(N) ->0 K. A state is an arbitrary finite superposition of finite occupied subsets. Write B(v)=sup id (occupied(v)), where occupied(v) is the union of the subsets in the Finsupp support. The supremum of the empty set is zero; B(v) is cast to Z in integer bounds. The bounds are sufficient and are not asserted to be sharp. No nontriviality, characteristic-zero or field hypothesis is imposed on K.

Use the signed insertion and deletion operators on this full carrier. The mode b_p creates for p<=-2 and annihilates otherwise; c_q creates for q<=1 and annihilates otherwise. The actual normal-ordered pair is b_p c_q for p<=-2 and minus c_q b_p otherwise. The stress operator is the statewise finite sum L_m(v)=finsum_k (m-k) :b_(m+k)c_(-k): v, with integer coefficients cast into K.

**Theorem 1.1 (Every high normal-ordered ghost pair vanishes on every state).**

$$\forall K:Type, [\operatorname{CommRing}\left(K\right)], \forall m, k\in \mathbb{Z}, v\in \operatorname{Fock}\left(K\right), 2\cdot\operatorname{sup}\left(\operatorname{occupied}\left(v\right), id\right)+4<m\Rightarrow \operatorname{normalPair}\left(K, m + k, -k, v\right)=0$$

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/BcGhostStressTails.normal_pair_high` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* W. Eholzer, L. Feher, A. Honecker (1997). *Ghost Systems: A Vertex Algebra Point of View*. DOI: [10.1016/S0550-3213(98)00061-3](https://doi.org/10.1016/S0550-3213(98)00061-3). URL: <https://arxiv.org/abs/hep-th/9708160>.

*Commentary.*

This is the termwise tail theorem used by the expanded-array BRST support argument. For the actual rectangle, the term c_(-n) normalPair(n+k,-k) g when n>=-1 and the term normalPair(n+k,-k) c_(-n) g otherwise must be killed separately at high n. The theorem supplies the first factor's vanishing on every state; it is not replaced by the aggregate L_high_mode statement, because later support reasoning reorders the two factors.

**Theorem 1.2 (Positive stress modes eventually kill every state).**

$$\forall K:Type, [\operatorname{CommRing}\left(K\right)], \forall v\in \operatorname{Fock}\left(K\right), \forall m\in \mathbb{Z}, 2\cdot\operatorname{sup}\left(\operatorname{occupied}\left(v\right), id\right)+4<m\Rightarrow \operatorname{L}\left(K, m, v\right)=0$$

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/BcGhostStressTails.L_high_mode` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* W. Eholzer, L. Feher, A. Honecker (1997). *Ghost Systems: A Vertex Algebra Point of View*. DOI: [10.1016/S0550-3213(98)00061-3](https://doi.org/10.1016/S0550-3213(98)00061-3). URL: <https://arxiv.org/abs/hep-th/9708160>.

*Commentary.*

Every actual normal-ordered summand vanishes for this m, not just those in a chosen finite interval. On a basis subset S put p=m+k and q=-k, so p+q=m. If p<=-2, the right c_q annihilator has site 2(q-2)>sup(S). If p>=-1, either the right b_p annihilator has site 2(p+1)+1>sup(S), or p is small and the left c_q annihilator has site 2(q-2)>sup(S). Deleting the b-site cannot introduce that c-site. Linearity extends this calculation to every state because every basis subset in its support has supremum at most B(v). The defining finsum is therefore zero.

Define outerNormalPair_n=c_(-n) composed with L_n for n>=-1, and L_n composed with c_(-n) for n<=-2, without an additional sign. This definition names only a support family; it does not define a complete BRST charge.

**Theorem 1.3 (The outer normal-ordering family has finite support).**

$$\forall K:Type, [\operatorname{CommRing}\left(K\right)], \forall v\in \operatorname{Fock}\left(K\right), \operatorname{HasFiniteSupport}\left(n\mapsto\operatorname{outerNormalPair}\left(K, n, v\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/BcGhostStressTails.outer_has_finite_support` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* W. Eholzer, L. Feher, A. Honecker (1997). *Ghost Systems: A Vertex Algebra Point of View*. DOI: [10.1016/S0550-3213(98)00061-3](https://doi.org/10.1016/S0550-3213(98)00061-3). URL: <https://arxiv.org/abs/hep-th/9708160>.

*Commentary.*

The support is contained in the integer interval [-B(v)-2,2B(v)+4]. Below its lower endpoint the right c_(-n) is deletion at site 2(-n-2)>B(v), which kills every basis subset of v. Above its upper endpoint the right L_n kills v by the positive stress tail theorem. Thus the actual outer family, with unrestricted integer mode indices, is finite on each state. This supplies a finite-support ingredient for constructing a charge rather than assuming that the charge sum is well-defined.

Eholzer-Feher-Honecker, hep-th/9708160v1, Section 2, equations (2.7)-(2.10) and (2.15), supplies the classical fermionic ghost conventions. Physical modes are shifted as b_m=b_math_(m+1) and c_n=c_math_(n-2). The explicit support bounds here are derived from the actual finite-subset operators. No proof code from the source is copied.

These bounds alone prove neither an all-state Virasoro identity nor central charge -26, current or field sign identities, a ghost-degree law, a matter charge, BRST nilpotence, BRST cohomology, complete string theory or AdS/CFT.

## References

- Truth anchor: `D5/S3/VertexAlgebra/BcGhostStressTails.L_high_mode`
- Truth anchor: `D5/S3/VertexAlgebra/BcGhostStressTails.normal_pair_high`
- Truth anchor: `D5/S3/VertexAlgebra/BcGhostStressTails.outer_has_finite_support`
- Dependency: [D5/S3/VertexAlgebra/BcGhostFockSupport](BcGhostFockSupport.md)
