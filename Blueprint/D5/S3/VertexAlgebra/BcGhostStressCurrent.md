# All-State Ghost Stress-Current Covariance

## Abstract

The actual ghost stress tensor acts on b and c with conformal weights two and minus one on every state.

K is any commutative ring and Fock(K) is the finite-support sum over all finite subsets of the natural numbers. At b-mode m<=-2, create at site 2(-m-2); otherwise delete at site 2(m+1)+1. At c-mode n<=1, create at site 2(1-n)+1; otherwise delete at site 2(n-2). In each branch the indicated natural site is the nonnegative integer value of its expression. Insertion and deletion use the parity of occupied lower sites.

Write N(p,q)=b_p c_q for p<=-2 and N(p,q)=-c_q b_p otherwise. The genuine linear stress operator is L_m v=sum_k (m-k) N(m+k,-k)v. Each input has a finite normal-ordering support interval; the sum defines an operator on the full carrier without a uniform cutoff.

**Theorem 1.1 (The b-modes anticommute).**

$$\forall K:Type, [\operatorname{CommRing}\left(K\right)], \forall m,n\in \mathbb{Z},\ \operatorname{b}\left(K, m\right) \operatorname{b}\left(K, n\right)+\operatorname{b}\left(K, n\right) \operatorname{b}\left(K, m\right)=0$$

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/BcGhostStressCurrent.b_b` (`✓ std3`). ∎

*Citation.* W. Eholzer, L. Feher, A. Honecker (1997). *Ghost Systems: A Vertex Algebra Point of View*. DOI: [10.1016/S0550-3213(98)00061-3](https://doi.org/10.1016/S0550-3213(98)00061-3). URL: <https://arxiv.org/abs/hep-th/9708160>.

*Commentary.*

For every commutative ring K and all integers m,n, b_m b_n+b_n b_m=0 in Module.End K (Fock K). The equality uses the actual signed insertion and deletion operators on all finite superpositions of finite subsets, not an assumed CAR representation.

**Theorem 1.2 (The c-modes anticommute).**

$$\forall K:Type, [\operatorname{CommRing}\left(K\right)], \forall m,n\in \mathbb{Z},\ \operatorname{c}\left(K, m\right) \operatorname{c}\left(K, n\right)+\operatorname{c}\left(K, n\right) \operatorname{c}\left(K, m\right)=0$$

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/BcGhostStressCurrent.c_c` (`✓ std3`). ∎

*Citation.* W. Eholzer, L. Feher, A. Honecker (1997). *Ghost Systems: A Vertex Algebra Point of View*. DOI: [10.1016/S0550-3213(98)00061-3](https://doi.org/10.1016/S0550-3213(98)00061-3). URL: <https://arxiv.org/abs/hep-th/9708160>.

*Commentary.*

For every commutative ring K and all integers m,n, c_m c_n+c_n c_m=0 in Module.End K (Fock K), for the same concrete carrier and signed operators.

**Theorem 1.3 (The mixed anticommutator is the identity at opposite modes).**

$$\forall K:Type, [\operatorname{CommRing}\left(K\right)], \forall m,n\in \mathbb{Z},\ \operatorname{b}\left(K, m\right) \operatorname{c}\left(K, n\right)+\operatorname{c}\left(K, n\right) \operatorname{b}\left(K, m\right)=\operatorname{delta}\left(m+n, 0\right) 1$$

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/BcGhostStressCurrent.b_c` (`✓ std3`). ∎

*Citation.* W. Eholzer, L. Feher, A. Honecker (1997). *Ghost Systems: A Vertex Algebra Point of View*. DOI: [10.1016/S0550-3213(98)00061-3](https://doi.org/10.1016/S0550-3213(98)00061-3). URL: <https://arxiv.org/abs/hep-th/9708160>.

*Commentary.*

For every commutative ring K and all integers m,n, b_m c_n+c_n b_m=if m+n=0 then 1 else 0 in Module.End K (Fock K). Here delta_(m+n,0) is one exactly when m+n=0 and zero otherwise; 1 is the identity endomorphism. No field, nontriviality or characteristic assumption is imposed.

**Theorem 1.4 (The b-current has weight two).**

$$\forall K:Type, [\operatorname{CommRing}\left(K\right)], \forall m,n\in \mathbb{Z},\ \operatorname{L}\left(K, m\right) \operatorname{b}\left(K, n\right)-\operatorname{b}\left(K, n\right) \operatorname{L}\left(K, m\right)={(m-n)} \operatorname{b}\left(K, m+n\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/BcGhostStressCurrent.L_b_commutator` (`✓ std3`). ∎

*Citation.* W. Eholzer, L. Feher, A. Honecker (1997). *Ghost Systems: A Vertex Algebra Point of View*. DOI: [10.1016/S0550-3213(98)00061-3](https://doi.org/10.1016/S0550-3213(98)00061-3). URL: <https://arxiv.org/abs/hep-th/9708160>.

*Commentary.*

For every commutative ring K and integers m,n, L_m b_n-b_n L_m=(m-n)b_(m+n) as K-linear endomorphisms. Equivalently the equality holds on every finite superposition of arbitrary finite subsets. The scalar is the integer mapped into K. There are no field, nontriviality or characteristic assumptions.

**Theorem 1.5 (The c-current has weight minus one).**

$$\forall K:Type, [\operatorname{CommRing}\left(K\right)], \forall m,n\in \mathbb{Z},\ \operatorname{L}\left(K, m\right) \operatorname{c}\left(K, n\right)-\operatorname{c}\left(K, n\right) \operatorname{L}\left(K, m\right)={(-2m-n)} \operatorname{c}\left(K, m+n\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/BcGhostStressCurrent.L_c_commutator` (`✓ std3`). ∎

*Citation.* W. Eholzer, L. Feher, A. Honecker (1997). *Ghost Systems: A Vertex Algebra Point of View*. DOI: [10.1016/S0550-3213(98)00061-3](https://doi.org/10.1016/S0550-3213(98)00061-3). URL: <https://arxiv.org/abs/hep-th/9708160>.

*Commentary.*

For every commutative ring K and integers m,n, L_m c_n-c_n L_m=(-2m-n)c_(m+n) as K-linear endomorphisms of exactly the same full carrier, with integer scalar mapped into K.

The exterior-coordinate equivalence identifies create_i with left multiplication by the exterior generator at i and annihilate_i with contraction by its coordinate functional. These are the concrete exterior_create and exterior_annihilate identities. Exterior multiplication and contraction give creation-creation and contraction-contraction anticommutation and the mixed Kronecker identity over any commutative ring. Splitting at b-mode -2 and c-mode 1 and checking the natural site indices gives the three integer-mode CAR. They in turn give [N(p,q),b_n]=delta_(q+n,0)b_p and [N(p,q),c_n]=-delta_(p+n,0)c_q. For each input v the two stress sums are evaluated in one interval enclosing the support for v, the support for the current applied to v, and the single surviving index. Linearity transports the finite sum and the CAR collapse it to that index. This argument uses the actual statewise support theorem.

Eholzer, Feher and Honecker, section 2 of hep-th/9708160, gives the conformal weights in equation (2.5), the Fock/CAR conventions in equations (2.7)-(2.10), and the stress-tensor modes in equation (2.15). The physical labels here are b_math(m+1) and c_math(n-2) in uniform vertex-algebra mode notation, which explains the coefficient m-k. These covariance laws do not establish the all-state Virasoro central charge -26, vacuum invariance, BRST cohomology, string amplitudes, Monster moonshine or AdS/CFT.

## References

- Truth anchor: `D5/S3/VertexAlgebra/BcGhostStressCurrent.L_b_commutator`
- Truth anchor: `D5/S3/VertexAlgebra/BcGhostStressCurrent.L_c_commutator`
- Truth anchor: `D5/S3/VertexAlgebra/BcGhostStressCurrent.b_b`
- Truth anchor: `D5/S3/VertexAlgebra/BcGhostStressCurrent.b_c`
- Truth anchor: `D5/S3/VertexAlgebra/BcGhostStressCurrent.c_c`
- Dependency: [D5/S3/VertexAlgebra/BcGhostExteriorOperators](BcGhostExteriorOperators.md)
