# Actual Ghost BRST Support

## Abstract

Actual ghost deletion and the support needed for an algebraic BRST charge.

K is any commutative ring, including the zero ring. A ghost state is a finitely supported K-linear combination of finite subsets of N. The occupied set is the union of the subsets in its coefficient support. The existing signed creation and deletion operators, b, c, normalPair and L are used without replacement by an abstract representation. Write B(g)=sup(occupied(g)), with sup(empty)=0.

**Theorem 1.1 (Actual deletion cannot add an occupied site).**

Lean statement: `D5/S3/VertexAlgebra/BcGhostBrstSupport.occupied_annihilate_subset`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/BcGhostBrstSupport.occupied_annihilate_subset` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every site i and every state g, the occupied set of annihilate(i)g is contained in occupied(g) with i erased. Every nonzero output basis coefficient originates in a supported input subset containing i, and its subset is exactly that input subset with i erased. Cancellation can remove coefficients but cannot create any other output subset.

**Theorem 1.2 (The shifted c-mode has an input-dependent lower tail).**

Lean statement: `D5/S3/VertexAlgebra/BcGhostBrstSupport.c_vanish_below`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/BcGhostBrstSupport.c_vanish_below` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If n<-B(g)-2, then c(-n)g=0. This is the actual annihilation branch: its even site 2(-n-2) exceeds every occupied site of g. In the n<=-2 branch, deletion also bounds the occupied set of c(-n)g by that of g.

**Theorem 1.3 (The actual expanded array has joint finite support).**

Lean statement: `D5/S3/VertexAlgebra/BcGhostBrstSupport.expanded_support_rectangle`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/BcGhostBrstSupport.expanded_support_rectangle` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The array is c(-n)normalPair(n+k,-k)g for n>=-1, and normalPair(n+k,-k)c(-n)g for n<=-2. Its support lies in the finite rectangle [-B(g)-2,2B(g)+4] times [-(3B(g)+8),3B(g)+8]. The low tail kills the right c(-n). The high tail applies the original BcGhostStressTails.normal_pair_high to every actual pair before applying c(-n). In shifted rows, occupied(c(-n)g) is contained in occupied(g), by actual deletion origin. The shifted occupied supremum is bounded by B(g); hence the shifted cutoff is at most B(g)+abs(n)+4, and therefore at most 3B(g)+8 on the retained outer interval. The shifted cutoff is not silently replaced by an unshifted assumption. This is joint support of the actual two-index array, not only separate finiteness of each row.

**Theorem 1.4 (The normally ordered ghost summand has a finite outer interval).**

Lean statement: `D5/S3/VertexAlgebra/BcGhostBrstSupport.normalGhost_support_interval`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/BcGhostBrstSupport.normalGhost_support_interval` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

N_n g=c(-n)L_n g for n>=-1, and L_n c(-n)g for n<=-2. Its support in n lies in [-B(g)-2,2B(g)+4]. N_n directly reuses BcGhostStressTails.outerNormalPair; no replacement operator or forwarding alias is defined. L_n is the actual statewise finite weighted normal-pair sum. A nonzero outer value requires a nonzero expanded entry, so the outer bound follows from the joint rectangle.

**Theorem 1.5 (Finite double-interval evaluation of the actual joint sum).**

Lean statement: `D5/S3/VertexAlgebra/BcGhostBrstSupport.expanded_joint_sum`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/BcGhostBrstSupport.expanded_joint_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The pointwise finsum over (n,k) of (n-k) expanded(g,(n,k)) is the double finite sum on the stated rectangle. normalGhost_joint_finsum identifies the outer finsum of N_n g with that same joint sum. The coefficient is n-k, not n+k. These are construction identities, consumed by the actual tensor charge evaluation; they are not independent novelty claims.

The construction uses the original public zero-annihilation proofs of BcGhostFockSupport, with their arbitrary-CommRing scope. No CAR, Virasoro, nilpotence or cohomology claim is implicit in these support and summation statements.

## References

- Truth anchor: `D5/S3/VertexAlgebra/BcGhostBrstSupport.c_vanish_below`
- Truth anchor: `D5/S3/VertexAlgebra/BcGhostBrstSupport.expanded_joint_sum`
- Truth anchor: `D5/S3/VertexAlgebra/BcGhostBrstSupport.expanded_support_rectangle`
- Truth anchor: `D5/S3/VertexAlgebra/BcGhostBrstSupport.normalGhost_support_interval`
- Truth anchor: `D5/S3/VertexAlgebra/BcGhostBrstSupport.occupied_annihilate_subset`
- Dependency: [D5/S3/VertexAlgebra/BcGhostFockSupport](BcGhostFockSupport.md)
- Dependency: [D5/S3/VertexAlgebra/BcGhostStressTails](BcGhostStressTails.md)
