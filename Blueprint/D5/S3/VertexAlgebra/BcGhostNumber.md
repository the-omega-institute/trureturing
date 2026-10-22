# Integral Ghost Number On The Original Fock Space

## Abstract

The original infinite algebraic bc Fock carrier has integral signed occupation and exact ghost-mode degrees.

Let K be any commutative ring, including rings of positive characteristic and the zero ring. The carrier is exactly BcGhostFockSupport.Fock(K)=Finset(N) ->0 K. For a finite subset S, degree(S) is the integer number of odd sites minus the integer number of even sites. Both cardinalities are cast into Z before subtraction. Thus the degree can be negative; it is not truncated natural subtraction or the unsigned exterior degree. J is the diagonal K-linear endomorphism with J(single(S,a))=cast_K(degree(S)) times single(S,a). The original vacuum is single(empty,1), its integer degree is zero, and J kills it. The eigenvalue is mapped into K, so an integer grading label need not be recoverable from that scalar in positive characteristic.

The original even sites are b creators and odd sites are c creators. Inserting an absent even site lowers the degree by one, while inserting an absent odd site raises it by one. Erasing a present site makes the opposite change. Occupied-site creation and absent-site annihilation are zero. These statements are proved for actual insertion and erasure of arbitrary finite subsets, with the original Koszul signs retained. The proofs then use Finsupp linear induction to handle every finite superposition, rather than assuming a homogeneous input state.

**Theorem 1.1 (Every original b mode has degree minus one).**

Lean statement: `D5/S3/VertexAlgebra/BcGhostNumber.J_b_commutator`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/BcGhostNumber.J_b_commutator` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every commutative ring K and every integer m, J times b(m) minus b(m) times J equals minus b(m) as endomorphisms of the entire original Fock(K). For m<=-2 the even site is 2*(-m-2).toNat and b inserts it. Otherwise b erases the odd site 2*(m+1).toNat+1. Both branches lower ghost number by one. There is no field, nontriviality, rank, Virasoro or assumed-grading premise.

**Theorem 1.2 (Every original c mode has degree one).**

Lean statement: `D5/S3/VertexAlgebra/BcGhostNumber.J_c_commutator`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/BcGhostNumber.J_c_commutator` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every commutative ring K and every integer n, J times c(n) minus c(n) times J equals c(n) on all original Fock(K). For n<=1 the odd site is 2*(1-n).toNat+1 and c inserts it. Otherwise c erases the even site 2*(n-2).toNat. Both branches raise ghost number by one, with precisely the same hypotheses and full scope as the b law.

**Theorem 1.3 (The original normally ordered stress is neutral).**

Lean statement: `D5/S3/VertexAlgebra/BcGhostNumber.J_L_commutator`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/BcGhostNumber.J_L_commutator` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every commutative ring K and every integer m, J times L(m) minus L(m) times J equals zero on all original Fock(K). The actual normal pair is b(p) composed with c(q) for p<=-2 and minus c(q) composed with b(p) otherwise. Both orders have degree zero. The actual stress sum uses coefficient cast_K(m-k) and indices p=m+k, q=-k. For each state v, the supplied L_interval_sum theorem evaluates L on v and on J(v) in an interval bounded by the maximum of their two supplied cutoffs. The interval depends on the input; there is no fixed global truncation and no support or CAR reproof. This neutral-stress result is consumed by the original tensor BRST ghost-number proof.

Signed occupation and its propagation through the actual statewise finite sums are the mathematical target. Diagonal basis evaluation, scalar rearrangements and tensor lifts are consumed helpers, not separate new mathematical results. This source-only unit supplies no cohomology computation, no-ghost theorem, physical spectrum or string/AdS result.

## References

- Truth anchor: `D5/S3/VertexAlgebra/BcGhostNumber.J_L_commutator`
- Truth anchor: `D5/S3/VertexAlgebra/BcGhostNumber.J_b_commutator`
- Truth anchor: `D5/S3/VertexAlgebra/BcGhostNumber.J_c_commutator`
- Dependency: [D5/S3/VertexAlgebra/BcGhostFockSupport](BcGhostFockSupport.md)
