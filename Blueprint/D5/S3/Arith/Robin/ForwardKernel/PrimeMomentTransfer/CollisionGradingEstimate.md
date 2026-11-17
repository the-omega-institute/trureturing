# Collision grading estimates

## Abstract

Degree-sensitive estimates for arbitrary-order quadratic collisions.

Write s=sqrt(H*L) and rho=sqrt(L/H). A collision configuration with q unretained blocks, r retained blocks and excess degree d has total order 2*q+r+d and coefficient degree q+d. The identities s^2=H*L and s*rho=L identify its length and coefficient scales exactly. Coefficient factors are bounded uniformly in terms of the total order.

**Theorem 1.1 (The multiplicity grading).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/CollisionGradingEstimate.collision_degree_decomposition`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/CollisionGradingEstimate.collision_degree_decomposition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a finite block type B, multiplicities m:B->Nat, and retained subset S, suppose m(b)>=1 on S and m(b)>=2 outside S. Then the total multiplicity k=sum_b m(b) equals 2*card(complement S)+card(S)+delta, where delta=sum_(b in S)(m(b)-1)+sum_(b outside S)(m(b)-2). This follows by splitting the total sum into retained and unretained blocks.

**Theorem 1.2 (Grading the actual block multiplicities).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/CollisionGradingEstimate.collision_partition_grading_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/CollisionGradingEstimate.collision_partition_grading_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the same multiplicity assumptions and C>=1,H>0,L>=0, writing q=card(complement S), r=card(S) and k=sum_b m(b), the quantity ((C+1)*L)^(k-card(B))*C^(q+1)*H^q*s^r is at most (C+1)^(k+1)*s^k*rho^delta. Moreover delta=0 if and only if every retained block has multiplicity one and every unretained block has multiplicity two. Nonnegativity of each summand in delta establishes the characterization; the decomposition gives k-card(B)=q+delta.

**Theorem 1.3 (The degree-sensitive scale bound).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/CollisionGradingEstimate.collision_grading_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/CollisionGradingEstimate.collision_grading_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For real C,H,L with C>=1, H>0 and L>=0, and all natural q,r,d, ((C+1)*L)^(q+d)*C^(q+1)*H^q*s^r is at most (C+1)^(2*q+r+d+1)*s^(2*q+r+d)*rho^d. Indeed L^(q+d)*H^q*s^r equals s^(2*q+r+d)*rho^d. The remaining coefficient factor (C+1)^(q+d)*C^(q+1) is at most (C+1)^(2*q+r+d+1), since C>=1 and r>=0.

**Theorem 1.4 (Positive degrees gain the scale ratio).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/CollisionGradingEstimate.collision_positive_grading_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/CollisionGradingEstimate.collision_positive_grading_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For real C,H,L with C>=1 and H>=L>=1, and all natural q,r,d with d>=1, ((C+1)*L)^(q+d)*C^(q+1)*H^q*s^r is at most (C+1)^(2*q+r+d+1)*s^(2*q+r+d)*rho. This follows from the degree-sensitive bound and 0<=rho<=1, which gives rho^d<=rho.

**Theorem 1.5 (A lost free component gains inverse length).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/CollisionGradingEstimate.collision_free_component_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/CollisionGradingEstimate.collision_free_component_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For real C,H,L with C>=1, H>0 and L>=0, and all natural n,r, ((C+1)*L)^(n+1)*C^(n+1)*H^n*s^r is at most (C+1)^(2*(n+1)+r+1)*s^(2*(n+1)+r)/H. Multiplication by positive H restores the zero-degree scale with q=n+1; increasing C^(n+1) to C^(n+2) allows application of the degree-sensitive bound.

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/CollisionGradingEstimate.collision_degree_decomposition`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/CollisionGradingEstimate.collision_free_component_bound`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/CollisionGradingEstimate.collision_grading_bound`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/CollisionGradingEstimate.collision_partition_grading_bound`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/CollisionGradingEstimate.collision_positive_grading_bound`
