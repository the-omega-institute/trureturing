# Assignment moment reindexing

## Abstract

Finite assignment moments under enumeration.

Let D and T be finite types, A a commutative real algebra, ell a real linear functional on A, and Y a family indexed by D. Enumerating T preserves both the scalar weight product and the algebra product in each injective assignment moment.

**Theorem 1.1 (Distinct-index moment under any enumeration).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/AssignmentMomentReindex.assignment_moment_reindex`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/AssignmentMomentReindex.assignment_moment_reindex` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any finite type T and equivalence e from T to Fin n, the injective-assignment sum of the product of scalar weights times ell of the product of Y factors equals the ordered distinct-index moment of the weights composed with e.inverse. Both scalar and algebra products are unchanged by the enumeration.

**Theorem 1.2 (Enumeration of retained assignments).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/AssignmentMomentReindex.retained_assignment_reindex`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/AssignmentMomentReindex.retained_assignment_reindex` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite subset S of a label type B and scalar weights w indexed by B, the sum over injective maps x from S to D of the product of w(t,x(t)) over t in S times ell of the product of Y(x(t)) over t in S equals the ordered distinct-index moment of the weights w((equivFin(S)).inverse(i)), indexed by Fin(card(S)). The equality is finite reindexing by equivFin.

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/AssignmentMomentReindex.assignment_moment_reindex`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/AssignmentMomentReindex.retained_assignment_reindex`
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/QuadraticMomentDefs](QuadraticMomentDefs.md)
