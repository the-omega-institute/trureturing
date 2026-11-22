# Jacobi endpoint resolvent

## Abstract

The first Green column of a finite tridiagonal matrix factors along the path.

**Definition 1.1 (Tail index type).**

Lean statement: `D5/S3/Quantum/Matrix/JacobiEndpointResolvent.Tail`

*Formalization.* `D5/S3/Quantum/Matrix/JacobiEndpointResolvent.Tail` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a site i in Fin n, the tail contains precisely the sites j with i≤j.

**Definition 1.2 (First tail site).**

Lean statement: `D5/S3/Quantum/Matrix/JacobiEndpointResolvent.tailFirst`

*Formalization.* `D5/S3/Quantum/Matrix/JacobiEndpointResolvent.tailFirst` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The first site of the tail starting at i is i viewed in the tail index type.

**Definition 1.3 (Principal compression).**

Lean statement: `D5/S3/Quantum/Matrix/JacobiEndpointResolvent.tail`

*Formalization.* `D5/S3/Quantum/Matrix/JacobiEndpointResolvent.tail` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a square matrix A indexed by Fin n, tail(A,i) restricts both indices to the tail starting at i.

**Definition 1.4 (Shifted matrix).**

Lean statement: `D5/S3/Quantum/Matrix/JacobiEndpointResolvent.spectralShift`

*Formalization.* `D5/S3/Quantum/Matrix/JacobiEndpointResolvent.spectralShift` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a square matrix H and a scalar z over the same field, the shifted matrix is A=zI−H.

**Definition 1.5 (Tridiagonal support).**

Lean statement: `D5/S3/Quantum/Matrix/JacobiEndpointResolvent.IsTridiagonal`

*Formalization.* `D5/S3/Quantum/Matrix/JacobiEndpointResolvent.IsTridiagonal` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An entry vanishes whenever its row and column indices differ by more than one.

**Definition 1.6 (Lower bond).**

Lean statement: `D5/S3/Quantum/Matrix/JacobiEndpointResolvent.bond`

*Formalization.* `D5/S3/Quantum/Matrix/JacobiEndpointResolvent.bond` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The bond b_j is H(j+1,j) when j has a successor. The terminal site has bond value zero.

**Definition 1.7 (Intervening bond product).**

Lean statement: `D5/S3/Quantum/Matrix/JacobiEndpointResolvent.bondProduct`

*Formalization.* `D5/S3/Quantum/Matrix/JacobiEndpointResolvent.bondProduct` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The product at i ranges over j<i and is one at i=0.

**Definition 1.8 (Leading inverse tail entry).**

Lean statement: `D5/S3/Quantum/Matrix/JacobiEndpointResolvent.tailDiagonal`

*Formalization.* `D5/S3/Quantum/Matrix/JacobiEndpointResolvent.tailDiagonal` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a square matrix A and a site i, m_i(A) is the first diagonal entry of the nonsingular inverse of tail(A,i).

**Definition 1.9 (Inverse tail product).**

Lean statement: `D5/S3/Quantum/Matrix/JacobiEndpointResolvent.tailDiagonalProduct`

*Formalization.* `D5/S3/Quantum/Matrix/JacobiEndpointResolvent.tailDiagonalProduct` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The inverse tail product at i multiplies m_j(A) over all j≤i.

**Definition 1.10 (First inverse column).**

Lean statement: `D5/S3/Quantum/Matrix/JacobiEndpointResolvent.firstColumn`

*Formalization.* `D5/S3/Quantum/Matrix/JacobiEndpointResolvent.firstColumn` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

In positive dimension, g(A) is the column at site zero of the nonsingular inverse of A.

**Theorem 1.11 (Transfer across one bond).**

Lean statement: `D5/S3/Quantum/Matrix/JacobiEndpointResolvent.firstColumn_step`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/JacobiEndpointResolvent.firstColumn_step` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let H be tridiagonal over a field, with every principal tail of A=zI−H invertible. For consecutive sites p,i with i=p+1, g(A)_i=b_p g(A)_p m_i(A). On rows in the tail starting at i, the equation A g=e_0 has zero right-hand side. The prefix contributes only at the first row of that tail, where the shifted matrix entry is −b_p. Solving the tail equation gives the stated coordinate, including the case b_p=0.

**Theorem 1.12 (First Green column product).**

Lean statement: `D5/S3/Quantum/Matrix/JacobiEndpointResolvent.firstColumn_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/JacobiEndpointResolvent.firstColumn_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the same tridiagonal support and tail invertibility assumptions, for every site i in positive dimension, g(A)_i is the product of b_j over j<i times the product of m_j(A) over j≤i. At site zero the full tail is a reindexing of A. The successor step multiplies the earlier coordinate by the new bond and leading inverse entry.

**Theorem 1.13 (Leading inverse entry is nonzero).**

Lean statement: `D5/S3/Quantum/Matrix/JacobiEndpointResolvent.tailDiagonal_ne_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/JacobiEndpointResolvent.tailDiagonal_ne_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any square matrix A over a field with invertible principal tails, every m_i(A) is nonzero. If the leading entry of the inverse column were zero, the restriction to the next tail would solve a homogeneous equation and vanish by invertibility. The same conclusion holds at the terminal site because the tail has just one coordinate. In either case the column equation requires unit input at the first tail site.

**Theorem 1.14 (Vanishing detects an intervening zero bond).**

Lean statement: `D5/S3/Quantum/Matrix/JacobiEndpointResolvent.firstColumn_eq_zero_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/JacobiEndpointResolvent.firstColumn_eq_zero_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under tridiagonal support and tail invertibility, g(zI−H)_i vanishes if and only if some bond b_j with j<i vanishes. The inverse tail product has no zero factors. Since the scalars form a field, the remaining finite product is zero exactly when one of its factors is zero.

**Theorem 1.15 (Action of a supported perturbation).**

Lean statement: `D5/S3/Quantum/Matrix/JacobiEndpointResolvent.supported_mulVec_firstColumn`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/JacobiEndpointResolvent.supported_mulVec_firstColumn` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the same assumptions on H and z, let W have columns indexed by Fin n and arbitrary row type. For any natural k, suppose W has zero columns at all sites j with k≤j. Then W times the first inverse column of zI−H is the sum over j<k in Fin n of W's j-th column scaled by the intervening bond product and the inverse tail product at j. The finite filter also covers k=0 and k>n. This is the column identity used for the supported perturbation in the fixed-collar Petz recovery argument.

## References

- Truth anchor: `D5/S3/Quantum/Matrix/JacobiEndpointResolvent.IsTridiagonal`
- Truth anchor: `D5/S3/Quantum/Matrix/JacobiEndpointResolvent.Tail`
- Truth anchor: `D5/S3/Quantum/Matrix/JacobiEndpointResolvent.bond`
- Truth anchor: `D5/S3/Quantum/Matrix/JacobiEndpointResolvent.bondProduct`
- Truth anchor: `D5/S3/Quantum/Matrix/JacobiEndpointResolvent.firstColumn`
- Truth anchor: `D5/S3/Quantum/Matrix/JacobiEndpointResolvent.firstColumn_eq`
- Truth anchor: `D5/S3/Quantum/Matrix/JacobiEndpointResolvent.firstColumn_eq_zero_iff`
- Truth anchor: `D5/S3/Quantum/Matrix/JacobiEndpointResolvent.firstColumn_step`
- Truth anchor: `D5/S3/Quantum/Matrix/JacobiEndpointResolvent.spectralShift`
- Truth anchor: `D5/S3/Quantum/Matrix/JacobiEndpointResolvent.supported_mulVec_firstColumn`
- Truth anchor: `D5/S3/Quantum/Matrix/JacobiEndpointResolvent.tail`
- Truth anchor: `D5/S3/Quantum/Matrix/JacobiEndpointResolvent.tailDiagonal`
- Truth anchor: `D5/S3/Quantum/Matrix/JacobiEndpointResolvent.tailDiagonalProduct`
- Truth anchor: `D5/S3/Quantum/Matrix/JacobiEndpointResolvent.tailDiagonal_ne_zero`
- Truth anchor: `D5/S3/Quantum/Matrix/JacobiEndpointResolvent.tailFirst`
