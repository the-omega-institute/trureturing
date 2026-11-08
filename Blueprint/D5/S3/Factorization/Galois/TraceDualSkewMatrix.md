# Trace-dual Galois Skew Matrices

## Abstract

Trace-dual coordinates for an arbitrary semilinear Galois algebra.

Let F/k be a finite Galois extension and let A be any unital F-algebra, with a compatible k-algebra structure and a multiplicative semilinear action of Gamma = Gal(F/k). The universes of k, F, A and the basis index are independent. The algebra A may be noncommutative or trivial, and need not be finite dimensional. No inverse of the group order or descent hypothesis is assumed.

**Definition 1.1 (Fixed algebra and right module).**

Lean statement: `D5/S3/Factorization/Galois/TraceDualSkewMatrix.invariants`

*Formalization.* `D5/S3/Factorization/Galois/TraceDualSkewMatrix.invariants` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The k-subalgebra C consists of the elements fixed by every g in Gamma. The right C-module A is implemented as a left module over C-op: the scalar op(c) sends x to x*c. The action commutes with k-scalars because it is semilinear over the given Galois action on F.

**Theorem 1.2 (Canonical skew action).**

Lean statement: `D5/S3/Factorization/Galois/TraceDualSkewMatrix.Phi_apply`

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Galois/TraceDualSkewMatrix.Phi_apply` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Phi(r)(x) = sum_g r.coeff(g)*(g acting on x). Coefficients act by left multiplication and group elements act by the supplied action. Mathlib's liftNCAlgHom constructs the algebra homomorphism. Its forward map contains no choice of a field basis.

**Definition 1.3 (Trace-dual invariant coordinates).**

Lean statement: `D5/S3/Factorization/Galois/TraceDualSkewMatrix.d`

*Formalization.* `D5/S3/Factorization/Galois/TraceDualSkewMatrix.d` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Choose a finite k-basis b of F and its trace-dual basis. Write u_i for the image of b_i in A and v_i for the image of its trace-dual element. The coordinate d_i(x) is sum_g g acting on (v_i*x), as an element of C. Left translation permutes Gamma, proving fixedness, and d_i(x*c) = d_i(x)*c proves right C-linearity.

**Theorem 1.4 (Coordinate delta identity).**

Lean statement: `D5/S3/Factorization/Galois/TraceDualSkewMatrix.d_basis_mul`

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Galois/TraceDualSkewMatrix.d_basis_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every c in C, d_j(u_i*c) equals c when j=i and zero otherwise. This follows from the trace-dual pairing and the expression of Galois trace as a sum of automorphisms.

**Theorem 1.5 (Reconstruction).**

Lean statement: `D5/S3/Factorization/Galois/TraceDualSkewMatrix.reconstruct`

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Galois/TraceDualSkewMatrix.reconstruct` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every x in A satisfies sum_i u_i*d_i(x) = x. Over F, the matrices P[g,i] = g(b_i) and Q[i,g] = g(traceDual_i) satisfy QP=1 by the trace pairing. Their equal finite dimensions give PQ=1 by the existing field matrix inverse theorem. The resulting automorphism orthogonality transports through F to A. Stable finiteness is used only over the field F.

**Definition 1.6 (Actual invariant module coordinates).**

Lean statement: `D5/S3/Factorization/Galois/TraceDualSkewMatrix.coordinates`

*Formalization.* `D5/S3/Factorization/Galois/TraceDualSkewMatrix.coordinates` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The maps x mapped to (d_i(x)) and c mapped to sum_i u_i*c_i are inverse C-op-linear maps between A and the functions I to C. Reconstruction and the coordinate delta identity prove the two inverse laws.

**Definition 1.7 (Genuine right invariant basis).**

Lean statement: `D5/S3/Factorization/Galois/TraceDualSkewMatrix.rightBasis`

*Formalization.* `D5/S3/Factorization/Galois/TraceDualSkewMatrix.rightBasis` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Pointwise op turns the coordinate functions into functions I to C-op. Mathlib's Basis.ofEquivFun then gives a genuine C-op-basis of A, whose ith vector is u_i. The basis is constructed rather than assumed.

**Theorem 1.8 (Explicit inverse coefficients).**

Lean statement: `D5/S3/Factorization/Galois/TraceDualSkewMatrix.Psi_coeff`

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Galois/TraceDualSkewMatrix.Psi_coeff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Psi(T).coeff(g) = sum_i T(u_i)*(g acting on v_i). This order of multiplication is retained when A is noncommutative.

**Theorem 1.9 (Endomorphism inverse law).**

Lean statement: `D5/S3/Factorization/Galois/TraceDualSkewMatrix.Phi_Psi`

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Galois/TraceDualSkewMatrix.Phi_Psi` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Phi(Psi(T)) = T for every endomorphism of the right C-module A. The coefficient formula, finite sum interchange and right C-linearity reduce this law to invariant-coordinate reconstruction.

**Theorem 1.10 (Skew coefficient inverse law).**

Lean statement: `D5/S3/Factorization/Galois/TraceDualSkewMatrix.Psi_Phi`

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Galois/TraceDualSkewMatrix.Psi_Phi` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Psi(Phi(r)) = r for every element of the skew monoid algebra. At each group coefficient, finite sum interchange and the transported automorphism orthogonality give the original coefficient.

**Definition 1.11 (Canonical skew and endomorphism equivalence).**

Lean statement: `D5/S3/Factorization/Galois/TraceDualSkewMatrix.skewEndEquiv`

*Formalization.* `D5/S3/Factorization/Galois/TraceDualSkewMatrix.skewEndEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The canonical k-algebra equivalence identifies SkewMonoidAlgebra A Gamma with Module.End C-op A. A field basis supplies its inverse proof; the forward homomorphism remains exactly Phi. The theorem skewEndEquiv_symm_coeff gives its inverse coefficient formula using any finite k-basis of F.

**Theorem 1.12 (Ordinary matrix entries).**

Lean statement: `D5/S3/Factorization/Galois/TraceDualSkewMatrix.endMatrixEquiv_apply`

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Galois/TraceDualSkewMatrix.endMatrixEquiv_apply` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The endomorphism T has matrix entry (j,i) equal to d_j(T(u_i)). Conjugation by the actual invariant coordinates and Mathlib's endomorphism matrix equivalence reduce to matrices over End C-op C. The existing moduleEndSelfOp equivalence converts those entries to C itself, so the matrix coefficient ring is C.

**Definition 1.13 (Basis-dependent matrix presentation).**

Lean statement: `D5/S3/Factorization/Galois/TraceDualSkewMatrix.skewMatrixEquiv`

*Formalization.* `D5/S3/Factorization/Galois/TraceDualSkewMatrix.skewMatrixEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For the chosen field basis b, the skew algebra is k-algebra equivalent to ordinary Matrix I I C. This matrix presentation depends on b. It makes no normalized-rank, inner-action, Schur, Frobenius-bound or literature-novelty assertion.

**Theorem 1.14 (Skew matrix coefficient formula).**

Lean statement: `D5/S3/Factorization/Galois/TraceDualSkewMatrix.skewMatrixEquiv_apply`

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Galois/TraceDualSkewMatrix.skewMatrixEquiv_apply` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The (j,i) entry of the matrix of r is d_j(sum_g r.coeff(g)*(g acting on u_i)).

## References

- Truth anchor: `D5/S3/Factorization/Galois/TraceDualSkewMatrix.Phi_Psi`
- Truth anchor: `D5/S3/Factorization/Galois/TraceDualSkewMatrix.Phi_apply`
- Truth anchor: `D5/S3/Factorization/Galois/TraceDualSkewMatrix.Psi_Phi`
- Truth anchor: `D5/S3/Factorization/Galois/TraceDualSkewMatrix.Psi_coeff`
- Truth anchor: `D5/S3/Factorization/Galois/TraceDualSkewMatrix.coordinates`
- Truth anchor: `D5/S3/Factorization/Galois/TraceDualSkewMatrix.d`
- Truth anchor: `D5/S3/Factorization/Galois/TraceDualSkewMatrix.d_basis_mul`
- Truth anchor: `D5/S3/Factorization/Galois/TraceDualSkewMatrix.endMatrixEquiv_apply`
- Truth anchor: `D5/S3/Factorization/Galois/TraceDualSkewMatrix.invariants`
- Truth anchor: `D5/S3/Factorization/Galois/TraceDualSkewMatrix.reconstruct`
- Truth anchor: `D5/S3/Factorization/Galois/TraceDualSkewMatrix.rightBasis`
- Truth anchor: `D5/S3/Factorization/Galois/TraceDualSkewMatrix.skewEndEquiv`
- Truth anchor: `D5/S3/Factorization/Galois/TraceDualSkewMatrix.skewMatrixEquiv`
- Truth anchor: `D5/S3/Factorization/Galois/TraceDualSkewMatrix.skewMatrixEquiv_apply`
