# Chain Schur Response

## Abstract

The chain Schur response has explicit linear coefficients and a quadratic error bound.

Let n be any natural number and m=n+1. The matrix H(m) has diagonal four and adjacent entries minus one. Put A=H(m) direct sum H(m). The two rows of B select the first vertex of the first and second chains, respectively. The hidden spatial matrix Gh is the hidden submatrix of G(n,k,b): it is diagonal with entry k everywhere except at the last vertex of the first chain, where the entry is k-b. All parameters k,b,s,u are real. Here u denotes the spatial perturbation parameter. Put E=u Gh-s I and Q=(A+E) inverse. An inverse is the nonsingular matrix inverse; Unit means invertibility. For the first identity alone, A and E may be arbitrary real square matrices on any finite decidable index type, including the empty type.

Define w=H(m) inverse applied to the first unit vector, z=1+sum of the squares of the coordinates of w, t=w(n), and eta=t squared/z. Thus the vector square is Euclidean. The recurrence d has d(0)=1, d(1)=4, and d(j+2)=4d(j+1)-d(j). Write P=diag(1,0). The matrix coefficients are Z=I+(B A inverse)(A inverse B transpose) and C=k I+(B A inverse) Gh (A inverse B transpose). The effective matrix T is the actual product Z inverse times C. Define S(s,u)=(1+ku-s)I-B Q B transpose and R(s,u)=-B A inverse E A inverse E Q B transpose. Matrix norms below are the maximum absolute row-sum norm, also for rectangular matrices. Let F=norm(B) norm(A inverse) squared norm(B transpose) and L=2 norm(B) norm(A inverse) cubed norm(B transpose). These constants depend on n, and not on s or u.

**Theorem 1.1 (The iterated inverse identity).**

$${Unit\left(A\right)\land Unit\left(A+E\right)}\implies {Q = A^{-1}-A^{-1}\cdot E\cdot A^{-1}+A^{-1}\cdot E\cdot A^{-1}\cdot E\cdot Q}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenResource/ChainSchurResponse.inverse_first_order` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The inverse-difference identity gives Q=A inverse-A inverse E Q. Substitute this same expression for the last Q on the right once and distribute in the original matrix order. The result is exact for every invertible A and A+E.

**Theorem 1.2 (A positive common coefficient).**

$$0 < z$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenResource/ChainSchurResponse.z_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every coordinate square is nonnegative, and z is their sum plus one.

**Theorem 1.3 (The endpoint transfer).**

$$t = \frac{1}{d\left(m\right)}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenResource/ChainSchurResponse.endpoint_formula` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The first inverse column of the chain is the reversed recurrence divided by d(m). Its last numerator is d(0)=1.

**Theorem 1.4 (The spectral coefficient).**

$$Z = z\cdot I$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenResource/ChainSchurResponse.Z_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The columns of A inverse B transpose are copies of w supported on separate chains. Symmetry therefore makes their Gram matrix the sum of the coordinate squares times the identity. Adding the visible identity gives Z.

**Theorem 1.5 (The spatial coefficient).**

$$C = k\cdot z\cdot I-b\cdot t^{2}\cdot P$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenResource/ChainSchurResponse.C_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The constant spatial weight contributes k times the same Gram matrix. The exceptional endpoint subtracts b times t squared from the first visible diagonal entry. Adding the visible k I gives the displayed coefficient.

**Theorem 1.6 (The normalized effective matrix).**

$$T = diag\left(k-b\cdot eta, k\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenResource/ChainSchurResponse.effective_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Since z is positive, the inverse of Z is z inverse times the identity. Multiplication by C divides the endpoint correction by z.

**Theorem 1.7 (The exact Schur expansion).**

$${Unit\left(A+E\right)}\implies {S\left(s, u\right) = S\left(0, 0\right)-s\cdot Z+u\cdot C+R\left(s, u\right)}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenResource/ChainSchurResponse.response_expansion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The hidden mass matrix is positive definite. Insert the iterated inverse identity into S and collect the two linear terms. The Schur subtraction gives R its negative sign. Only invertibility of A+E is assumed here.

**Theorem 1.8 (The remainder product bound).**

$$\Vert R\left(s, u\right)\Vert  \le F\cdot \Vert Q\Vert \cdot \Vert E\Vert ^{2}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenResource/ChainSchurResponse.remainder_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Apply submultiplicativity to every matrix factor. The two copies of E produce its squared norm. This bound holds for all real parameters, even when the nonsingular inverse is zero.

**Theorem 1.9 (A bounded inverse).**

$${\Vert Q\Vert  \le M}\implies {\Vert R\left(s, u\right)\Vert  \le F\cdot M\cdot \Vert E\Vert ^{2}}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenResource/ChainSchurResponse.remainder_bound_of_inverse_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any real M bounding the inverse norm, replace that norm in the product estimate by M. All the other factors are nonnegative.

**Theorem 1.10 (A fixed quadratic error constant).**

$${Unit\left(A+E\right)\land \Vert A^{-1}\Vert \cdot \Vert E\Vert  \le \frac{1}{2}}\implies {S\left(s, u\right) = S\left(0, 0\right)-s\cdot Z+u\cdot C+R\left(s, u\right)\land \Vert R\left(s, u\right)\Vert  \le L\cdot \Vert E\Vert ^{2}}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenResource/ChainSchurResponse.response_first_order` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

From Q=A inverse-A inverse E Q and the triangle inequality, norm(Q) is at most norm(A inverse) plus norm(A inverse) norm(E) norm(Q). The smallness condition lets us move the last term to the left and bound norm(Q) by twice norm(A inverse). Substitution in the remainder estimate gives L. This is an exact expansion with a quantitative bound, proved without taking a derivative.

## References

- Truth anchor: `D5/S3/Arith/GoldenResource/ChainSchurResponse.C_eq`
- Truth anchor: `D5/S3/Arith/GoldenResource/ChainSchurResponse.Z_eq`
- Truth anchor: `D5/S3/Arith/GoldenResource/ChainSchurResponse.effective_eq`
- Truth anchor: `D5/S3/Arith/GoldenResource/ChainSchurResponse.endpoint_formula`
- Truth anchor: `D5/S3/Arith/GoldenResource/ChainSchurResponse.inverse_first_order`
- Truth anchor: `D5/S3/Arith/GoldenResource/ChainSchurResponse.remainder_bound`
- Truth anchor: `D5/S3/Arith/GoldenResource/ChainSchurResponse.remainder_bound_of_inverse_bound`
- Truth anchor: `D5/S3/Arith/GoldenResource/ChainSchurResponse.response_expansion`
- Truth anchor: `D5/S3/Arith/GoldenResource/ChainSchurResponse.response_first_order`
- Truth anchor: `D5/S3/Arith/GoldenResource/ChainSchurResponse.z_pos`
- Dependency: [D5/S3/Arith/GoldenResource/ChainBlockPencil](ChainBlockPencil.md)
