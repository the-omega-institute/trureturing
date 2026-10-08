# Finite Scalar Trace Kernels

## Abstract

Finite scalar deletion histories have an exact congruence kernel and recover different source data at modulus two and at larger moduli.

N denotes the natural numbers. K is the product of LegalDigits with two profinite integers. LegalDigits consists of one-sided Boolean streams with no adjacent ones. U(p,j) is the natural value zero or one of digit j, and omega(p) is the entire address. For each positive modulus h, rho(h,p) projects both initial profinite coordinates modulo h. In Lean this existing projection is indexed by m=h-1, so every natural m represents exactly the positive modulus m+1. All arithmetic in a clause is in ZMod(h), and digit equalities mean actual Boolean equalities.

**Definition 1.1 (Successive deletion vectors).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/FiniteScalarTraceKernel.trajectory`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/FiniteScalarTraceKernel.trajectory` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For any commutative ring and input U, z(0)=z and z(j+1)=(z(j).second-z(j).first+U(j),z(j).first-U(j)). Equivalently z(j)=U(j)*(1,0)+M*z(j+1), with the existing Fibonacci map M(x,y)=(y,x+y). This recurrence is applied to each residue projection of the initial profinite vector, without imposing a relation between the address and that independent vector.

**Definition 1.2 (Finite scalar history).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/FiniteScalarTraceKernel.scalarTrace`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/FiniteScalarTraceKernel.scalarTrace` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

q(x,y)=2*x+3*y is the existing quantity function. c(h,p,j)=q*z(j) modulo h, and T(h,r,p) is the function on Fin(r+1) with values c(h,p,j). Thus time zero is included and the horizon r records r+1 readings. Only the initial residue and the digits used by the recurrence enter this trace. The theorem states this dependence explicitly.

**Theorem 1.3 (Exact kernels and short horizons).**

$$\left(\forall \left(m: N\right), \forall \left(r: N\right), \left(1 \leq r\right) \implies \left(\forall \left(p: K\right), \forall \left(s: K\right), \left(\operatorname{T}\left(m + 1, r, p\right) = \operatorname{T}\left(m + 1, r, s\right)\right) \iff \left(\left(\operatorname{rho}\left(m + 1, s\right) - \operatorname{rho}\left(m + 1, p\right) = \left(-3 \cdot \left(\operatorname{U}\left(s, 0\right) - \operatorname{U}\left(p, 0\right)\right), 2 \cdot \left(\operatorname{U}\left(s, 0\right) - \operatorname{U}\left(p, 0\right)\right)\right)\right) \land \left(\forall \left(j: N\right), \left(j + 2 \leq r\right) \implies \left(2 \cdot \left(\operatorname{U}\left(s, j\right) - \operatorname{U}\left(p, j\right)\right) + \operatorname{U}\left(s, j + 1\right) - \operatorname{U}\left(p, j + 1\right) = 0\right)\right)\right)\right)\right) \land \left(\forall \left(m: N\right), \forall \left(p: K\right), \forall \left(s: K\right), \left(\operatorname{T}\left(m + 1, 0, p\right) = \operatorname{T}\left(m + 1, 0, s\right)\right) \iff \left(\operatorname{q}\left(\operatorname{rho}\left(m + 1, p\right)\right) = \operatorname{q}\left(\operatorname{rho}\left(m + 1, s\right)\right)\right)\right) \land \left(\forall \left(r: N\right), \forall \left(p: K\right), \forall \left(s: K\right), \operatorname{T}\left(1, r, p\right) = \operatorname{T}\left(1, r, s\right)\right) \land \left(\forall \left(m: N\right), \forall \left(p: K\right), \operatorname{rho}\left(m + 1, p\right) = \left(2 \cdot \left(\operatorname{c}\left(m + 1, p, 0\right)\right) - 3 \cdot \left(\operatorname{c}\left(m + 1, p, 1\right) + \operatorname{U}\left(p, 0\right)\right), -\operatorname{c}\left(m + 1, p, 0\right) + 2 \cdot \left(\operatorname{c}\left(m + 1, p, 1\right) + \operatorname{U}\left(p, 0\right)\right)\right)\right) \land \left(\forall \left(m: N\right), \forall \left(r: N\right), \left(\left(3 \leq m + 1\right) \land \left(2 \leq r\right)\right) \implies \left(\forall \left(p: K\right), \forall \left(s: K\right), \left(\operatorname{T}\left(m + 1, r, p\right) = \operatorname{T}\left(m + 1, r, s\right)\right) \iff \left(\left(\forall \left(j: N\right), \left(j < r\right) \implies \left(\operatorname{U}\left(p, j\right) = \operatorname{U}\left(s, j\right)\right)\right) \land \left(\operatorname{rho}\left(m + 1, p\right) = \operatorname{rho}\left(m + 1, s\right)\right)\right)\right)\right) \land \left(\forall \left(r: N\right), \left(1 \leq r\right) \implies \left(\forall \left(p: K\right), \forall \left(s: K\right), \left(\operatorname{T}\left(2, r, p\right) = \operatorname{T}\left(2, r, s\right)\right) \iff \left(\left(\forall \left(j: N\right), \left(\left(1 \leq j\right) \land \left(j < r\right)\right) \implies \left(\operatorname{U}\left(p, j\right) = \operatorname{U}\left(s, j\right)\right)\right) \land \left(\operatorname{z}\left(2, p, 1\right) = \operatorname{z}\left(2, s, 1\right)\right)\right)\right)\right) \land \left(\forall \left(p: K\right), \operatorname{z}\left(2, p, 1\right) = \left(\operatorname{c}\left(2, p, 0\right) - \operatorname{c}\left(2, p, 1\right), \operatorname{c}\left(2, p, 1\right)\right)\right) \land \left(\forall \left(r: N\right), \left(1 \leq r\right) \implies \left(\forall \left(p: K\right), \forall \left(s: K\right), \left(\operatorname{T}\left(2, r, p\right) = \operatorname{T}\left(2, r, s\right)\right) \implies \left(\operatorname{rho}\left(2, s\right) - \operatorname{rho}\left(2, p\right) = \left(\operatorname{U}\left(s, 0\right) - \operatorname{U}\left(p, 0\right), 0\right)\right)\right)\right) \land \left(\forall \left(r: N\right), \left(1 \leq r\right) \implies \left(\forall \left(p: K\right), \forall \left(s: K\right), \left(\left(\operatorname{rho}\left(2, p\right) = \operatorname{rho}\left(2, s\right)\right) \land \left(\operatorname{T}\left(2, r, p\right) = \operatorname{T}\left(2, r, s\right)\right)\right) \implies \left(\operatorname{U}\left(p, 0\right) = \operatorname{U}\left(s, 0\right)\right)\right)\right) \land \left(\forall \left(m: N\right), \forall \left(r: N\right), \forall \left(p: K\right), \forall \left(s: K\right), \left(\left(\operatorname{omega}\left(p\right) = \operatorname{omega}\left(s\right)\right) \land \left(\operatorname{rho}\left(m + 1, p\right) = \operatorname{rho}\left(m + 1, s\right)\right)\right) \implies \left(\operatorname{T}\left(m + 1, r, p\right) = \operatorname{T}\left(m + 1, r, s\right)\right)\right) \land \left(\forall \left(m: N\right), \forall \left(r: N\right), \exists \left(p: K\right), \exists \left(s: K\right), \left(\operatorname{rho}\left(m + 1, p\right) = \operatorname{rho}\left(m + 1, s\right)\right) \land \left(\operatorname{T}\left(m + 1, r, p\right) = \operatorname{T}\left(m + 1, r, s\right)\right) \land \left(\operatorname{U}\left(p, r\right) \neq \operatorname{U}\left(s, r\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/FiniteScalarTraceKernel.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The first two scalar readings invert the row matrix [[2,3],[1,2]], whose determinant is one. Equal initial readings therefore require the initial-vector difference to equal (-3,2) times the first-digit difference. The scalar recurrence c(j)-c(j+1)-c(j+2)=2*U(j)+U(j+1) gives the residual conditions. Conversely, equal first two readings and equal forcing terms through j+2<=r propagate equality to every time at most r; no forcing equality is required beyond the horizon.

At horizon zero there is just one scalar comparison; at modulus one every trace is constant. At horizon one the stated inverse reconstructs the initial residue for the actual candidate first digit. For moduli at least three and horizons at least two, the legal adjacent pairs 00,01,10 have distinct codes 0,1,2. The residuals recover precisely the first r digits and the initial residue. Modulo two they recover digits 1 through r-1 and the vector after one deletion. For r=1 that digit interval is empty, and z(1)=(c(0)-c(1),c(1)). Changing the first digit requires the displayed initial-vector compensation; equal fixed initial residues force the first digits to agree. For every modulus and horizon, the all-zero address and the address with a single one at position r, both with zero initial profinite coordinates, give identical traces and different digits at position r. Thus the final observed time does not reveal that digit; at horizon zero this also demonstrates that the scalar reading does not determine the address.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/FiniteScalarTraceKernel.result`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/FiniteScalarTraceKernel.scalarTrace`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/FiniteScalarTraceKernel.trajectory`
- Dependency: [D5/S1/Digit/Infinite/SuccessorContinuity](../../../S1/Digit/Infinite/SuccessorContinuity.md)
- Dependency: [D5/S1/Dynamics/ProfiniteCharacter](../../../S1/Dynamics/ProfiniteCharacter.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/GraftAffineClosure](GraftAffineClosure.md)
