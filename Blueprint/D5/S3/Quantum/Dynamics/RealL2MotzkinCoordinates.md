# Real Half-Line Motzkin Coordinates

## Abstract

Every coordinate of every real half-line iterate is an alternating-sign evaluation of the boundary-weighted Motzkin polynomial.

**Theorem 1.1 (The coordinate correspondence at every natural order and height).**

$$\forall k,j \in \mathbb{N}, (K_{\infty}^{k} e_{0})_{j} = (-1)^{j} M_{k,j}(3,3).$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/RealL2MotzkinCoordinates.iterate_coordinates` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let H be the complete real Hilbert space of square-summable sequences indexed by the natural numbers. Write e_j for its coordinate vectors and S for its unilateral shift, with S e_j = e_(j+1). Set K_infinity = 3I-S-S*, using the Hilbert adjoint of this actual shift. The endpoint is e_0. Natural coordinate j corresponds to coordinate j+1 on the positive-integer half-line.

Let M_(k,j)(t,s) be the existing integer-coefficient Motzkin polynomial: up and down steps have weight one, and horizontal steps have weight s at height zero and t at positive height. The expression M_(k,j)(3,3) means the ring-homomorphic evaluation that sends every integer coefficient to its real cast and both variables to the real number three.

Pairing S with coordinate vectors shows that (S* x)_j = x_(j+1). Thus the zeroth coordinate of K_infinity x is 3x_0-x_1; at positive coordinate j+1 it is 3x_(j+1)-x_j-x_(j+2). Induction on k matches these identities with the last-step Motzkin recurrence. The factor (-1)^j turns both negative neighbor terms into the two positive path contributions.

At k=0 the equality is the endpoint coordinate identity, including j=0 and every positive j. The equality also includes every j>k, where the Motzkin polynomial and the iterate coordinate vanish. No finite truncation or bound on the power or coordinate is used.

## References

- Truth anchor: `D5/S3/Quantum/Dynamics/RealL2MotzkinCoordinates.iterate_coordinates`
- Dependency: [D5/S3/Combinatorics/MotzkinHankel/CiglerMotzkinHankelDefs](../../Combinatorics/MotzkinHankel/CiglerMotzkinHankelDefs.md)
- Dependency: [D5/S3/Quantum/Dynamics/RealL2FirstReturnMoments](RealL2FirstReturnMoments.md)
