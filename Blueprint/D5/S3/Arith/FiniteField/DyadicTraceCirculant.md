# Dyadic Trace-Circulant Determinant

## Abstract

A unit dyadic translation circulant has a nonsingular consecutive half-size section over the binary field.

**Theorem 1.1 (The consecutive half-size determinant equals one).**

$$\forall k, t \in \mathbb{N}, k\geq2 \land \operatorname{gcd}(t, 2^{k}-1)=1 \Rightarrow \operatorname{det}(A(k, t))=1.$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FiniteField/DyadicTraceCirculant.dyadic_trace_circulant_det_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Put N = 2^k - 1 and M = 2^(k - 1). Write A(k,t) for dyadicTraceCirculant k t. Its rows and columns are the consecutive residues 0 through M - 1. Its entry at x,y is the sum in F_2 of the indicators y - x = t 2^i in Z/NZ, for 0 <= i < k. Both endpoints are first mapped to Z/NZ and then subtracted, including when y < x. The parameter t is coprime to N.

Translations act through the cyclic group Z/NZ. In the field K of size 2^k, Frobenius sends u to u squared and permutes the dyadic translation shifts. The finite-field trace expands as the sum of these Frobenius powers. Consequently the spectrum is exactly the units u with Tr(u^t) = 1. The coprime power map is a permutation of the units. Surjectivity of the F_2-linear trace gives equal fibers of size M; zero is absent from the trace-one fiber. The unit u = 1 is retained whenever its trace is one.

The kernel is the sum over this spectrum of u^x times the inverse of u^y. Insert the trace as its binary indicator and interchange the two finite sums. Orthogonality of powers summed over the multiplicative group of K recovers precisely the directed displacement y - x. The usual nonzero scalar is -1, which equals one in characteristic two. These trace and root-sum identities are classical finite-field Fourier algebra, as in Lidl and Niederreiter, Finite Fields.

Reversing the consecutive columns gives moments with distinct nonzero nodes u and weights equal to the inverse of u^(M - 1). The resulting matrix is the zero-shift square finite Prony Hankel section. Its nonsingularity is supplied by finite_prony_square_hankel_det_ne_zero in FinitePronyMatrixPencil, using the established Vandermonde factorization. Undoing the column permutation and descending along F_2 into K gives a nonzero determinant in F_2, hence determinant one.

This conclusion requires a unit t and the consecutive section. It asserts no arbitrary half-size subset result and no idempotence of the compressed matrix. For Circle C3.1 it is an auxiliary determinant result: a full cycle cover does not specify an all-physical-label cycle or the required geometric inventory. That construction remains open.

## References

- Truth anchor: `D5/S3/Arith/FiniteField/DyadicTraceCirculant.dyadic_trace_circulant_det_one`
- Dependency: [D5/S3/Analytic/GoldenTomography/FinitePronyMatrixPencil](../../Analytic/GoldenTomography/FinitePronyMatrixPencil.md)
