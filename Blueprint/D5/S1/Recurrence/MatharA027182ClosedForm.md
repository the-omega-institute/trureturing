# Closed form of the A027182 self-convolution

## Abstract

The A027182 self-convolution has a closed form in central binomial coefficients and powers of two.

**Theorem 1.1 (All-index closed form).**

Lean statement: `D5/S1/Recurrence/MatharA027182ClosedForm.closed_form`

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/MatharA027182ClosedForm.closed_form` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let T(n,k)=t(n,k)−4 with t(n,k)=C(n+2,k+1)+C(n+1,k)+C(n+1,k+1)+C(n,k), let g_n(x) be the sum of T(n,k)x^k over 0≤k≤n, and let a(n) be the coefficient of x^n in g_n(x)^2. For every natural n, a(n)=4C(2n+4,n+2)+4C(2n+2,n+1)+C(2n,n)−72·2^n+16n+40; at n=0 this gives a(0)=1.

Since T(n,n−k)=T(n,k), the middle coefficient of the square is the sum of T(n,k)^2 over 0≤k≤n. Writing T(n,k)=2A_k+B_k−4 with A_k=C(n+2,k+1) and B_k=C(n,k), expand the square and evaluate the five sums by Vandermonde's identity and the binomial theorem: the sum of A_k^2 is C(2n+4,n+2)−2, the sum of A_kB_k is C(2n+2,n+1), the sum of B_k^2 is C(2n,n), the sum of A_k is 4·2^n−2 and the sum of B_k is 2^n.

## References

- Truth anchor: `D5/S1/Recurrence/MatharA027182ClosedForm.closed_form`
- Dependency: [D5/S1/Recurrence/MatharA027182SelfConvolution](MatharA027182SelfConvolution.md)
