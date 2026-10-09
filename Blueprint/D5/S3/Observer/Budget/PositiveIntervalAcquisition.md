# Positive Forward Sensing on Arbitrary Intervals

## Abstract

Every nonempty finite low-digit interval can be recovered by forward sensing with logarithmically many subsequent reads and strictly positive waits.

Let p>=2 and P>0 be natural numbers, H=clog(2,P), and B=H(P-1). Protocol(H) is the binary query tree with early stopping leaves and a waiting increment at each query. Its execution returns the recovered low residue and final elapsed count. A retained first digit b together with a low residue r describes the initial source bP+r modulo pP.

The physical digit at elapsed count n is floor(((bP+r+n) mod pP)/P). Decoded(p,P,b,n,r) is zero when this digit equals (b+floor(n/P)) mod p, and one otherwise. Cut(P,n,r) is zero for r<P-(n mod P), and one otherwise. Thus Decoded uses only the physical answer, retained digit, and elapsed count.

Acquire(P,d,l,u,n) stops at l when the remaining depth d is zero or u<=l+1. Otherwise it splits at m=floor((l+u)/2), waits the strictly positive forward distance to phase P-m, and continues on [l,m) or [m,u). The list Waits records precisely the successive waiting increments on an execution. T=Acquire(P,H,0,P,0) is independent of b. Recovery of r also recovers bP+r and the final current residue (bP+r+n_final) mod pP. This tree description counts subsequent reads; the initial read acquiring b contributes one further read.

**Lemma 1.1 (Endpoint alignment gives a strictly positive midpoint wait).**

$$\forall P : \mathbb{N}, \forall l : \mathbb{N}, \forall u : \mathbb{N}, \forall n : \mathbb{N}, \left(l < u \land u \leq P \land l + 1 < u \land \left(\operatorname{mod}\left(n, P\right) = \operatorname{mod}\left(P - l, P\right) \lor \operatorname{mod}\left(n, P\right) = \operatorname{mod}\left(P - u, P\right)\right)\right) \implies \left(l < \operatorname{div}\left(l + u, 2\right) \land \operatorname{div}\left(l + u, 2\right) < u \land 0 < \operatorname{waitTo}\left(P, n, P - \operatorname{div}\left(l + u, 2\right)\right) \land \operatorname{waitTo}\left(P, n, P - \operatorname{div}\left(l + u, 2\right)\right) < P \land \operatorname{mod}\left(n + \operatorname{waitTo}\left(P, n, P - \operatorname{div}\left(l + u, 2\right)\right), P\right) = P - \operatorname{div}\left(l + u, 2\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Budget/PositiveIntervalAcquisition.interval_wait` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For l<u<=P and l+1<u, put m=floor((l+u)/2). If n modulo P equals (P-l) modulo P or (P-u) modulo P, then m is strictly between the endpoints. The positive forward distance w to P-m satisfies 0<w<P and (n+w) modulo P equals P-m.

**Theorem 1.2 (Shared interval tree, physical digit law, costs, and attained depth).**

$$\forall p : \mathbb{N}, \forall P : \mathbb{N}, \left(2 \leq p \land 0 < P\right) \implies \exists T : \operatorname{Protocol}\left(\operatorname{clog}\left(2, P\right)\right), \left(T = \operatorname{Acquire}\left(P, \operatorname{clog}\left(2, P\right), 0, P, 0\right) \land \left(\forall b : \mathbb{N}, \forall n : \mathbb{N}, \forall r : \mathbb{N}, r < P \implies \left(\operatorname{div}\left(\operatorname{mod}\left(b \times P + r + n, p \times P\right), P\right) = \operatorname{mod}\left(b + \operatorname{div}\left(n, P\right) + \operatorname{Cut}\left(P, n, r\right), p\right) \land \operatorname{Decoded}\left(p, P, b, n, r\right) = \operatorname{Cut}\left(P, n, r\right)\right)\right) \land \left(\forall b : \mathbb{N}, \forall r : \mathbb{N}, r < P \implies \left(\operatorname{Answer}\left(\operatorname{Decoded}\left(p, P, b\right), T, 0, r\right) = r \land \operatorname{Time}\left(\operatorname{Decoded}\left(p, P, b\right), T, 0, r\right) \leq \operatorname{clog}\left(2, P\right) \times \left(P - 1\right) \land \operatorname{length}\left(\operatorname{Waits}\left(\operatorname{Decoded}\left(p, P, b\right), T, 0, r\right)\right) \leq \operatorname{clog}\left(2, P\right) \land \forall w : \mathbb{N}, w \in \operatorname{Waits}\left(\operatorname{Decoded}\left(p, P, b\right), T, 0, r\right) \implies \left(0 < w \land w < P\right)\right)\right) \land \left(\forall b : \mathbb{N}, \operatorname{length}\left(\operatorname{Waits}\left(\operatorname{Decoded}\left(p, P, b\right), T, 0, P - 1\right)\right) = \operatorname{clog}\left(2, P\right)\right) \land \left(P = 1 \implies T = \operatorname{Stop}\left(0\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Budget/PositiveIntervalAcquisition.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At each live interval the elapsed phase is aligned with one endpoint. The midpoint lies strictly between both endpoints, so the next phase differs and its positive waiting distance is below P. The physical digit distinguishes exactly the two subintervals, including when p=2. Both subintervals fit the remaining binary depth. The rightmost residue always follows the larger half, whose upper logarithm drops by one, so its read count attains H. A singleton needs no subsequent query.

## References

- Truth anchor: `D5/S3/Observer/Budget/PositiveIntervalAcquisition.interval_wait`
- Truth anchor: `D5/S3/Observer/Budget/PositiveIntervalAcquisition.result`
- Dependency: [D5/S3/Observer/Budget/DyadicForwardWaitingOptimality](DyadicForwardWaitingOptimality.md)
