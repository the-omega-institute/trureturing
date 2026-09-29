# Finite Source Critical Tail

## Abstract

Finite source boundaries have geometric antidiagonal tails at the critical weight.

**Theorem 1.1 (A larger radius controls the actual recursive output).**

$$\forall K \in Type, A \in \mathbb{R}, rho \in \mathbb{R}, M \in \mathbb{N}, b \in \mathbb{N}\to K,\; \left(\operatorname{NormedRing}\left(K\right) \land \left(0 < A \land \left(0 < rho \land \left(rho < 1 \land \left(A \cdot rho = \left(1 - rho\right)^{2} \land \left(\left(\forall i \in \mathbb{N},\; \operatorname{norm}\left(\operatorname{b}\left(i\right)\right) \le A\right) \land \left(\forall i \in \mathbb{N},\; M < i \Rightarrow \operatorname{b}\left(i\right) = 0\right)\right)\right)\right)\right)\right)\right) \Rightarrow \left(\exists R \in \mathbb{R},\; rho < R \land \left(R < 1 \land \left(\left(\forall n \in \mathbb{N}, k \in \mathbb{N},\; \operatorname{norm}\left(\operatorname{extension}\left(b, n, k\right)\right) \cdot R^{k} \le A\right) \land \left(\left(\forall L \in \mathbb{N},\; \operatorname{Tail}\left(rho, b, L\right) \le A \cdot \frac{rho}{R}^{L}\right) \land \operatorname{Tendsto}\left(\operatorname{Tail}\left(rho, b\right), atTop, \operatorname{nhds}\left(0\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/SeriesInequalities/FiniteSourceCriticalTail.finite_source_critical_tail` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let K be a normed ring, including the real or complex numbers. The boundary b is bounded in norm by A and vanishes at every index greater than M. The extension E has E(n,0)=b(n) and E(n,k+1)=E(n+1,k)-sum over j=0,...,k of E(n,j)b(k-j).

Tail(rho,b,L) is the supremum of rho^(n+k) times the norm of E(n,k), over all natural n and k with L at most n+k. The theorem proves that these sets of values are bounded and that their suprema converge to zero.

The finite mass polynomial g(x)=x+A sum over i=0,...,M of x^(i+1) satisfies g(rho)=1-(1-rho)rho^(M+1)<1. Continuity supplies rho<R<1 with g(R)<1. Strong induction on the column index gives the uniform bound norm(E(n,k)) R^k at most A.

Writing q=rho/R, one has rho at most q and q<1. Thus every weighted entry on the Lth tail is at most A q^L. This controls the complete output of a finitely supported boundary, including its infinitely many columns. The radius may depend on the support bound M.

The statement proves finite-source tail decay. It does not assert a rational Taylor-germ identity, norm-closedness of the full source image, or compactness of that image.

## References

- Truth anchor: `D5/S3/Analytic/SeriesInequalities/FiniteSourceCriticalTail.finite_source_critical_tail`
