# Residual estimates

## Abstract

Residual estimates

**Theorem 1.1 (One-period residual formula).**

$$\forall p \in \mathbb{N},\; \forall L \in \mathbb{N},\; \forall r \in \mathbb{N},\; r \le p \Rightarrow \left(\operatorname{f}\left(p, L, r\right) = \operatorname{w}\left(L, r\right) + \operatorname{w}\left(L, p - r\right) \Leftrightarrow \left(p = 0 \lor L \le p + \operatorname{min}\left(r, p - r\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Divisors/ErdosNicolas/Residual.f_eq_two_terms` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* P. Erdős and J.-L. Nicolas (1989). *On functions connected with prime divisors of an integer*. URL: <https://oeis.org/A330076>.

*Commentary.*

For r <= p, the two-site formula holds exactly when p=0 or L<=p+min(r,p-r). For p>0 these sites have distances r and p-r. Under the window condition every omitted distance is at least L, where the residual vanishes. Conversely an exceeded window gives a positive omitted term. At p=0, r=0 and every L gives zero. The window is exact for p>0: exceeding either omitted distance p+r or 2p-r introduces a positive term. For p=3,r=1,L=4 equality still holds; L=5 fails.

**Theorem 1.2 (Two-period residual formula).**

$$\forall p \in \mathbb{N},\; \forall r \in \mathbb{N},\; r \le p \Rightarrow \operatorname{f}\left(p, 2 \cdot p, r\right) = \operatorname{w}\left(2 \cdot p, r\right) + \operatorname{w}\left(2 \cdot p, p - r\right) + \operatorname{w}\left(2 \cdot p, p + r\right) + \operatorname{w}\left(2 \cdot p, 2 \cdot p - r\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Divisors/ErdosNicolas/Residual.f_eq_four_terms` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* P. Erdős and J.-L. Nicolas (1989). *On functions connected with prime divisors of an integer*. URL: <https://oeis.org/A330076>.

*Commentary.*

For natural parameters with r <= p, the four possible contributing sites are minus one, zero, one and two. The distances are p+r, r, p-r and 2p-r. The omitted sites have distance at least 2p. At either endpoint r=0 or r=p, the result is twice w(2p,p). The zero-period case has value zero.

## References

- Truth anchor: `D5/S3/Arith/Divisors/ErdosNicolas/Residual.f_eq_four_terms`
- Truth anchor: `D5/S3/Arith/Divisors/ErdosNicolas/Residual.f_eq_two_terms`
- Dependency: [D5/S3/Arith/Divisors/ErdosNicolas/KernelCriterion](KernelCriterion.md)
