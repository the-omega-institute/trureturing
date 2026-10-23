# Cyclic Transport and Weighted Rank

## Abstract

Cyclic Transport and Weighted Rank

Let K be any field and n any natural number. The coordinates are indexed by Fin(n+1). Write sigma=finRotate(n+1), P(k)=product of r(j) for j<k, and T_r(x)(i)=x(sigma(i))-r(i)x(i). Zero coefficients are permitted in r. The argument works for every length, including one coordinate. The cyclic bipartite conclusion additionally assumes characteristic two and nonzero b(i).

**Theorem 1.1 (Cyclic transport nullity).**

$$\forall K \in Type,\; [\mathrm{Field}\left(K\right)] \forall n \in \mathrm{Nat},\; \forall r \in \mathrm{Fin}\left(n + 1\right) \to K,\; \mathrm{finrank}\left(K, \mathrm{ker}\left(\mathrm{transport}\left(r\right)\right)\right) = \mathrm{If}\left(\mathrm{product}\left(r\right) = 1, 1, 0\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/WeightedCycleKernel.transport_nullity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every r:Fin(n+1)->K, the kernel dimension of T_r is one if product(r)=1 and zero otherwise. Kernel coordinates satisfy x(k)=P(k)x(0). Evaluation at zero is injective. The last equation gives x(0)=product(r)x(0); if the product is not one, all coordinates vanish. If it is one, the prefix-product vector is a nonzero kernel vector. This is the all-length inference used in the weighted rank calculation.

**Theorem 1.2 (Rank of the cyclic bipartite block).**

$$\forall K \in Type,\; [\mathrm{Field}\left(K\right)] \forall n \in \mathrm{Nat},\; [\mathrm{CharP}\left(K, 2\right)] \forall a \in \mathrm{Fin}\left(n + 1\right) \to K,\; \forall b \in \mathrm{Fin}\left(n + 1\right) \to K,\; (\forall i \in \mathrm{Fin}\left(n + 1\right),\; \mathrm{b}\left(i\right) \ne 0) \Rightarrow \mathrm{rank}\left(\mathrm{fromBlocks}\left(0, \mathrm{cyclicBidiagonal}\left(a, b\right), \mathrm{transpose}\left(\mathrm{cyclicBidiagonal}\left(a, b\right)\right), 0\right)\right) = \mathrm{If}\left(\mathrm{product}\left(a\right) = \mathrm{product}\left(b\right), 2 \cdot n, 2 \cdot \left(n + 1\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/WeightedCycleKernel.cyclic_bipartite_rank` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let B(i,j)=[j=i]a(i)+[j=sigma(i)]b(i), with every b(i) nonzero. The symmetric block matrix [0 B; transpose(B) 0] has rank 2n if product(a)=product(b), and 2(n+1) otherwise. In characteristic two its kernel equation becomes cyclic transport with r(i)=a(i)/b(i). Rank-nullity computes rank(B). The two off-diagonal kernel components give twice that rank. The coefficients a(i) are unrestricted.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/WeightedCycleKernel.cyclic_bipartite_rank`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/WeightedCycleKernel.transport_nullity`
