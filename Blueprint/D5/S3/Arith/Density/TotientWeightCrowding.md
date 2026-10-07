# Finite Totient Weight Crowding

## Abstract

Total Euler totient weight bounds the cardinality of every finite positive support.

**Theorem 1.1 (A universal finite support estimate).**

$$\forall A: \operatorname{Finset}\left(\mathbb{N}\right),(\forall d\in A,0<d)\Rightarrow\operatorname{card}\left(A\right)^{3}\le16\cdot(\sum_{d\in A}\operatorname{phi}\left(d\right))^{2}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Density/TotientWeightCrowding.finite_totient_weight_crowding` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let A be a finite set of positive natural numbers. Write k for its cardinality and W for the sum of the actual Euler totients of its members. Then k cubed is at most sixteen times W squared. All sums, products, and powers in the statement are natural-number operations. The empty set has k=W=0. No divisor closure or restriction on the largest member is required.

Euler's classical product formula gives n <= 2 phi(n)^2 for every positive n. Indeed, write n=qR, where R is the product of its distinct prime factors, and put T equal to the product of p-1 over those factors. Then phi(n)=qT and q>=1. Every odd prime satisfies p <= (p-1)^2; the prime two contributes only a factor of two. Thus R<=2T^2 and n<=2(qT)^2.

When k>0, split A into a low part satisfying 4 phi(d)^2 <= k and its complement. Each low member lies between one and floor(k/2), so the low part has at most floor(k/2) members. If h is the size of the high part, then k<=2h and h>0.

Let m be the minimum actual totient among the high members. Its minimizing member satisfies k<4m^2, and summing the lower bound m over the high part gives hm<=W. Consequently k^3 <= 4h^2 k <= 16(hm)^2 <= 16W^2. This estimate uses only positivity and distinctness of the indices.

## References

- Truth anchor: `D5/S3/Arith/Density/TotientWeightCrowding.finite_totient_weight_crowding`
