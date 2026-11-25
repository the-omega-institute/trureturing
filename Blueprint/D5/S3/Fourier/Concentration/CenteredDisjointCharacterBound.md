# Centered disjoint coefficient bound

## Abstract

Centering the local exponential difference preserves the signed phase sum and a quadratic penalty.

**Theorem 1.1 (Quadratic exponential majorant).**

$$\begin{aligned}&d<k\implies\operatorname{C}\left(T\right)=0\\&d \ge k\implies|\operatorname{C}\left(T\right)| \le \prod_{j \in T}|\operatorname{a}\left(j\right)|\sum_{0 \le m \le \operatorname{floor}\left(n/2\right)}\frac{|u|^{n-2m}v^{m}}{(n-2m)!m!}\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Concentration/CenteredDisjointCharacterBound.centered_overlap_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any finite subset T, complex phases a(j), complex c and natural degree d, put k=|T|, u=c−(sum of a(j) over T)/2 and v=(sum of |a(j)|² over T)/24. Write C(T) for the degree-d coefficient of exp(cx) times the product over T of exp(−a(j)x)−1. If d<k this coefficient vanishes. Otherwise put n=d−k and use the displayed finite sum over m from 0 to the floor of n/2.

The local centered identity expresses the exponential difference as −a(j)x exp(−a(j)x/2) multiplied by an even series. Its degree-2m coefficient is (a(j)/2)^(2m)/(2m+1)!, also when a(j)=0. The established factorial inequality 6^m m! ≤ (2m+1)! bounds its modulus by (|a(j)|²/24)^m/m!; odd coefficients are zero.

Extracting the k linear factors and combining the complex exponentials yields exp(ux). The Cauchy product propagates the coefficientwise domination, so the even factors are majorized by the coefficients of exp(v x²). Their product with the majorant exp(|u|x) gives the finite sum after reindexing the even powers. The bound retains the complex center u for each subset and the total squared local phase norms.

This estimate can replace the earlier degree-sensitive overlap bound in the signed parity remainder. Estimating the resulting sums over subsets and characters at the resolution of actual zeta-zero near-collisions remains a separate arithmetic problem.

## References

- Truth anchor: `D5/S3/Fourier/Concentration/CenteredDisjointCharacterBound.centered_overlap_bound`
- Dependency: [D5/S3/Arith/DiophantineApproximation/CountingVolume](../../Arith/DiophantineApproximation/CountingVolume.md)
- Dependency: [D5/S3/Fourier/Concentration/DisjointCharacterRemainder](DisjointCharacterRemainder.md)
