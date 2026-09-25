# Strict Turan Inequality for g

## Abstract

The first complete closed-domain clause of Sun's Conjecture 5.2 holds at every positive index.

**Theorem 1.1 (The full g inequality on x at most -1).**

$$\forall n: \mathbb{N}, 1 \le n \Rightarrow \forall x: \mathbb{R}, x \le -1 \Rightarrow g\left(x, n\right)^{2} > g\left(x, n - 1\right) \cdot g\left(x, n + 1\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Sun/GStrict.g_strict_turan` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Zhi-Hong Sun (2026). *Generalizations of the Christoffel-Darboux formula and congruences involving Apéry-like numbers*. DOI: [10.48550/arXiv.2608.13192](https://doi.org/10.48550/arXiv.2608.13192). URL: <https://arxiv.org/html/2608.13192v1>.

*Commentary.*

For every n at least one and every real x at most -1, the square of g(x,n) strictly exceeds the product of its two neighbors. Put t=-(x+1)/2 and P(k)=(-1)^k g(-2t-1,k). The local recurrence has a(k)=k^2 and b(k)=2k(k+1), and positive coefficients exclude adjacent zeros. At t=0, GEndpoint supplies strictness. For 0<t<2n, the recurrence determinant is a positive quadratic form, with discriminant factor t(4n(n+1)-t)>0. On t at least 2n, recurrence uniqueness identifies P with the canonical supplier sequence; the direct weighted-tail call and weight (n+1)^2/n^2>1 give strictness after splitting the neighbor product by sign. Sign transport returns the literal lowercase g claim. The endpoint, local range and closed tail cover the entire source domain.

## References

- Truth anchor: `D5/S1/Recurrence/Sun/GStrict.g_strict_turan`
- Dependency: [D5/S1/Recurrence/Sun/GEndpoint](GEndpoint.md)
- Dependency: [D5/S1/Recurrence/Turan/StrictlyIncreasingTail](../Turan/StrictlyIncreasingTail.md)
