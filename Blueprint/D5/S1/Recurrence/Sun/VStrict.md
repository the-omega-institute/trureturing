# Strict Turan Inequality for v

## Abstract

The second complete closed-domain clause of Sun's Conjecture 5.2 holds at every positive index.

**Theorem 1.1 (The full v inequality on x at most -1/8).**

$$\forall n: \mathbb{N}, 1 \le n \Rightarrow \forall x: \mathbb{R}, x \le -(\frac{1}{8}) \Rightarrow v\left(x, n\right)^{2} > v\left(x, n - 1\right) \cdot v\left(x, n + 1\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Sun/VStrict.v_strict_turan` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Zhi-Hong Sun (2026). *Generalizations of the Christoffel-Darboux formula and congruences involving Apéry-like numbers*. DOI: [10.48550/arXiv.2608.13192](https://doi.org/10.48550/arXiv.2608.13192). URL: <https://arxiv.org/html/2608.13192v1>.

*Commentary.*

For every n at least one and every real x at most -1/8, the square of v(x,n) strictly exceeds the product of its two neighbors. Set t=-x, m=n(n+1), D=4m+1, r=2m sqrt(m)/sqrt(D), L=m-r, U=m+r, and T=m-2n^3/sqrt(4n^2-1). The exact identity 4m^3-(m-1/8)^2 D=(12m-1)/64>0 proves L<1/8; also T<m<U. Thus t at least 1/8 and t<T lies in the open local interval (L,U), where the recurrence determinant is a positive quadratic form. Positive recurrence coefficients exclude adjacent zeros. At t at least T, VTail supplies strictness including the threshold. The proof translates the sign-normalized determinant back to literal lowercase v. The argument includes x=-1/8 and every positive n; it makes no claim about uppercase V.

## References

- Truth anchor: `D5/S1/Recurrence/Sun/VStrict.v_strict_turan`
- Dependency: [D5/S1/Recurrence/Sun/VTail](VTail.md)
