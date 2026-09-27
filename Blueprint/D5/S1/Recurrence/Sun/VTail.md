# Strict Turan Tail for v

## Abstract

Positive radical normalization transports the weighted recurrence bound to a strict lowercase-v tail.

**Theorem 1.1 (Strictness beyond the v tail threshold).**

$$\forall n: \mathbb{N}, 1 \le n \Rightarrow \forall t: \mathbb{R}, (n: \mathbb{R}) \cdot \left((n: \mathbb{R}) + 1\right) - \frac{2 \cdot (n: \mathbb{R})^{3}}{\sqrt{4 \cdot (n: \mathbb{R})^{2} - 1}} \le t \Rightarrow 0 < \left((-1)^{n} \cdot v\left(-t, n\right)\right)^{2} - (-1)^{n - 1} \cdot v\left(-t, n - 1\right) \cdot (-1)^{n + 1} \cdot v\left(-t, n + 1\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Sun/VTail.v_tail_strict` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Zhi-Hong Sun (2026). *Generalizations of the Christoffel-Darboux formula and congruences involving Apéry-like numbers*. DOI: [10.48550/arXiv.2608.13192](https://doi.org/10.48550/arXiv.2608.13192). URL: <https://arxiv.org/html/2608.13192v1>.

*Acknowledgement.* Ilia Krasikov (2011). *Turán inequalities for three-term recurrences with monotonic coefficients*. DOI: [10.1016/j.jat.2011.04.007](https://doi.org/10.1016/j.jat.2011.04.007). URL: <https://arxiv.org/html/1101.3204v1>.

*Commentary.*

Write R(j)=(-1)^j v(-t,j), a(j)=j^3/sqrt(4j^2-1) for j>0, b(j)=j(j+1), and q(j)=sqrt(2j+1)R(j). The positive factor d(j)=1/sqrt(2j+1) gives R(j)=d(j)q(j). The proof checks both initials and the exact recurrence by two-step uniqueness; it does not assume that the source sequence has the supplier's normalization. Positivity of the radicals and monotonicity of b are proved. Strict increase of a follows by clearing positive denominators: at j=k+1 the numerator is 16k^7+168k^6+746k^5+1815k^4+2604k^3+2187k^2+982k+177, positive for k at least zero. The direct supplier call yields a weighted nonnegative determinant on the closed threshold t at least n(n+1)-2n^3/sqrt(4n^2-1). Exact positive scaling transports it to R, with neighbor weight (n+1)^3(2n-1)/(n^3(2n+1))>1. The recurrence excludes adjacent zeros, and the sign split of the neighbor product makes the unweighted determinant strict. VStrict consumes this tail.

## References

- Truth anchor: `D5/S1/Recurrence/Sun/VTail.v_tail_strict`
- Dependency: [D5/S1/Recurrence/Sun/Sequences](Sequences.md)
- Dependency: [D5/S1/Recurrence/Turan/StrictlyIncreasingTail](../Turan/StrictlyIncreasingTail.md)
