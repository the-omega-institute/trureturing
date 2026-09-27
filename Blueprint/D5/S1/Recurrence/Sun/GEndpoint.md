# Strictness at the g Endpoint

## Abstract

A factorial-scaled integer parity invariant makes the g determinant strict at the closed endpoint x=-1.

**Theorem 1.1 (Strict g determinant at x=-1).**

$$\forall n: \mathbb{N}, 1 \le n \Rightarrow g\left(-1, n\right)^{2} > g\left(-1, n - 1\right) \cdot g\left(-1, n + 1\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Sun/GEndpoint.g_endpoint_strict` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Zhi-Hong Sun (2026). *Generalizations of the Christoffel-Darboux formula and congruences involving Apéry-like numbers*. DOI: [10.48550/arXiv.2608.13192](https://doi.org/10.48550/arXiv.2608.13192). URL: <https://arxiv.org/html/2608.13192v1>.

*Commentary.*

For every positive n, set P(k)=(-1)^k g(-1,k) and Z(k)=(k!)^2 P(k). The recurrence makes Z integral with Z(0)=1, Z(1)=0 and Z(k+2)=-2(k+1)(k+2)Z(k+1)-(k+1)^4 Z(k). Induction in ZMod 2 shows Z is odd at even indices and even at odd indices. Consequently (n+1)Z(n)+n^3 Z(n-1) is odd and nonzero. The scaled determinant is the square of the corresponding real combination, so it is strictly positive. GStrict consumes this endpoint result; no finite-index experiment substitutes for the parity induction.

## References

- Truth anchor: `D5/S1/Recurrence/Sun/GEndpoint.g_endpoint_strict`
- Dependency: [D5/S1/Recurrence/Sun/Sequences](Sequences.md)
