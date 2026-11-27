# Laurent, Lucas, Fibonacci, alternating and product Morgan–Voyce identities

## Abstract

The Morgan–Voyce polynomials satisfy a Laurent identity, P_m(1) = L_{2m+1}, a Fibonacci multiple formula, period six at −1, and a product over 4 sin²(jπ/(2m + 1)).

**Theorem 1.1 (Further Morgan–Voyce identities).**

Lean statement: `D5/S1/Recurrence/Invariants/AffinePolynomialPairMorganVoyceIdentities.result`

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/AffinePolynomialPairMorganVoyceIdentities.result` (`✓ std3`). ∎

*Citation.* Haobo Ma; Wenlin Zhang (2026). *Extensions of Knuth's coefficient families (1993), with corrected OEIS links: Werner's conjecture in OEIS A208509, Formula, revision 28*. DOI: [10.5281/zenodo.24211281](https://doi.org/10.5281/zenodo.24211281). URL: <https://zenodo.org/records/24211281>.

*Commentary.*

In every commutative ring, for all z and w, z^{2m+1} − w^{2m+1} = (z − w) ∑_k [x^k]P_m (z − w)^{2k} (zw)^{m−k}, the degree-m homogenization of P_m evaluated at ((z − w)², zw); with w = z^{−1} this is the Laurent identity z^{2m+1} − z^{−(2m+1)} = (z − z^{−1}) P_m((z − z^{−1})²). P_m(1) = L_{2m+1} with the frozen Lucas numbers. For all m and n, F_{(2m+1)n} = ∑_{k=0}^{m} [x^k]P_m (−1)^{(m+k)n} 5^k F_n^{2k+1}. The values P_m(−1) repeat 1, 2, 1, −1, −2, −1. The homogeneous identity is proved by induction with multiplier z² + w²; its special case zw = c with c² = 1 gives z^{2m+1} − w^{2m+1} = (z − w) c^m P_m((z − w)² c). With z = φ^n, w = ψ^n and c = (−1)^n, Binet's formula gives the Fibonacci identity. Over the reals, P_m(x) = ∏_{j=1}^{m} (x + 4 sin²(jπ/(2m + 1))) for every m; the source states m ≥ 1, and at m = 0 both sides are 1. P_m is monic of degree m. The Laurent identity at z = cos θ + i sin θ shows that −4 sin²θ is a root when sin((2m + 1)θ) = 0 and sin θ ≠ 0. The m roots for θ = jπ/(2m + 1), 1 ≤ j ≤ m, are distinct because sin is strictly increasing on (0, π/2), so they exhaust the roots and P_m is their product. This is Corollary 3 of H. Ma and W. Zhang's note on A208509 (DOI 10.5281/zenodo.24211281).

## References

- Truth anchor: `D5/S1/Recurrence/Invariants/AffinePolynomialPairMorganVoyceIdentities.result`
- Dependency: [D5/S1/Recurrence/Invariants/AffinePolynomialPairMorganVoyceShear](AffinePolynomialPairMorganVoyceShear.md)
