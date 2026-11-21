# Finite-time strip bounds for Laplace moments

## Abstract

Finite-time strip bounds for Laplace moments

**Theorem 1.1 (Finite product bound for entire interpolation).**

$$\exp\left(\frac{-L(r_{j}-q_{j})}{2}\right) \le M \prod_{k\in I\setminus\{j\}} \frac{\left|q_{j}-q_{k}\right|}{r_{j}+r_{k}}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Hardy/FiniteStripMomentBound.entire_strip_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Pierre Lissy (2026). *Optimal cost of fast boundary controls for the one-dimensional heat equation*. DOI: [10.48550/arXiv.2608.08041](https://doi.org/10.48550/arXiv.2608.08041). URL: <https://arxiv.org/abs/2608.08041v1>.

*Commentary.*

Write rᵢ = √(qᵢ²+β²). The input is an entire function whose norm at each z is at most M exp(L max(0, −Re z)), with M nonnegative. It takes value one at the selected node and vanishes at every other node in a finite family of distinct nonnegative real nodes indexed by a finite type I with decidable equality. The bound holds for every positive strip parameter β and every L ≥ 0.

The Cayley map gives u in the right half-plane. At z = β(u − 1/u)/2, multiplication by exp(−Lβ/(2u)) cancels the possible growth where Re z is negative. The disk bound then applies with constant M. For nodes q and r the pseudohyperbolic distance is |q−r| divided by the sum of their radii, where the radius at q is √(q²+β²). At the selected node the damping has modulus exp(−L(√(q²+β²)−q)/2).

**Theorem 1.2 (Lower bound for the exact Kronecker moments).**

$$\frac{\prod_{k\in I\setminus\{j\}} \frac{r_{j}+r_{k}}{\left|q_{j}-q_{k}\right|} \exp\left(\frac{-L(r_{j}-q_{j})}{2}\right)}{\sqrt{L}} \le \left\lVert h \right\rVert_{L^{2}(0,L)}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Hardy/FiniteStripMomentBound.windowNorm_lower_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Pierre Lissy (2026). *Optimal cost of fast boundary controls for the one-dimensional heat equation*. DOI: [10.48550/arXiv.2608.08041](https://doi.org/10.48550/arXiv.2608.08041). URL: <https://arxiv.org/abs/2608.08041v1>.

*Commentary.*

The time L and strip parameter β are positive, with rᵢ = √(qᵢ²+β²). Let q be any injective family of nonnegative real nodes indexed by a finite type I with decidable equality, and let j be an index. The moment conditions integrate h(s) exp(−qₖs) against Lebesgue measure on (0,L), with h real and square-integrable there. The moments equal one at the selected node and zero at the others. The resulting norm bound is the product of the reciprocal distances times the damping at the selected node, divided by √L.

The finite-window Laplace transform is entire by differentiation under the integral. Its growth constant is at most √L times the L² norm of h by Cauchy–Schwarz. Distinctness makes every factor being inverted positive. Lissy's Proposition 2.1 gives the exact-support context for a continuum heat equation through two Hardy conditions. The finite-window inequality here uses the support directly in the integral and yields an explicit product for arbitrary finite nodes.

## References

- Truth anchor: `D5/S3/Analytic/Hardy/FiniteStripMomentBound.entire_strip_bound`
- Truth anchor: `D5/S3/Analytic/Hardy/FiniteStripMomentBound.windowNorm_lower_bound`
- Dependency: [D5/S3/Analytic/Hardy/FiniteBlaschkeBound](FiniteBlaschkeBound.md)
