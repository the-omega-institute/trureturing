# PowerConvexity

## Abstract

Dimension-independent operator power convexity through a compensated integral.

**Theorem 1.1 (Convex compensated resolvent kernel).**

$$\forall u: \operatorname{Level}(), A: \operatorname{Type}(u),\ [\operatorname{CStarAlgebra}(A)], [\operatorname{PartialOrder}(A)], [\operatorname{StarOrderedRing}(A)],\ p, t: \mathbb{R}, 0<t\implies\ \operatorname{ConvexOn}(\mathbb{R}, \operatorname{Ici}(0: A), \operatorname{cfc}(\operatorname{rpowIntegrand12}(p, t)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Lieb/PowerConvexity.convexOn_cfc_rpowIntegrand_one_two` (`✓ std3`). ∎

*Citation.* Frédéric Dupuis (2025). *Integral representations and order properties of spectral powers in Mathlib*. URL: <https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Analysis/SpecialFunctions/ContinuousFunctionalCalculus/Rpow/IntegralRepresentation.lean>.

*Commentary.*

For t > 0 and every real p, the CFC of the compensated kernel t to exponent p-1 times [t inverse X + t Ring.inverse(t I + X) - I] is convex on the full nonnegative cone of any complete ordered complex C-star algebra. Shifted inverse convexity is consumed directly from pinned Mathlib. This kernel is the real live supplier for the integral proof.

**Theorem 1.2 (Full operator power interval).**

$$\forall u: \operatorname{Level}(), A: \operatorname{Type}(u),\ [\operatorname{CStarAlgebra}(A)], [\operatorname{PartialOrder}(A)], [\operatorname{StarOrderedRing}(A)],\ p: \mathbb{R}, 1\le p\le 2\implies\ \operatorname{ConvexOn}(\mathbb{R}, \operatorname{Ici}(0: A), \Lambda X\mapsto\operatorname{rpow}(X, p))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Lieb/PowerConvexity.convexOn_rpow` (`✓ std3`). ∎

*Citation.* Frédéric Dupuis (2025). *Integral representations and order properties of spectral powers in Mathlib*. URL: <https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Analysis/SpecialFunctions/ContinuousFunctionalCalculus/Rpow/IntegralRepresentation.lean>.

*Commentary.*

For every 1 <= p <= 2, spectral CFC power is convex on the full nonnegative cone of every complete ordered complex C-star algebra. For 1 < p < 2 use the existing one-measure representation and norm integrability of the whole compensated kernel, transfer its nonunital CFC to unital CFC, then integrate the convexity inequality. No separate integral of the linear, inverse, or constant summands is asserted.

At p=1 the map is affine. At p=2 the convexity gap is s t times (X-Y)* (X-Y), where s+t=1. Cross products retain their order, so the square identity includes noncommuting inputs. The cone includes zero and singular operators.

**Theorem 1.3 (Uniform all-Hilbert Jensen input).**

$$\forall u: \operatorname{Level}(), p: \mathbb{R},\ 1\le p\le 2\implies\ \operatorname{CondIciAll}(\Lambda x\mapsto\operatorname{rpow}(x, p))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Lieb/PowerConvexity.condIciAll_rpow` (`✓ std3`). ∎

*Citation.* Frédéric Dupuis (2025). *Integral representations and order properties of spectral powers in Mathlib*. URL: <https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Analysis/SpecialFunctions/ContinuousFunctionalCalculus/Rpow/IntegralRepresentation.lean>.

*Commentary.*

For every universe and every complete nontrivial complex Hilbert space K, x to exponent p is operator convex on the nonnegative real spectrum, continuous on that interval, and zero at zero. Thus it supplies the actual CondIciAll required by the public Jensen perspective theorem. Finite Hilbert-Schmidt convexity is not substituted for this uniform condition.

The method is classical and consumes pinned Mathlib sources by Frederic Dupuis, Apache-2.0; it makes no novelty claim. TracePerspectiveConvexity consumes the uniform condition via the existing public unrestricted-real-exponent phiK bridge. Its matrix transport and reverse Young endpoint optimizer interpolation supply CarlenLiebConvexity. The original Hiai theorem and support boundary remain separate obligations. Native four-slot audit is unfinished under #5214: a faithful enrolled template and realization covering the full C-star and all-Hilbert telescopes, rigid universe reconstruction and variation/sensitivity evidence have not been supplied. No declared_validated status is claimed.

## References

- Truth anchor: `D5/S3/Quantum/Lieb/PowerConvexity.condIciAll_rpow`
- Truth anchor: `D5/S3/Quantum/Lieb/PowerConvexity.convexOn_cfc_rpowIntegrand_one_two`
- Truth anchor: `D5/S3/Quantum/Lieb/PowerConvexity.convexOn_rpow`
- Dependency: [D5/S3/Quantum/Lieb/JensenOperatorInequality](JensenOperatorInequality.md)
