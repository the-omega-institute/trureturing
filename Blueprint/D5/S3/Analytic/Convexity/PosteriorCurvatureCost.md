# Posterior curvature and weak lower semicontinuity

## Abstract

The literal nonnegative posterior curvature integral is lower semicontinuous in the full weak topology of finite measures, with both infinite endpoint costs retained.

Let f be any real function convex on the positive real half-line. The curvature measure is the existing Stieltjes measure of its right derivative. No operator convexity or endpoint finiteness is required. For n in N, put a=1/(n+1), b=n+1. Integrate max(s v-u,0) on [a,1], and max(u-s v,0) on (1,b]. The atom at 1 belongs only to the first integral. These are finite real Bochner integrals because the curvature measure is finite on compact positive intervals.

**Definition 1.1 (Finite curvature truncations).**

Lean statement: `D5/S3/Analytic/Convexity/PosteriorCurvatureCost.curvatureTruncation`

*Formalization.* `D5/S3/Analytic/Convexity/PosteriorCurvatureCost.curvatureTruncation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

curvatureTruncation hf n u v is the sum of those two real integrals. The auxiliary positive endpoints small n, one and large n are defined inside the original Positive subtype.

**Theorem 1.2 (Nonnegativity).**

Lean statement: `D5/S3/Analytic/Convexity/PosteriorCurvatureCost.curvatureTruncation_nonneg`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Convexity/PosteriorCurvatureCost.curvatureTruncation_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every convexity witness hf, natural n and arbitrary real u,v, 0 <= curvatureTruncation hf n u v. Each hinge is nonnegative.

**Theorem 1.3 (Continuous in both real inputs).**

Lean statement: `D5/S3/Analytic/Convexity/PosteriorCurvatureCost.curvatureTruncation_continuous`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Convexity/PosteriorCurvatureCost.curvatureTruncation_continuous` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every hf and n the function (u,v) maps to curvatureTruncation hf n u v is continuous on R squared. The proof uses continuous parametric integration on the compact domains. The upper integral is expressed by restricting the curvature measure to (1,infinity), so its varying integrand is still integrated over a compact interval.

**Theorem 1.4 (Increasing truncations).**

Lean statement: `D5/S3/Analytic/Convexity/PosteriorCurvatureCost.curvatureTruncation_monotone`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Convexity/PosteriorCurvatureCost.curvatureTruncation_monotone` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every hf and real u,v, n maps to curvatureTruncation hf n u v is monotone. The lower domains increase as a decreases, the upper domains increase as b increases, and both integrands are nonnegative.

**Theorem 1.5 (Exact extended curvature remainder).**

Lean statement: `D5/S3/Analytic/Convexity/PosteriorCurvatureCost.iSup_curvatureTruncation`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Convexity/PosteriorCurvatureCost.iSup_curvatureTruncation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every hf and arbitrary real u,v, the supremum over n of ENNReal.ofReal(curvatureTruncation hf n u v) equals the literal curvatureRemainder hf u v. The lower domains exhaust (0,1], the upper domains exhaust (1,infinity). Monotone convergence proves the equality with no finite-remainder premise, including infinite values at either posterior endpoint.

**Definition 1.6 (Nonnegative continuous posterior functions).**

Lean statement: `D5/S3/Analytic/Convexity/PosteriorCurvatureCost.posteriorTruncation`

*Formalization.* `D5/S3/Analytic/Convexity/PosteriorCurvatureCost.posteriorTruncation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Posterior is the compact interval [0,1]. posteriorTruncation hf n is the NNReal-valued continuous function t maps to curvatureTruncation hf n t (1-t), with its proved nonnegativity. The NNReal representation is a genuine continuous map.

**Definition 1.7 (The actual nonnegative weak-measure objective).**

Lean statement: `D5/S3/Analytic/Convexity/PosteriorCurvatureCost.posteriorCurvatureCost`

*Formalization.* `D5/S3/Analytic/Convexity/PosteriorCurvatureCost.posteriorCurvatureCost` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every hf and nu in Mathlib's FiniteMeasure Posterior, posteriorCurvatureCost hf nu is the ENNReal lintegral of curvatureRemainder hf t (1-t) against nu. Its domain carries the stock topology of weak convergence of finite measures. The zero measure and arbitrary finite total mass are included.

**Theorem 1.8 (Exact increasing integral supremum).**

Lean statement: `D5/S3/Analytic/Convexity/PosteriorCurvatureCost.posteriorCurvatureCost_eq_iSup`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Convexity/PosteriorCurvatureCost.posteriorCurvatureCost_eq_iSup` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every hf and finite measure nu, posteriorCurvatureCost hf nu equals the supremum over n of the integral of posteriorTruncation hf n against nu, embedded in ENNReal. Pointwise exact exhaustion and monotone convergence in nu prove this equality. Infinity is preserved rather than truncated in the conclusion.

**Theorem 1.9 (Full weak lower semicontinuity).**

Lean statement: `D5/S3/Analytic/Convexity/PosteriorCurvatureCost.posteriorCurvatureCost_lowerSemicontinuous`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Convexity/PosteriorCurvatureCost.posteriorCurvatureCost_lowerSemicontinuous` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every hf, posteriorCurvatureCost hf is lower semicontinuous on FiniteMeasure Posterior. Each truncated integral is continuous by FiniteMeasure.continuous_lintegral_continuousMap; their exact supremum is lower semicontinuous. This uses the full weak topology and hence applies to arbitrary convergent nets. Only the curvature exhaustion is sequential; no sequential replacement of weak compactness or assumption of lower semicontinuity is used.

These are scalar analytic suppliers for the arbitrary-von-Neumann original-source reverse-test problem. They reuse the repository's curvature representation and Mathlib's monotone convergence, continuous parametric integration and weak finite-measure topology. The truncation argument is standard measure theory; no literature novelty or independent attainment conclusion is claimed here. The consuming attainment module computes the original full objective as a fixed finite affine term plus this nonnegative extended integral.

## References

- Truth anchor: `D5/S3/Analytic/Convexity/PosteriorCurvatureCost.curvatureTruncation`
- Truth anchor: `D5/S3/Analytic/Convexity/PosteriorCurvatureCost.curvatureTruncation_continuous`
- Truth anchor: `D5/S3/Analytic/Convexity/PosteriorCurvatureCost.curvatureTruncation_monotone`
- Truth anchor: `D5/S3/Analytic/Convexity/PosteriorCurvatureCost.curvatureTruncation_nonneg`
- Truth anchor: `D5/S3/Analytic/Convexity/PosteriorCurvatureCost.iSup_curvatureTruncation`
- Truth anchor: `D5/S3/Analytic/Convexity/PosteriorCurvatureCost.posteriorCurvatureCost`
- Truth anchor: `D5/S3/Analytic/Convexity/PosteriorCurvatureCost.posteriorCurvatureCost_eq_iSup`
- Truth anchor: `D5/S3/Analytic/Convexity/PosteriorCurvatureCost.posteriorCurvatureCost_lowerSemicontinuous`
- Truth anchor: `D5/S3/Analytic/Convexity/PosteriorCurvatureCost.posteriorTruncation`
- Dependency: [D5/S3/Analytic/Convexity/CurvaturePerspectiveEndpoints](CurvaturePerspectiveEndpoints.md)
