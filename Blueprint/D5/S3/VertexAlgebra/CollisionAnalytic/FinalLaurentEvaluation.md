# The final inverse chart evaluates to its rational function

## Abstract

Absolute evaluation of the original final inverse Laurent coefficients for every finite complex polynomial numerator.

**Theorem 1.1 (Joint absolute convergence and the exact Laurent sum).**

Lean statement: `D5/S3/VertexAlgebra/CollisionAnalytic/FinalLaurentEvaluation.final_laurent_absolute_evaluation`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/CollisionAnalytic/FinalLaurentEvaluation.final_laurent_absolute_evaluation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Atsushi Matsuo; Kiyokazu Nagatomo (1997). *On axioms for a vertex algebra and the locality of quantum fields*. URL: <https://arxiv.org/abs/hep-th/9706118v1>.

*Commentary.*

Let Q be any complex polynomial in three variables, k any natural number, and a a triple of natural pole orders. For nonzero complex x,y,z with norm(x)<norm(y) and norm(x)+norm(y)<norm(z), take the original ThreeFieldFinalLaurentFiber.laurentCoefficient of Q coerced to a power series. Its Laurent monomial terms, indexed by every signed integer exponent vector e, are absolutely summable. Their HasSum value is Q(x,y,z) divided by x^k y^k (x+y)^k (x+y+z)^(a0) (y+z)^(a1) z^(a2). The theorem also proves absolute summability of the ungrouped original laurentTerm family over every pair (e,i).

Write i=((j,q),(h,l)). The original input exponent n equals e plus the native signed shift. Translation in each signed exponent is a bijection; it changes neither the numerator nor its coefficients. The raw term factors as the numerator monomial at n, times x^(-k)y^(-2k)z^(-(a0+a1+a2)), times the three inverse-binomial series. The middle factor retains the joint q,h term choose(q,h)(x/y)^h(y/z)^q. Its h norm sum is (1+norm(x/y))^q, so the q norm series has ratio (norm(x)+norm(y))/norm(z). This proves joint absolute convergence before grouping.

Mathlib's negative-binomial geometric sum evaluates each positive pole order. Ring.choose_neg supplies the exact sign and ordinary binomial coefficient; order zero is the single nonzero term at index zero. Finite numerator support and absolute product sums give the entire raw family. The original laurentInput equations, mem_laurentFiber_iff and laurentCoefficient_eq_sum then identify each grouped sum. The triangle inequality gives absolute convergence after grouping; HasSum.prod_fiberwise preserves the exact value. Algebra simplifies it to the displayed rational quotient.

No individual raw exponent is required to be nonnegative: nonnegativity is tested only on the original input to the polynomial. Zero Q and every combination of zero pole orders are included. This statement concerns the given scalar polynomial numerator and its final inverse chart. Applying it to a field channel requires an independently established equality with these coefficients and a genuine finite numerator.

This scalar analytic bridge does not assert all-chart analytic sewing, operator-valued convergence, arbitrary-dimensional lattice scalar polynomial numerators, joint internal-occupation convergence, or completion of Moonshine, VOA/CFT, anomaly, fusion, string theory or AdS/CFT. Matsuo--Nagatomo is local-field background. The binomial, geometric and unconditional summation results are Mathlib contributions under Apache 2.0; no literature novelty is claimed.

## References

- Truth anchor: `D5/S3/VertexAlgebra/CollisionAnalytic/FinalLaurentEvaluation.final_laurent_absolute_evaluation`
- Dependency: [D5/S3/VertexAlgebra/FormalSeries/ThreeFieldFinalLaurentFiber](../FormalSeries/ThreeFieldFinalLaurentFiber.md)
