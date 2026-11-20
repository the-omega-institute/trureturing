# A one-sided curvature bound for weighted tail primitives

## Abstract

A monotone count bounds the weighted primitive's central second difference from above.

**Theorem 1.1 (The central second difference from integrand bounds).**

Lean statement: `D5/S3/Analytic/Asymptotics/OneSidedTailCurvature.weighted_second_difference_le`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Asymptotics/OneSidedTailCurvature.weighted_second_difference_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let f,k be real-valued functions on ℝ and let a,b,B,L,t,h be real with a ≥ 0, L ≥ 0, h ≥ 0, a ≤ t−h, and t+h ≤ b. Assume f is interval integrable with respect to volume on a..b, and k(y)−k(x) = ∫ from x to y of f(v) dv whenever a ≤ x ≤ y ≤ b. Assume f(x) ≤ B on [a,b] and f(y)−f(x) ≤ L(y−x) whenever a ≤ x ≤ y ≤ b. Then (t+h)k(t+h)+(t−h)k(t−h)−2t k(t) ≤ (bL+2B)h².

Translate the right half of the interval back by h. The increment bound controls the difference of the adjacent integrals by Lh². The pointwise bound controls their sum by 2Bh. Expanding the central difference of t k(t) gives t times the difference plus h times the sum, and 0 ≤ t ≤ b.

**Theorem 1.2 (A finite central difference bound for a monotone count).**

Lean statement: `D5/S3/Analytic/Asymptotics/OneSidedTailCurvature.weighted_tail_curvature`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Asymptotics/OneSidedTailCurvature.weighted_tail_curvature` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let 0 < a ≤ b and let V,k be real-valued functions on ℝ. Assume V is nondecreasing on [exp(a),exp(b)]. Put q(v) = (v+1)/v², r(V,v) = 1−exp(−v)V(exp(v)), and f(v) = q(v)r(V,v). Assume f is interval integrable with respect to volume on a..b and k(y)−k(x) = ∫ from x to y of f(v) dv whenever a ≤ x ≤ y ≤ b. There exists C ≥ 0 such that for every h ≥ 0 and t with [t−h,t+h] contained in [a,b], (t+h)k(t+h)+(t−h)k(t−h)−2t k(t) ≤ Ch².

Set M = max(|V(exp(a))|, |V(exp(b))|), R = 1+M, and Lq = (1/a)²(1+2/a). Monotonicity bounds the count by the two endpoint values in order, so |r(V,v)| ≤ R. For x ≤ y in [a,b], the order of the counts and 1−exp(−(y−x)) ≤ y−x give r(V,y)−r(V,x) ≤ M(y−x). The positive decreasing weight satisfies 0 ≤ q(x)−q(y) ≤ Lq(y−x). Thus f has upper bound q(a)R and upper increment slope q(a)M+Lq R. One can take C = b(q(a)M+Lq R)+2q(a)R.

## References

- Truth anchor: `D5/S3/Analytic/Asymptotics/OneSidedTailCurvature.weighted_second_difference_le`
- Truth anchor: `D5/S3/Analytic/Asymptotics/OneSidedTailCurvature.weighted_tail_curvature`
