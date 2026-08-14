# The Exact Golden Displacement Surface Region

## Abstract

The prime-exponent slices determine the exact convergence region of the golden displacement surface, including its hidden-product threshold and a point beyond the former half-plane.

**Theorem 1.1 (The substitution start has a linear lower bound).**

$$\forall v: \mathbb{N}, \varphi v+\varphi -2\leq \operatorname{goldenSubstStart}(v)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Displacement/GoldenDisplacementSurfaceRegion.goldenSubstStart_linear_lower_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The frozen beta identity expresses the substitution start as the golden Euler exponent plus its conjugate linear part. Combining it with the frozen beta growth estimate and the standard golden-ratio identities gives the stated lower bound without new floor analysis.

**Theorem 1.2 (Prime-power terms are single real powers).**

$$p \text{prime} \Rightarrow dTerm(s, w, p^e)= p^{-(s \operatorname{goldenSubstStart}(e)+w e)}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Displacement/GoldenDisplacementSurfaceRegion.dTerm_prime_pow_rpow` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The frozen prime-power monomial factors have the same positive base. Real-power multiplication therefore combines their two exponents into one exact exponent account.

**Theorem 1.3 (The prime-slice criterion is exact).**

$$0\leq s \Rightarrow \operatorname{Summable}(dTerm(s, w)) \iff \forall k, 1< s \operatorname{goldenSubstStart}({k+1})+w {k+1}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Displacement/GoldenDisplacementSurfaceRegion.dTerm_summable_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Necessity restricts a summable surface to every fixed positive prime-exponent slice, where the exact prime rpow criterion forces exponent greater than one. For sufficiency, the exponent at the second slice makes the asymptotic slope positive. A natural shift then removes the finitely many small slices, and the linear substitution bound supplies a geometric majorant for the remaining product sum. The frozen nonnegative Euler bridge promotes the summable prime-power tail to the global series.

**Theorem 1.4 (The hidden-product axis has threshold one half).**

$$\operatorname{Summable}(dTerm(s, 0)) \iff \frac{1}{2}< s$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Displacement/GoldenDisplacementSurfaceRegion.nS_dirichlet_summable_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The first prime slice is the prime series with exponent minus twice s, so summability forces s above one half. Conversely every positive substitution start is at least two, and the exact slice criterion sums the full hidden-product Dirichlet series above that threshold.

**Theorem 1.5 (The former half-plane lies in the exact region).**

$$0\leq s, 1< s+w \Rightarrow \forall k, 1< s \operatorname{goldenSubstStart}({k+1})+w {k+1}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Displacement/GoldenDisplacementSurfaceRegion.exponent_gt_one_of_half_plane` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The substitution start dominates its exponent. Multiplying by nonnegative s shows that every exact prime-slice exponent dominates the former half-plane exponent, recovering the frozen sufficient condition as a corollary of the sharper region.

**Theorem 1.6 (A convergent point lies outside the former half-plane).**

$$\operatorname{Summable}(dTerm(1, -\frac{1}{2}))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Displacement/GoldenDisplacementSurfaceRegion.summable_dTerm_outside_half_plane` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At s equal to one and w equal to minus one half, the exact exponent criterion holds: the first slice is computed directly, while all later slices follow from the linear golden lower bound. Yet s plus w is only one half, so this witness lies strictly beyond the formerly known sufficient half-plane.

## References

- Truth anchor: `D5/S3/Analytic/Displacement/GoldenDisplacementSurfaceRegion.dTerm_prime_pow_rpow`
- Truth anchor: `D5/S3/Analytic/Displacement/GoldenDisplacementSurfaceRegion.dTerm_summable_iff`
- Truth anchor: `D5/S3/Analytic/Displacement/GoldenDisplacementSurfaceRegion.exponent_gt_one_of_half_plane`
- Truth anchor: `D5/S3/Analytic/Displacement/GoldenDisplacementSurfaceRegion.goldenSubstStart_linear_lower_bound`
- Truth anchor: `D5/S3/Analytic/Displacement/GoldenDisplacementSurfaceRegion.nS_dirichlet_summable_iff`
- Truth anchor: `D5/S3/Analytic/Displacement/GoldenDisplacementSurfaceRegion.summable_dTerm_outside_half_plane`
- Dependency: [D5/S3/Analytic/Displacement/GoldenDisplacementFaceHeatAbscissa](GoldenDisplacementFaceHeatAbscissa.md)
