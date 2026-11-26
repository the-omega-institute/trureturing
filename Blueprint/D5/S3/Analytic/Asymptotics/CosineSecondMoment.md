# Divergence of the normalized cosine defect

## Abstract

A divergent second moment forces the normalized cosine defect to diverge.

**Theorem 1.1 (A divergent second moment forces infinite positive curvature).**

Lean statement: `D5/S3/Analytic/Asymptotics/CosineSecondMoment.tendsto_cosine_defect_div_sq_atTop`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Asymptotics/CosineSecondMoment.tendsto_cosine_defect_div_sq_atTop` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let a and ω be real sequences indexed by ℕ. Assume a(n) ≥ 0 for all n, a is summable, and a(n)ω(n)² is not summable. Then (∑ₙ a(n)(1−cos(ω(n)h)))/h² tends to +∞ as h tends to zero through nonzero real values.

Each defect summand is between zero and 2a(n). Given any real bound, choose a finite initial sum of a(n)ω(n)² that exceeds the bound after multiplication by 2/π². For h sufficiently small, all frequencies in that finite sum satisfy |ω(n)h| ≤ π. Then 1−cos(ω(n)h) ≥ (2/π²)(ω(n)h)². Divide by h² and use the nonnegativity of every term outside the initial segment.

## References

- Truth anchor: `D5/S3/Analytic/Asymptotics/CosineSecondMoment.tendsto_cosine_defect_div_sq_atTop`
