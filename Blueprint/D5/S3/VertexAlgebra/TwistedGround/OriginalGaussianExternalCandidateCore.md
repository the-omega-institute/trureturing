# Rational Core of the Signed Gaussian Candidate

## Abstract

Rational Core of the Signed Gaussian Candidate

These are algebraic identities for the rational part of the candidate kernel. Its analytic square-root factors and its identification with the complete original J/T mode generators remain to be established.

**Definition 1.1 (nPoly).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalCandidateCore.nPoly`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalCandidateCore.nPoly` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For complex x,t,s, the numerator is t*s*(t+s) - 2*(2-x)*t*s + (1-x)*(t+s).

**Definition 1.2 (qPoly).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalCandidateCore.qPoly`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalCandidateCore.qPoly` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The rational core divides nPoly by 2*(t-s)^2. This uses total complex division; identities interpreting the quotient away from the diagonal carry explicit nonzero assumptions.

**Theorem 1.3 (nPoly_comm).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalCandidateCore.nPoly_comm`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalCandidateCore.nPoly_comm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every complex x,t,s, exchanging t and s preserves the numerator.

**Theorem 1.4 (nPoly_diagonal).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalCandidateCore.nPoly_diagonal`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalCandidateCore.nPoly_diagonal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every complex x,t, the diagonal numerator is 2*t*(t-1)*(t-(1-x)).

**Theorem 1.5 (nPoly_sub_diagonal_factor).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalCandidateCore.nPoly_sub_diagonal_factor`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalCandidateCore.nPoly_sub_diagonal_factor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every complex x,t,s, subtracting nPoly x s s from nPoly x t s gives (t-s)*(s*t+2*s^2-2*(2-x)*s+(1-x)), without dividing by t-s.

**Theorem 1.6 (nPoly_first_diagonal).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalCandidateCore.nPoly_first_diagonal`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalCandidateCore.nPoly_first_diagonal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every complex x,s, the diagonal value of the preceding factor normalizes to 3*s^2-2*(2-x)*s+(1-x).

**Theorem 1.7 (nPoly_source_curve).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalCandidateCore.nPoly_source_curve`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalCandidateCore.nPoly_source_curve` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every complex x,t,s, the same numerator has the source-curve form t*s*(t+s)-2*(1+(1-x))*t*s+(1-x)*(t+s).

**Definition 1.8 (rightChart).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalCandidateCore.rightChart`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalCandidateCore.rightChart` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The right chart sends u to 1/u for true and to u for false.

**Definition 1.9 (leftChart).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalCandidateCore.leftChart`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalCandidateCore.leftChart` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The left chart sends u to (1-(1-x)*u)/(1-u) for true and to ((1-x)-u)/(1-u) for false.

**Theorem 1.10 (complementary_kernel_reflection).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalCandidateCore.complementary_kernel_reflection`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalCandidateCore.complementary_kernel_reflection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For complex x,t,s with t distinct from s, qPoly x t s plus qPoly (1-x) (1-t) (1-s) equals one half.

Each chart-reflection theorem below assumes x is nonzero, 1-u and 1-v are nonzero, and both the right-chart pair and the left-chart pair are distinct. It also assumes u is nonzero when its sign is true and v is nonzero when its sign is true.

**Theorem 1.11 (reflected_positive_positive).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalCandidateCore.reflected_positive_positive`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalCandidateCore.reflected_positive_positive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the stated chart-domain assumptions with both signs true, evaluating qPoly on the two left charts equals evaluating it on the two right charts.

**Theorem 1.12 (reflected_negative_negative).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalCandidateCore.reflected_negative_negative`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalCandidateCore.reflected_negative_negative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the stated chart-domain assumptions with both signs false, evaluating qPoly on the two left charts equals evaluating it on the two right charts.

**Theorem 1.13 (reflected_positive_negative).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalCandidateCore.reflected_positive_negative`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalCandidateCore.reflected_positive_negative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the stated chart-domain assumptions with signs true and false, evaluating qPoly on the two left charts equals evaluating it on the two right charts.

**Theorem 1.14 (reflected_negative_positive).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalCandidateCore.reflected_negative_positive`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalCandidateCore.reflected_negative_positive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the stated chart-domain assumptions with signs false and true, evaluating qPoly on the two left charts equals evaluating it on the two right charts.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalCandidateCore.complementary_kernel_reflection`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalCandidateCore.leftChart`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalCandidateCore.nPoly`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalCandidateCore.nPoly_comm`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalCandidateCore.nPoly_diagonal`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalCandidateCore.nPoly_first_diagonal`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalCandidateCore.nPoly_source_curve`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalCandidateCore.nPoly_sub_diagonal_factor`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalCandidateCore.qPoly`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalCandidateCore.reflected_negative_negative`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalCandidateCore.reflected_negative_positive`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalCandidateCore.reflected_positive_negative`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalCandidateCore.reflected_positive_positive`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalCandidateCore.rightChart`
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalRadialSums](OriginalGaussianExternalRadialSums.md)
