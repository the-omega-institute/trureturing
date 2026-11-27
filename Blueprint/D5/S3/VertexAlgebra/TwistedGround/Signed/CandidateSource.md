# Signed Gaussian sources and the spatial T equation

## Abstract

Signed Gaussian sources and the spatial T equation

**Definition 1.1 (Signed source factor).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Signed/CandidateSource.h`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/Signed/CandidateSource.h` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a Boolean label e and complex u and r, h(e,u,r) is 1 − (1 − r)u for true (positive) and 1 − r − u for false (negative). Write b(u) = 1 − u for the common factor.

**Definition 1.2 (Normalized source root).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Signed/CandidateSource.W`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/Signed/CandidateSource.W` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

W(e,u,r) is h(e,u,r) times the original signed sourceMode(e,u,r). The mode sum fixes the root.

**Definition 1.3 (Signed J numerator factor).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Signed/CandidateSource.rho`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/Signed/CandidateSource.rho` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For Boolean e and f and complex u and v, ρ(e,f,u,v) equals u + v for equal labels and −(1 + uv) for mixed labels.

**Definition 1.4 (Signed T denominator factor).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Signed/CandidateSource.K`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/Signed/CandidateSource.K` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For Boolean pairs (++), (+−), (−+), (−−), respectively, K(e,f,u,v) is uv, −u, −v, or 1 in the original complex coordinates u and v.

**Definition 1.5 (Signed T denominator).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Signed/CandidateSource.E`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/Signed/CandidateSource.E` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

E(e,f,u,v,r) = b(u)b(v) − rK(e,f,u,v). In particular the negative pair uses b(u)b(v) − r.

**Definition 1.6 (Signed T numerator).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Signed/CandidateSource.N`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/Signed/CandidateSource.N` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

In the same sign order (++), (+−), (−+), (−−), N(e,f,u,v,r) is 1 + (1 − r)uv, −((1 − r)u + v), −(u + (1 − r)v), or 1 − r + uv, respectively.

**Definition 1.7 (Rational T factor).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Signed/CandidateSource.rationalT`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/Signed/CandidateSource.rationalT` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For each sign pair and complex u, v and r, the factor is rN/(2E) + r²uv/E², with N and E evaluated at (e,f,u,v,r).

**Definition 1.8 (Signed T candidate).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Signed/CandidateSource.candidateT`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/Signed/CandidateSource.candidateT` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The product of the original sourceMode(e,u,r) and sourceMode(f,v,r) multiplies the difference rationalT(e,f,u,v,r) − correction(r), where correction(r) = r(1 − r)ℓ(r) and ℓ is the logarithmic derivative of the original half-binomial period.

**Definition 1.9 (Regular signed J candidate).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Signed/CandidateSource.candidateJ`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/Signed/CandidateSource.candidateJ` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The two original sourceMode factors multiply r/4 − correction(r) + r²ρ(e,f,u,v)/(4b(u)b(v)(W(e,u,r) + W(f,v,r))²). This expression is regular on the source bidisk, including the same-sign diagonal.

**Definition 1.10 (Literal frequency coefficient).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Signed/CandidateSource.beta`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/Signed/CandidateSource.beta` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For complex u, β(e,u) equals (1 − 3u)/2 for the positive label and −(u + 1)/2 for the negative label, as in the original slice operators.

**Definition 1.11 (Signed slice operator).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Signed/CandidateSource.L`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/Signed/CandidateSource.L` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For F : ℂ → ℂ, L(e,F,u) = u b(u) deriv(F,u) + β(e,u)F(u). On slices of the original kernel it gives the corresponding literal mode derivative.

**Definition 1.12 (Signed D contribution).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Signed/CandidateSource.modeD`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/Signed/CandidateSource.modeD` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The D term is −ru/h(e,u,r) at the positive label and +ru/h(e,u,r) at the negative label. In the original mode convention, modeH(e,u,r,λ) = modeD(e,u,r) − modeA(e,u,r) − 2r modeScale(e,u)λ, with modeScale equal to 1 for true and u for false.

**Definition 1.13 (Argument of the normalized root).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Signed/CandidateSource.normalizedArgument`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/Signed/CandidateSource.normalizedArgument` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For complex u and r, the argument is 1 + ru/b(u) for the positive label and 1 − r/b(u) for the negative label. On ‖u‖ + ‖r‖ < 1 it equals h(e,u,r)/b(u) and has strictly positive real part.

**Lemma 1.14 (Signed source factor is nonzero).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Signed/CandidateSource.h_ne_zero`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/Signed/CandidateSource.h_ne_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For either Boolean e and complex u and r with ‖u‖ + ‖r‖ < 1, h(e,u,r) ≠ 0 by the corresponding branch of the original mode-factor bounds.

**Lemma 1.15 (Derivative of the original signed source).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Signed/CandidateSource.source_u`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/Signed/CandidateSource.source_u` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For either Boolean e and complex u and r with ‖u‖ + ‖r‖ < 1, the map w ↦ sourceMode(e,w,r) has complex derivative mLog(e,u,r) sourceMode(e,u,r) at u. Here mLog = 1/(2b(u)) + slope(e,r)/(2h(e,u,r)), with slope 1 − r for true and 1 for false. The proof uses the original explicit mode derivative.

**Lemma 1.16 (Signed source frequency multiplier).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Signed/CandidateSource.source_frequency`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/Signed/CandidateSource.source_frequency` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For either Boolean e and complex u and r with b(u) ≠ 0 and h(e,u,r) ≠ 0, u b(u)mLog(e,u,r) + β(e,u) = modeA(e,u,r). Substitution into the product rule recovers the original modeA coefficient.

**Lemma 1.17 (Square of the normalized source).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Signed/CandidateSource.W_square`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/Signed/CandidateSource.W_square` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For either Boolean e and complex u and r with ‖u‖ + ‖r‖ < 1, W(e,u,r)² = h(e,u,r)/b(u), using the square of the original sourceMode.

**Lemma 1.18 (Original source and root normalization).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Signed/CandidateSource.source_W_normalization`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/Signed/CandidateSource.source_W_normalization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For either Boolean e and complex u and r with ‖u‖ + ‖r‖ < 1, sourceMode(e,u,r) b(u) W(e,u,r) = 1. This identity gives the reciprocal source factors used in the J chart cancellation.

**Lemma 1.19 (The two normalized roots cannot cancel).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Signed/CandidateSource.W_sum_ne_zero`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/Signed/CandidateSource.W_sum_ne_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all Boolean e and f and complex u, v and r with ‖u‖ + ‖r‖ < 1 and ‖v‖ + ‖r‖ < 1, W(e,u,r) + W(f,v,r) ≠ 0. The original generator sum identifies each W with the principal half-power of its normalized argument by combining powers at that same base. Both roots have positive real part.

**Lemma 1.20 (Period derivative in the original source convention).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Signed/CandidateSource.ell_eq_source`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/Signed/CandidateSource.ell_eq_source` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For complex r with ‖r‖ < 1, ℓ(r) equals OriginalGaussianAllIndexResolvent.shiftedCentralDerivative(r,0)/period(r). Identify the zero-shift central series with the original period and use its existing derivative before dividing by the period.

**Lemma 1.21 (The T denominator is nonzero on the source domain).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Signed/CandidateSource.E_ne_zero`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/Signed/CandidateSource.E_ne_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all Boolean e and f and complex u, v and r with ‖u‖ + √‖r‖ < 1 and ‖v‖ + √‖r‖ < 1, E(e,f,u,v,r) ≠ 0. The sign table gives ‖K‖ ≤ 1, while each b factor has norm greater than √‖r‖. Consequently ‖rK‖ < ‖b(u)b(v)‖.

**Theorem 1.22 (Signed T displacement with the original source).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Signed/CandidateSource.candidateT_original_displacement`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/Signed/CandidateSource.candidateT_original_displacement` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all Boolean e and f, complex u and v, and real 0 < r < 1 with ‖u‖ + √r < 1 and ‖v‖ + √r < 1, set x = (r : ℂ), λ = shiftedCentralDerivative(x,0)/period(x), and C(u,v) = candidateT(e,f,u,v,x). The difference modeScale(f,v)L(e,C(·,v),u) − modeScale(e,u)L(f,C(u,·),v) equals (1 − x) sourceMode(e,u,x) sourceMode(f,v,x) [modeA(e,u,x)modeH(f,v,x,λ) − modeH(e,u,x,λ)modeA(f,v,x)]/2.

The rational differentiation gives the alternating A and D combination in that order. The period correction converts it to the alternating A and H combination with the original λ. The source inequalities give the nonzero denominators, including on the axes and diagonal.

**Lemma 1.23 (Joint analyticity of the regular J candidate).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Signed/CandidateSource.candidateJ_joint_analytic`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/Signed/CandidateSource.candidateJ_joint_analytic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all Boolean e and f and complex u, v and r with ‖u‖ + ‖r‖ < 1 and ‖v‖ + ‖r‖ < 1, the map p ↦ candidateJ(e,f,p.1,p.2,r) on ℂ × ℂ is complex analytic at (u,v). The original sources are analytic in their external coordinates, and the b factors and the normalized root sum give the required denominator bounds.

**Theorem 1.24 (Joint differentiability on the original source bidisk).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Signed/CandidateSource.candidates_original_joint_differentiable`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/Signed/CandidateSource.candidates_original_joint_differentiable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all Boolean e and f, complex u and v, and real 0 < r < 1 with ‖u‖ + √r < 1 and ‖v‖ + √r < 1, both maps p ↦ candidateJ(e,f,p.1,p.2,(r : ℂ)) and p ↦ candidateT(e,f,p.1,p.2,(r : ℂ)) are jointly complex Fréchet differentiable at (u,v), in that order in the conjunction. The inequality r ≤ √r supplies the source disks for J. Nonvanishing of E gives joint analyticity of T there as well.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Signed/CandidateSource.E`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Signed/CandidateSource.E_ne_zero`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Signed/CandidateSource.K`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Signed/CandidateSource.L`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Signed/CandidateSource.N`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Signed/CandidateSource.W`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Signed/CandidateSource.W_square`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Signed/CandidateSource.W_sum_ne_zero`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Signed/CandidateSource.beta`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Signed/CandidateSource.candidateJ`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Signed/CandidateSource.candidateJ_joint_analytic`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Signed/CandidateSource.candidateT`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Signed/CandidateSource.candidateT_original_displacement`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Signed/CandidateSource.candidates_original_joint_differentiable`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Signed/CandidateSource.ell_eq_source`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Signed/CandidateSource.h`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Signed/CandidateSource.h_ne_zero`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Signed/CandidateSource.modeD`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Signed/CandidateSource.normalizedArgument`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Signed/CandidateSource.rationalT`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Signed/CandidateSource.rho`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Signed/CandidateSource.source_W_normalization`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Signed/CandidateSource.source_frequency`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Signed/CandidateSource.source_u`
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalAnalyticCandidate](../OriginalGaussianExternalAnalyticCandidate.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalEquations](../OriginalGaussianExternalEquations.md)
