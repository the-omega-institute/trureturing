# Signed J chart regularization and spatial displacement

## Abstract

Signed J chart regularization and spatial displacement

**Definition 1.1 (Signed chart denominator).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Signed/JSpatial.G`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/Signed/JSpatial.G` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For Boolean labels e and f and complex u and v, G(e,f,u,v) is u − v for equal labels and 1 − uv for mixed labels.

**Definition 1.2 (Rational J factor).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Signed/JSpatial.rationalJ`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/Signed/JSpatial.rationalJ` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For Boolean e and f and complex u, v and r, rationalJ equals Qconstant(e,f,r) + jN(e,f,u,v,r)/(2G(e,f,u,v)²). The offset is 0 for (++), and r/2 for the other three sign pairs. The numerator jN is u h(e,u,r)b(v) + v b(u)h(f,v,r) for equal labels. For (+−) it is −(h(e,u,r)b(v) + uv b(u)h(f,v,r)), and for (−+) it is −(uv h(e,u,r)b(v) + b(u)h(f,v,r)).

**Definition 1.3 (Signed Cauchy subtraction).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Signed/JSpatial.cauchy`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/Signed/JSpatial.cauchy` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For Boolean e and f and complex u and v, cauchy(e,f,u,v) is ρ(e,f,u,v)/(2G(e,f,u,v)²). Its numerator is u + v for equal labels and −(1 + uv) for mixed labels.

**Definition 1.4 (J expressed in the rational chart).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Signed/JSpatial.chartJ`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/Signed/JSpatial.chartJ` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The chart evaluates the product of the two original signed sources times the difference rationalJ(e,f,u,v,r) − correction(r), then subtracts cauchy(e,f,u,v). On ‖u‖ + ‖r‖ < 1 and ‖v‖ + ‖r‖ < 1 with G ≠ 0, the root-square and source normalization identities reduce this expression to the regular candidateJ.

**Theorem 1.5 (Signed J displacement with the original source).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Signed/JSpatial.candidateJ_original_displacement`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/Signed/JSpatial.candidateJ_original_displacement` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all Boolean e and f, complex u and v, and real 0 < r < 1 with ‖u‖ + √r < 1 and ‖v‖ + √r < 1, set x = (r : ℂ), λ = shiftedCentralDerivative(x,0)/period(x), and C(u,v) = candidateJ(e,f,u,v,x). The sum modeScale(f,v)L(e,C(·,v),u) + modeScale(e,u)L(f,C(u,·),v) equals (1 − x) sourceMode(e,u,x) sourceMode(f,v,x) [modeA(e,u,x)modeH(f,v,x,λ) + modeH(e,u,x,λ)modeA(f,v,x)]/2 + modeB(e)modeB(f).

Off the chart pole, the rational derivative gives A(e)D(f) + D(e)A(f) − 2A(e)A(f), with the D factor −ru/h(e,u,r) for the positive label and +ru/h(e,u,r) for the negative label. The period correction converts this to the A and H sum. The spatial operator on cauchy gives −modeB(e)modeB(f), so the subtraction contributes +modeB(e)modeB(f). This is 1/4 for equal labels and −1/4 for mixed labels.

For mixed labels, ‖uv‖ < 1 excludes chart poles. For equal labels, joint analyticity of the regular candidate makes its two complex partial derivatives continuous at u = v. With the second coordinate fixed, the equation extends to the diagonal by continuity from the punctured first-coordinate disk.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Signed/JSpatial.G`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Signed/JSpatial.candidateJ_original_displacement`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Signed/JSpatial.cauchy`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Signed/JSpatial.chartJ`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Signed/JSpatial.rationalJ`
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/Signed/CandidateSource](CandidateSource.md)
