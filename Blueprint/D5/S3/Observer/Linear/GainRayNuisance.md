# Trace-kernel nuisance geometry for mixed words

## Abstract

Trace-kernel nuisance geometry for mixed words

**Theorem 1.1 (A common source in the actual scalar kernel).**

Lean statement: `D5/S3/Observer/Linear/GainRayNuisance.scalar_kernel_source`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/GainRayNuisance.scalar_kernel_source` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural d, chronological Boolean word w and fixed Readout d w C whose scalarFunctional is nonzero, scalarRepresentative is nonzero and represents that functional by the trace pairing on every real auxiliary matrix. There is one auxiliary S in its kernel such that, simultaneously at every original prefix i in Fin(length(w)+1), trace(acquisition(take i w)*S) is zero if and only if that cumulative matrix is a real scalar multiple of scalarRepresentative. The representative is the weighted sum of the actual cumulative matrices with weights C(0,i). Trace-pairing extensionality identifies the vanishing restrictions, and finite hyperplane avoidance supplies the simultaneous S. Auxiliary matrices here have no physical positivity requirement.

**Theorem 1.2 (The exact rank with arbitrary vanishing weights).**

Lean statement: `D5/S3/Observer/Linear/GainRayNuisance.weighted_evaluation_rank`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/GainRayNuisance.weighted_evaluation_rank` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural d,n, injective real nodes t indexed by Fin n, and arbitrary real weights a indexed by Fin n, the matrix with entries a(i)*t(i)^k for k in Fin(d+1) has rank min(number of nonzero weights,d+1). The zero-support and rank-deficient cases are included. Select that many nonzero rows. Distinct-node interpolation, followed by division by the selected nonzero weights, makes the restricted evaluation onto. The number of supported rows and the whole coefficient dimension give the matching upper bounds.

**Theorem 1.3 (The exact twice-dimension kernel equality).**

Lean statement: `D5/S3/Observer/Linear/GainRayNuisance.scalar_kernel_endpoint`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/GainRayNuisance.scalar_kernel_endpoint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural d, word w, fixed C, and nonzero real linear functional ell on the full auxiliary matrix space, suppose response(T)=ell(T)*I for every auxiliary T and length(w)+1 is at most 2(d+1). If S belongs to ker ell and every actual cumulative trace at S is nonzero, then length(w)+1 equals 2(d+1) and ker C is exactly the image of responseMatrix(S). A nonzero scalar response makes C onto. The weighted evaluation image has dimension d+1 and lies in its kernel, so rank-nullity forces both equalities.

**Theorem 1.4 (Every endpoint ratio diagonal is scalar).**

Lean statement: `D5/S3/Observer/Linear/GainRayNuisance.scalar_kernel_ratios`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/GainRayNuisance.scalar_kernel_ratios` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the endpoint hypotheses with d at least one, for every T in ker ell and every two original prefix indices i,j, the ratios trace(A_i*T)/trace(A_i*S) and trace(A_j*T)/trace(A_j*S) coincide. Indeed, kernel equality shows that multiplying any degree-at-most-d evaluation vector by these ratios again gives such an evaluation vector. Diagonal evaluation rigidity then applies, including when one or every numerator vanishes. No invertibility of the ratio diagonal is assumed.

**Theorem 1.5 (The actual cumulative matrix span has dimension at most two).**

Lean statement: `D5/S3/Observer/Linear/GainRayNuisance.scalar_kernel_span_le_two`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/GainRayNuisance.scalar_kernel_span_le_two` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every d at least one, word w and C with nonzero scalarFunctional, the universal scalar response identity and a scalar-kernel S with every cumulative trace nonzero imply that the span of all initial-inclusive cumulative matrices has dimension at most two when the read count is at most 2(d+1). The ratio law makes each trace functional, restricted to the scalar kernel, proportional to the initial trace functional. Subtracting that multiple gives a functional vanishing on the scalar kernel, hence a multiple of the scalarFunctional itself. Trace-pairing extensionality places each actual matrix in the span of the initial matrix and scalarRepresentative.

**Theorem 1.6 (Every mixed word is obstructed through 2(d+1) reads).**

Lean statement: `D5/S3/Observer/Linear/GainRayNuisance.mixed_scalar_obstruction`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/GainRayNuisance.mixed_scalar_obstruction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every d at least one and every chronological Boolean word w containing both M=false and J=true, with initial-inclusive read count at most 2(d+1), any fixed C which annihilates the constant drift and satisfies response(T)=scalarFunctional(T)*I for every auxiliary real matrix T has scalarFunctional equal to zero. Choose a scalar-kernel S realizing precisely the proportionality-class zeros. If there is a zero trace, the nuisance image misses the all-ones drift vector, and its exact rank and the bound on the proportionality-class size contradict rank-nullity. If there are no zero traces, the endpoint argument bounds the cumulative span by two, whereas every mixed word has span at least three. Both switch orientations and every first-switch location are included.

**Theorem 1.7 (An actual success supplies a nonzero chart certificate).**

Lean statement: `D5/S3/Observer/Linear/GainRayNuisance.mixed_chart_success_certificate`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/GainRayNuisance.mixed_chart_success_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every d at least one, every mixed word with at most 2(d+1) initial-inclusive reads, every fixed C and every native world W where C succeeds with a nonzero scale of either sign, there are coefficient indices j,k such that chartWedge(C,j,k) is a nonzero polynomial. At every legal positive chart point, every actual success of that same C lies in its zero set; the polynomial is nonzero almost everywhere in the ambient real chart coordinate space. If all wedges vanished identically, whole-domain collinearity would give the scalar identity and the actual success would force its scalarFunctional to be nonzero, contrary to the mixed obstruction. This ambient certificate makes no assertion about nonvanishing after substitution on a prescribed-history fiber.

## References

- Truth anchor: `D5/S3/Observer/Linear/GainRayNuisance.mixed_chart_success_certificate`
- Truth anchor: `D5/S3/Observer/Linear/GainRayNuisance.mixed_scalar_obstruction`
- Truth anchor: `D5/S3/Observer/Linear/GainRayNuisance.scalar_kernel_endpoint`
- Truth anchor: `D5/S3/Observer/Linear/GainRayNuisance.scalar_kernel_ratios`
- Truth anchor: `D5/S3/Observer/Linear/GainRayNuisance.scalar_kernel_source`
- Truth anchor: `D5/S3/Observer/Linear/GainRayNuisance.scalar_kernel_span_le_two`
- Truth anchor: `D5/S3/Observer/Linear/GainRayNuisance.weighted_evaluation_rank`
- Dependency: [D5/S3/Observer/Linear/GainRayMixedGeometry](GainRayMixedGeometry.md)
- Dependency: [D5/S3/Observer/Linear/GainRayScalarIdentity](GainRayScalarIdentity.md)
- Dependency: [D5/S3/Observer/Linear/GainRayShortWord](GainRayShortWord.md)
- Dependency: [D5/S3/Observer/Linear/GainRaySuccessPolynomial](GainRaySuccessPolynomial.md)
- Dependency: [D5/S3/Observer/Linear/GainRayWordGeometry](GainRayWordGeometry.md)
