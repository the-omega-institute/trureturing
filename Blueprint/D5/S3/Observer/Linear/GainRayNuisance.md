# Trace-kernel nuisance geometry for mixed words

## Abstract

Trace-kernel nuisance geometry for mixed words

World d retains every nonzero real gain of degree at most d, every legal source, and every real drift. No individual coefficient or sampled value is required to be nonzero. The source-linear auxiliary identity places no positivity, rank or trace restriction on S.

**Theorem 1.1 (Legal sources span the auxiliary matrix space).**

Lean statement: `D5/S3/Observer/Linear/GainRayNuisance.legal_source_span`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/GainRayNuisance.legal_source_span` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The real linear span of all strictly entrywise positive rank-one trace-one 2 by 2 matrices is the whole real matrix space. The four source matrices sourceMatrix(sourceR i,sourceB i), i in Fin 4, are legal native sources: their positive chart coordinates are x=(1-sourceR i)/sourceB i and r=sourceB i/sourceR i. The determinant of their column-vectorized matrix is the existing value 1/768, so every real auxiliary matrix is their linear combination.

**Theorem 1.2 (Whole coefficients and drift split exactly).**

Lean statement: `D5/S3/Observer/Linear/GainRayNuisance.output_decomposition`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/GainRayNuisance.output_decomposition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural d, World d W, chronological word w and fixed Readout d w C, C readings(W,w) equals response(d,w,C)(W.source) W.coeff plus W.drift times C times the vector of ones. The responseMatrix has entry trace(acquisition(take i w) S) times i to the power k, for original clocks i=0,...,length(w) and coefficient indices k=0,...,d. response(d,w,C) is the source-linear matrix map S to C responseMatrix(d,w,S). scalarFunctional(d,w,C)(S) is its (0,0) entry.

**Theorem 1.3 (Affine collinearity forces zero drift and a scalar linear map).**

Lean statement: `D5/S3/Observer/Linear/GainRayNuisance.affine_collinearity_scalar`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/GainRayNuisance.affine_collinearity_scalar` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every d at least one, real linear endomorphism F of Coeff d and b:Coeff d, if for every nonzero beta and every real delta the vector F(beta)+delta*b is collinear with beta, then b=0 and F=s times the identity for some real s. This statement applies to a fixed source or to any other linear coefficient response, without a whole-source universality hypothesis. The drift argument compares delta=0 and delta=1 at a coefficient basis vector distinct from the desired output coordinate.

**Theorem 1.4 (Universal collinearity forces a source-linear scalar identity).**

Lean statement: `D5/S3/Observer/Linear/GainRayNuisance.universal_scalar_identity`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/GainRayNuisance.universal_scalar_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every d at least one, every word w and fixed matrix C, suppose that for every original World d W the output C readings(W,w) is collinear with W.coeff, allowing scalar zero. Then C times the vector of ones is zero, and for every real 2 by 2 auxiliary matrix S, response(d,w,C)(S)=scalarFunctional(d,w,C)(S) times the identity matrix of size d+1. Varying the arbitrary drift gives a common translation lying in every nonzero coefficient line. Two distinct coefficient directions force it to vanish. The pinned scalar-endomorphism theorem gives a scalar response for each legal source, and the legal-source span extends the identity to every S.

**Theorem 1.5 (An actual success has nonzero universal scale).**

Lean statement: `D5/S3/Observer/Linear/GainRayNuisance.successful_scalar_nonzero`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/GainRayNuisance.successful_scalar_nonzero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every d,w,C satisfying drift annihilation and the stated scalar identity for every auxiliary S, and every World d W at which C succeeds, scalarFunctional(d,w,C)(W.source) is nonzero. Success requires output s W.coeff for some real s not zero, with either sign. Since W.coeff is not the zero vector, a zero universal scale would contradict that success.

**Theorem 1.6 (A nonzero identity needs more reads than gain coordinates).**

Lean statement: `D5/S3/Observer/Linear/GainRayNuisance.scalar_identity_read_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/GainRayNuisance.scalar_identity_read_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural d, word w, fixed Readout d w C, auxiliary real matrix S and nonzero real s, suppose C annihilates the vector of ones and response(d,w,C)(S)=s times the identity of size d+1. Then d+2 is at most length(w)+1. The identity makes C surjective onto all d+1 coefficient coordinates. The nonzero vector of ones lies in its kernel, so rank-nullity requires one additional input coordinate.

**Theorem 1.7 (All rank-deficient short words are excluded).**

Lean statement: `D5/S3/Observer/Linear/GainRayNuisance.short_word_no_universal_success`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/GainRayNuisance.short_word_no_universal_success` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every d at least one, every word w with length(w)+1 at most d+1, and every fixed C universally collinear on all World d, C succeeds at no World d. The statement includes mixed words, pure M words, pure J words and the empty action word, with the initial read included. This rank argument applies through d+1 reads.

ChartPolynomial d is the real multivariate polynomial ring with d+4 variables. The coordinate order is x,r,beta(0),...,beta(d),delta. The source denominator is D=1+x*r, positive on the chart. For a real matrix A the trace numerator is A00+A01*x+A10*r+A11*x*r. The polynomial for read i is that numerator times the ordinary gain sum over k of beta(k)*i^k, plus delta*D. The output polynomial is the fixed C-weighted sum of these read polynomials. chartWedge uses beta(j) times output(k) minus beta(k) times output(j). These definitions use the same source, whole gain and drift at every clock.

**Theorem 1.8 (The cleared wedge is the native output wedge).**

Lean statement: `D5/S3/Observer/Linear/GainRayNuisance.eval_chart_wedge`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/GainRayNuisance.eval_chart_wedge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every d,w,C, positive real x,r, nonzero beta:Coeff d, arbitrary drift delta, and j,k in Fin(d+1), evaluation of chartWedge(d,w,C,j,k) at chartParameters(d,x,r,beta,delta) equals (1+x*r) times [beta(j) times (C readings(chartWorld(d,x,r,beta,delta),w))(k) minus beta(k) times that output at j]. Each read uses acquisition(take i w) and the literal clock i, including i=0.

**Theorem 1.9 (Nonzero polynomial witnesses exactly nonuniversal collinearity).**

Lean statement: `D5/S3/Observer/Linear/GainRayNuisance.chart_wedge_nonzero_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/GainRayNuisance.chart_wedge_nonzero_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural d, word w and fixed C, some chartWedge(d,w,C,j,k) is a nonzero polynomial if and only if it is false that C readings(W,w) is collinear with W.coeff at every original World d W. This is an equivalence on the entire source and gain domain. The reverse source chart is exact. A nonzero coefficient vector is collinear with an output precisely when all its coordinate wedges vanish. To obtain a polynomial identity from universal collinearity, evaluate on the product domain x>0,r>0 with all coefficient and drift coordinates arbitrary; at the zero coefficient vector each wedge also vanishes algebraically.

**Theorem 1.10 (Each actual successful output satisfies every wedge equation).**

Lean statement: `D5/S3/Observer/Linear/GainRayNuisance.success_chart_wedge_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/GainRayNuisance.success_chart_wedge_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every d,w,C, positive x,r, nonzero whole coefficient vector beta, arbitrary delta and j,k in Fin(d+1), if C succeeds at chartWorld(d,x,r,beta,delta), evaluation of chartWedge(d,w,C,j,k) at those coordinates is zero. The success scale can be any nonzero real, of either sign. Sampled roots, lower actual degree, repeated roots and arbitrary drift are included.

**Theorem 1.11 (A nonuniversal readout has an explicit nonzero success polynomial).**

Lean statement: `D5/S3/Observer/Linear/GainRayNuisance.chart_success_certificate`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/GainRayNuisance.chart_success_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every d,w,C failing whole-domain universal collinearity, there exist j,k in Fin(d+1) such that chartWedge(d,w,C,j,k) is nonzero, its evaluation vanishes at every positive-chart world where C succeeds, and its evaluation is nonzero for Lebesgue-almost every ambient coordinate vector in Fin(d+4) to the reals. Almost-everywhere nonvanishing is the direct application of GenericLieLength.ae_mvPolynomial_ne_zero to this polynomial. This ambient statement alone asserts no result about substitution into a prescribed-history fiber.

**Theorem 1.12 (A common source in the actual scalar kernel).**

Lean statement: `D5/S3/Observer/Linear/GainRayNuisance.scalar_kernel_source`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/GainRayNuisance.scalar_kernel_source` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural d, chronological Boolean word w and fixed Readout d w C whose scalarFunctional is nonzero, scalarRepresentative is nonzero and represents that functional by the trace pairing on every real auxiliary matrix. There is one auxiliary S in its kernel such that, simultaneously at every original prefix i in Fin(length(w)+1), trace(acquisition(take i w)*S) is zero if and only if that cumulative matrix is a real scalar multiple of scalarRepresentative. The representative is the weighted sum of the actual cumulative matrices with weights C(0,i). Trace-pairing extensionality identifies the vanishing restrictions, and finite hyperplane avoidance supplies the simultaneous S. Auxiliary matrices here have no physical positivity requirement.

**Theorem 1.13 (The exact rank with arbitrary vanishing weights).**

Lean statement: `D5/S3/Observer/Linear/GainRayNuisance.weighted_evaluation_rank`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/GainRayNuisance.weighted_evaluation_rank` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural d,n, injective real nodes t indexed by Fin n, and arbitrary real weights a indexed by Fin n, the matrix with entries a(i)*t(i)^k for k in Fin(d+1) has rank min(number of nonzero weights,d+1). The zero-support and rank-deficient cases are included. Select that many nonzero rows. Distinct-node interpolation, followed by division by the selected nonzero weights, makes the restricted evaluation onto. The number of supported rows and the whole coefficient dimension give the matching upper bounds.

**Theorem 1.14 (The exact twice-dimension kernel equality).**

Lean statement: `D5/S3/Observer/Linear/GainRayNuisance.scalar_kernel_endpoint`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/GainRayNuisance.scalar_kernel_endpoint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural d, word w, fixed C, and nonzero real linear functional ell on the full auxiliary matrix space, suppose response(T)=ell(T)*I for every auxiliary T and length(w)+1 is at most 2(d+1). If S belongs to ker ell and every actual cumulative trace at S is nonzero, then length(w)+1 equals 2(d+1) and ker C is exactly the image of responseMatrix(S). A nonzero scalar response makes C onto. The weighted evaluation image has dimension d+1 and lies in its kernel, so rank-nullity forces both equalities.

**Theorem 1.15 (Every endpoint ratio diagonal is scalar).**

Lean statement: `D5/S3/Observer/Linear/GainRayNuisance.scalar_kernel_ratios`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/GainRayNuisance.scalar_kernel_ratios` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the endpoint hypotheses with d at least one, for every T in ker ell and every two original prefix indices i,j, the ratios trace(A_i*T)/trace(A_i*S) and trace(A_j*T)/trace(A_j*S) coincide. Indeed, kernel equality shows that multiplying any degree-at-most-d evaluation vector by these ratios again gives such an evaluation vector. Diagonal evaluation rigidity then applies, including when one or every numerator vanishes. No invertibility of the ratio diagonal is assumed.

**Theorem 1.16 (The actual cumulative matrix span has dimension at most two).**

Lean statement: `D5/S3/Observer/Linear/GainRayNuisance.scalar_kernel_span_le_two`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/GainRayNuisance.scalar_kernel_span_le_two` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every d at least one, word w and C with nonzero scalarFunctional, the universal scalar response identity and a scalar-kernel S with every cumulative trace nonzero imply that the span of all initial-inclusive cumulative matrices has dimension at most two when the read count is at most 2(d+1). The ratio law makes each trace functional, restricted to the scalar kernel, proportional to the initial trace functional. Subtracting that multiple gives a functional vanishing on the scalar kernel, hence a multiple of the scalarFunctional itself. Trace-pairing extensionality places each actual matrix in the span of the initial matrix and scalarRepresentative.

**Theorem 1.17 (Every mixed word is obstructed through 2(d+1) reads).**

Lean statement: `D5/S3/Observer/Linear/GainRayNuisance.mixed_scalar_obstruction`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/GainRayNuisance.mixed_scalar_obstruction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every d at least one and every chronological Boolean word w containing both M=false and J=true, with initial-inclusive read count at most 2(d+1), any fixed C which annihilates the constant drift and satisfies response(T)=scalarFunctional(T)*I for every auxiliary real matrix T has scalarFunctional equal to zero. Choose a scalar-kernel S realizing precisely the proportionality-class zeros. If there is a zero trace, the nuisance image misses the all-ones drift vector, and its exact rank and the bound on the proportionality-class size contradict rank-nullity. If there are no zero traces, the endpoint argument bounds the cumulative span by two, whereas every mixed word has span at least three. Both switch orientations and every first-switch location are included.

**Theorem 1.18 (An actual success supplies a nonzero chart certificate).**

Lean statement: `D5/S3/Observer/Linear/GainRayNuisance.mixed_chart_success_certificate`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/GainRayNuisance.mixed_chart_success_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every d at least one, every mixed word with at most 2(d+1) initial-inclusive reads, every fixed C and every native world W where C succeeds with a nonzero scale of either sign, there are coefficient indices j,k such that chartWedge(C,j,k) is a nonzero polynomial. At every legal positive chart point, every actual success of that same C lies in its zero set; the polynomial is nonzero almost everywhere in the ambient real chart coordinate space. If all wedges vanished identically, whole-domain collinearity would give the scalar identity and the actual success would force its scalarFunctional to be nonzero, contrary to the mixed obstruction. This ambient certificate makes no assertion about nonvanishing after substitution on a prescribed-history fiber.

**Theorem 1.19 (Whole-vector collinearity from all coordinate wedges).**

Lean statement: `D5/S3/Observer/Linear/GainRayNuisance.collinear_of_wedges`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/GainRayNuisance.collinear_of_wedges` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a nonzero ordinary coefficient vector, vanishing of every output wedge supplies one common real scalar, allowing zero only in collinearity.

## References

- Truth anchor: `D5/S3/Observer/Linear/GainRayNuisance.affine_collinearity_scalar`
- Truth anchor: `D5/S3/Observer/Linear/GainRayNuisance.chart_success_certificate`
- Truth anchor: `D5/S3/Observer/Linear/GainRayNuisance.chart_wedge_nonzero_iff`
- Truth anchor: `D5/S3/Observer/Linear/GainRayNuisance.collinear_of_wedges`
- Truth anchor: `D5/S3/Observer/Linear/GainRayNuisance.eval_chart_wedge`
- Truth anchor: `D5/S3/Observer/Linear/GainRayNuisance.legal_source_span`
- Truth anchor: `D5/S3/Observer/Linear/GainRayNuisance.mixed_chart_success_certificate`
- Truth anchor: `D5/S3/Observer/Linear/GainRayNuisance.mixed_scalar_obstruction`
- Truth anchor: `D5/S3/Observer/Linear/GainRayNuisance.output_decomposition`
- Truth anchor: `D5/S3/Observer/Linear/GainRayNuisance.scalar_identity_read_bound`
- Truth anchor: `D5/S3/Observer/Linear/GainRayNuisance.scalar_kernel_endpoint`
- Truth anchor: `D5/S3/Observer/Linear/GainRayNuisance.scalar_kernel_ratios`
- Truth anchor: `D5/S3/Observer/Linear/GainRayNuisance.scalar_kernel_source`
- Truth anchor: `D5/S3/Observer/Linear/GainRayNuisance.scalar_kernel_span_le_two`
- Truth anchor: `D5/S3/Observer/Linear/GainRayNuisance.short_word_no_universal_success`
- Truth anchor: `D5/S3/Observer/Linear/GainRayNuisance.success_chart_wedge_zero`
- Truth anchor: `D5/S3/Observer/Linear/GainRayNuisance.successful_scalar_nonzero`
- Truth anchor: `D5/S3/Observer/Linear/GainRayNuisance.universal_scalar_identity`
- Truth anchor: `D5/S3/Observer/Linear/GainRayNuisance.weighted_evaluation_rank`
- Dependency: [D5/S3/Observer/CubicGain/FullWorldMeanSpan](../CubicGain/FullWorldMeanSpan.md)
- Dependency: [D5/S3/Observer/Linear/GainRayHistory](GainRayHistory.md)
- Dependency: [D5/S3/Observer/Linear/GainRayMixedGeometry](GainRayMixedGeometry.md)
- Dependency: [D5/S3/Observer/Linear/GainRayWordGeometry](GainRayWordGeometry.md)
- Dependency: [D5/S3/Quantum/Algebra/GenericLieLength](../../Quantum/Algebra/GenericLieLength.md)
