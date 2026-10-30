# Finite scalar lattice numerators

## Abstract

Finite scalar common numerators of the actual canonical lattice fields.

Let D be arbitrary integral symmetric even lattice data. Fix a complex matrix J satisfying J times gramComplex(D) equals the identity and gramComplex(D) times J equals the identity. The charges alpha, beta and gamma, and the four external oscillator polynomials u, v, w and p, are arbitrary. The form may be indefinite. Each field coefficient is the original canonical lattice coefficient, including its original cocycle and the convention that exponent a corresponds to mode -a-1.

**Theorem 1.1 (Energy support of the actual double coefficient).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeSectorScalarNumerator.actual_product_coefficient_energy_le`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sectors/LatticeSectorScalarNumerator.actual_product_coefficient_energy_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Write h(eta) for chargeEnergy(D,eta) and e(T) for oscillatorEnergy(T). If the T coefficient of canonical(D,alpha,beta+gamma,u,m,canonical(D,beta,gamma,v,n,w)) is nonzero, then h(alpha)+h(beta)+h(gamma)-m-n-2 is at most h(alpha+(beta+gamma))+e(T). Finite induction in the three oscillator polynomials reduces the assertion to monomials. Actual mode grading applies twice to their included carrier states; their three nonnegative oscillator energies give the lower bound. All integer modes and mixed-energy polynomials are retained.

**Definition 1.2 (Factorial linear test functional).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeSectorScalarNumerator.readout`

*Formalization.* `D5/S3/VertexAlgebra/Sectors/LatticeSectorScalarNumerator.readout` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a fixed p, readout(D,p)(t) is exactly FactorialFockMetric.inner(p,t), constructed from the existing Hilbert embedding and the inner product linear in its second argument. It is a complex-linear map on t; no multiplicative map or invariant BPZ form is asserted.

**Definition 1.3 (Finite test energy).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeSectorScalarNumerator.testEnergy`

*Formalization.* `D5/S3/VertexAlgebra/Sectors/LatticeSectorScalarNumerator.testEnergy` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The maximum of e(T) over the finite monomial support of p, with value zero for empty support. This remains defined for the zero test polynomial.

**Definition 1.4 (Signed total-degree cutoff).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeSectorScalarNumerator.degreeBound`

*Formalization.* `D5/S3/VertexAlgebra/Sectors/LatticeSectorScalarNumerator.degreeBound` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For natural clearing shifts A,B,N, put S=A+B+N, Lp=testEnergy(D,p) and delta=alpha+(beta+gamma). The integer degreeBound is K=S+Lp+h(delta)-h(alpha)-h(beta)-h(gamma). No charge-energy positivity is required.

**Theorem 1.5 (Finite scalar coefficient support).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeSectorScalarNumerator.scalar_numerator_support`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sectors/LatticeSectorScalarNumerator.scalar_numerator_support` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Suppose P is a vector power series whose zero extension is the actual cleared product with shifts a-A,b-B and clearing exponent N. For every p and every bivariate natural index d, a nonzero coefficient of mapSeries(readout(D,p),P) implies degree(d)<=K. At d=(i,j), clearing index k gives outer mode A+N-k-i-1 and inner mode B+k-j-1. Their sum cancels k exactly. The double-coefficient energy bound and the finite factorial coordinate expansion of p force the stated cutoff, without any locality or truncation assertion for individual homogeneous components.

**Theorem 1.6 (Unique finite common scalar numerator).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeSectorScalarNumerator.ordinary_actual_finite_scalar_numerator`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sectors/LatticeSectorScalarNumerator.ordinary_actual_finite_scalar_numerator` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

First choose N from ordinary_actual_cleared_channel_transport for D,alpha,beta,u,v. It retains actual locality and the u-on-v truncation bound and is independent of gamma,w,p. For each gamma,w choose A,B and the same common vector power series P, retaining both original input truncation bounds and all three vector channel equations; these choices precede p. For every p there is a unique polynomial R in two variables over the complex numbers whose power-series coercion is mapSeries(readout(D,p),P). Its total degree is at most K.toNat, equivalently its integer total degree is at most max(0,K). If K<0, both the tested series and R vanish. Applying the linear readout to the two original cleared ordered products gives the zero extension of that same R at a,b, with the original shifts a-A,b-B. Applying it to clearIterate(N,A,B) of the original iterate gives the zero extension of collision(R), namely substitution x=t+y,y=y. Polynomial extraction is exact coefficientwise truncTotal(K.toNat+1), justified by the support theorem; uniqueness uses injectivity of polynomial coercion.

**Theorem 1.7 (Lower energy of arbitrary actual words).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeSectorScalarNumerator.actual_word_coefficient_energy_le`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sectors/LatticeSectorScalarNumerator.actual_word_coefficient_energy_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary finite n, labelled charges c(i), oscillator states s(i), initial charge delta and oscillator w, put A(i)=Y(D,inclusion(D,c(i),s(i))). For every list l of labels, signed mode exponents e, and output label (rho,T), a nonzero coefficient of word(A,l,e)(inclusion(D,delta,w)) implies h(delta)+sum over i in l of (h(c(i))+e(i)) <= h(rho)+oscillatorEnergy(T). Labels and field values may repeat, l may be empty, and n may be zero. The proof inducts on the list length, retaining the complete suffix lower bound. Both the head state and the suffix output are finite sums of their actual grade projections. Every energy appearing in either sum is at least its corresponding lower bound. actual_mode_grade puts each homogeneous pair in grade m+n-q-1; mem_grade_iff excludes every coefficient below the accumulated bound. Reassembly preserves the bound even when coefficients cancel. No positivity, finite-dimensional grade, homogeneous-input or vacuum premise is used.

**Definition 1.8 (Arbitrary-word scalar cutoff).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeSectorScalarNumerator.wordDegreeBound`

*Formalization.* `D5/S3/VertexAlgebra/Sectors/LatticeSectorScalarNumerator.wordDegreeBound` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Put chi=(sum_i c(i))+delta. For the supplier's k,a and test p define K=sum_i a(i)+k*card(labelledPairs(n))+testEnergy(D,p)+h(chi)-h(delta)-sum_i h(c(i)), with all terms interpreted as integers. At n=2 the pair contribution is k and this agrees with degreeBound after identifying the two shifts and associating the charges. At n=3 the pair contribution is 3*k.

**Theorem 1.9 (Degree support of the same supplied series).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeSectorScalarNumerator.actual_word_scalar_numerator_support`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sectors/LatticeSectorScalarNumerator.actual_word_scalar_numerator_support` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let the complete identity order be List.ofFn(id). Assume precisely its signed cleared identity for an actual Carrier-valued power series P, with k and a fixed. Set phi=readout(D,p) composed with projection(D,chi) and S(d)=phi(P(d)). Then S(d) nonzero implies integer degree(d)<=K. The arbitrary-word lower-energy invariant bounds every monomial coefficient tested by p, whose energy is at most testEnergy(D,p). Each factor z_i-z_j shifts total exponent by one; its kth power shifts it by k. Thus every term of the clearing product has total degree k*card(labelledPairs(n)), including when the product is empty. Finite difference and product induction propagate the scalar upper cutoff, cancelling every clearing monomial shift against that degree. The generally infinite vector P is retained; no finite-vector-numerator premise is introduced.

**Theorem 1.10 (Finite scalar common numerator for every finite word).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeSectorScalarNumerator.ordinary_actual_word_finite_scalar_numerator`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sectors/LatticeSectorScalarNumerator.ordinary_actual_word_finite_scalar_numerator` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary n,D,J with both inverse-Gram equations and all labelled charges and oscillator states, actual state-field locality supplies k before delta,w. Apply ungraded_local_word_common_series to the complete nodup identity order to obtain the original a and generally infinite Carrier-valued P before p. Retain every original input truncation and all signed permutation clearing identities. For each arbitrary p, S(d)=readout(D,p)(projection(D,chi)(P(d))) has degree support at most K and is the power-series coercion of a unique complex multivariate polynomial R. Its totalDegree is at most K.toNat; K<0 forces S=0 and R=0. The scalar cleared identity with this same R holds for every permutation and every signed exponent. Exact truncTotal(K.toNat+1) extracts R and polynomial coercion proves uniqueness. Zero states, inhomogeneous states, repeated fields, n=0 and the empty word are included. The original n-word common vector series therefore becomes a finite scalar numerator, including the existing three-field and four-field channel carriers. Native rational evaluation and sewing comparisons may use this finite scalar input; no occupation-fiber identification, BPZ invariance, operator convergence or full CFT realization is concluded.

The scalar support argument and finite numerator construction extend the repository's actual-channel results. The existing Bakalov--Kac, Matsuo--Nagatomo and Carnahan attributions remain in the field suppliers, and Mathlib retains its authorship and Apache license for finite polynomial induction, power-series truncation and coercion. No external-literature novelty is claimed. The existing sewing module supplies the finite factorial coordinate expansion. Its arbitrary-D occupation-summability theorem retains its original unrestricted hypotheses.

As a derived product/reverse application of ordinary_actual_finite_scalar_numerator, fix its original witness order: N before gamma,w, then A,B,P before p, and the unique R for p. Let chi=alpha+(beta+gamma) and phi=readout(D,p) composed with projection(D,chi). Use the original modes -a-1 and -b-1, and the literal product and reverseProduct coefficients; inclusion_canonical identifies them with the corresponding actual carrier words. In the native labelled Laurent ring let L=X^(-A)Y^(-B)R and Q=L/(X-Y)^N, with fixed labels X,Y. Finite convolution is exactly the original clear binomial sum, natural-to-signed coefficient inclusion preserves its indices, and supported Hahn cancellation identifies both ordered expansions of Q. CollisionAbsoluteEvaluation.Labelled.collision_absolute_evaluation, with SupportedWordRationalCollision's ordered polynomial and rational embeddings, gives the following evaluation. For nonzero complex x,y in norm(y)<norm(x), the full signed product scalar series has Summable norms and HasSum equal to eval(R)(x,y)/(x^A*y^B*(x-y)^N). In norm(x)<norm(y), the full signed reverse-product scalar series has the same properties and value, with no additional sign. In either strict chamber the sum of norms is at most laurentMajorant(L,(x,y))*abs(norm(x)-norm(y))^(-N), where the native laurentMajorant is the finite sum of norm(L_e*x^(e_0)*y^(e_1)) over the Laurent support. This is an application of the finite numerator and existing analytic evaluation, separate from the scope of the named finite-numerator statements.

Zero and inhomogeneous external polynomials are included. Singular Gram forms require a separate grading argument. The named numerator theorems are formal coefficient identities; beyond the derived strict-chamber scalar application, operator convergence, invariant BPZ pairings, CFT sewing, Monster realization, anomalies, string theory and AdS/CFT remain outside the conclusion.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeSectorScalarNumerator.actual_product_coefficient_energy_le`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeSectorScalarNumerator.actual_word_coefficient_energy_le`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeSectorScalarNumerator.actual_word_scalar_numerator_support`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeSectorScalarNumerator.degreeBound`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeSectorScalarNumerator.ordinary_actual_finite_scalar_numerator`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeSectorScalarNumerator.ordinary_actual_word_finite_scalar_numerator`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeSectorScalarNumerator.readout`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeSectorScalarNumerator.scalar_numerator_support`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeSectorScalarNumerator.testEnergy`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeSectorScalarNumerator.wordDegreeBound`
- Dependency: [D5/S3/VertexAlgebra/FormalSeries/UngradedLocalWordSeries](../FormalSeries/UngradedLocalWordSeries.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeActualLZeroGrading](../LatticeActualLZeroGrading.md)
- Dependency: [D5/S3/VertexAlgebra/Sectors/LatticeSectorChannelTransport](LatticeSectorChannelTransport.md)
- Dependency: [D5/S3/VertexAlgebra/Sewing/CanonicalOccupation](../Sewing/CanonicalOccupation.md)
