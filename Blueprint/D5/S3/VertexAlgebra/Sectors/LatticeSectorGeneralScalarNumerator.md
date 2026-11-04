# Scalar lattice numerators without a Gram inverse

## Abstract

Finite scalar common numerators of arbitrary-length actual lattice words for every original lattice datum.

Let D be the original LatticeData, with arbitrary finite rank, symmetric integral Gram matrix and even diagonal. Singular, indefinite and rank-zero data are included. The carrier, inclusion, projection, canonical state-field map Y and energy grading are the original constructions. Every external oscillator polynomial may mix energies or vanish; all charge sectors are retained. No inverse matrix, positivity assumption, homogeneous-state restriction or replacement field is used.

**Theorem 1.1 (One finite scalar common numerator for every finite word).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeSectorGeneralScalarNumerator.ordinary_actual_word_finite_scalar_numerator`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sectors/LatticeSectorGeneralScalarNumerator.ordinary_actual_word_finite_scalar_numerator` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural n, labelled charges c(i) and oscillator polynomials s(i), put A(i)=Y(D,inclusion(D,c(i),s(i))) and order=List.ofFn(id) on Fin(n). There exists a natural k such that for every i<j, the kth power of deltaEnd annihilates the commutator of A(i) and A(j). This k is chosen before the input charge delta and state w. For every delta and w in Sector(D,delta), there are natural shifts a(i) and one Carrier-valued multivariate power series P, chosen before any test polynomial p. For every i and integer mode m with a(i)<=m, the original mode A(i)[[m]] annihilates inclusion(D,delta,w). For every list other permuting order and every signed exponent e, polynomialAction(clearingPolynomial(n,k),coefficientDistribution(A,inclusion(D,delta,w),1,other)) at e-a equals signedExtend(P,e). These are the original truncation and permutation identities, with exponent e corresponding to mode -e-1.

Write h(eta)=chargeEnergy(D,eta), chi=(sum_i c(i))+delta, and phi=readout(D,p) composed with projection(D,chi), where readout is the original factorial pairing, complex-linear in the tested state. For every arbitrary finite p, set S(d)=phi(P(d)). The exact original cutoff is K=wordDegreeBound(D,c,delta,k,a,p)=sum_i a(i)+k*card(labelledPairs(n))+testEnergy(D,p)+h(chi)-h(delta)-sum_i h(c(i)), with every term interpreted as an integer. Every nonzero S(d) has integer total degree degree(d)<=K. There exists a unique complex multivariate polynomial R whose power-series coercion is S and whose totalDegree is at most K.toNat. If K<0, both S and R are zero. For every permutation other and every signed e, applying the same clearing action to the scalar distribution b maps to phi(coefficientDistribution(A,inclusion(D,delta,w),1,other,b)), at e-a, gives signedExtend(R,e). The same P supplies every p, and this same R supplies all permutations for that p.

The energy argument retains every signed exponent and every suffix. For any list l of labels, not necessarily distinct, every surviving output coefficient (rho,T) of word(A,l,e)(inclusion(D,delta,w)) satisfies h(delta)+sum over i in l of (h(c(i))+e(i)) <= h(rho)+oscillatorEnergy(T). The empty list follows from the original included-sector coefficient support. At a list head, expand both the finite head state and the entire suffix output into their original finite grade projections. Every energy in either expansion is at least its corresponding lower bound. LatticeCoefficientEnergy.actual_mode_grade places their actual q-mode in grade m+n-q-1 with no inverse premise. The original grade coefficient characterization excludes all energies below the accumulated bound. Reassembling the finite sums preserves that bound.

Expand the factorial test against the finite monomial support of p. Each tested monomial has energy at most testEnergy(D,p), so the word estimate forces the scalar distribution to vanish above its signed total-exponent cutoff. The existing clearing estimate shifts this cutoff by exactly k*card(labelledPairs(n)); the input shifts contribute sum_i a(i). Applying this estimate to the supplied signed identity gives degree support for S. Actual field locality and ungraded_local_word_common_series supply the original k,a,P independently of this grading argument. The existing exact truncTotal(K.toNat+1) construction extracts R, and injectivity of polynomial coercion proves uniqueness. Linearity transfers every original vector permutation identity to this polynomial.

There is no lower bound on the Gram rank or word length: n=0, the empty word, repeated fields and arbitrary signed exponents remain included. The generally infinite vector series P is retained. Only its finite factorial tests are proved polynomial; no finite-vector-numerator assumption or convergence assumption is added.

The finite grade decomposition, sector support, clearing estimate, ungraded common-series construction and polynomial extraction are reused from the existing lattice and formal-series results. The field suppliers retain the Bakalov--Kac, Matsuo--Nagatomo and Carnahan attributions. Mathlib retains its authorship and Apache license for finite sums, multivariate polynomials and power-series truncation. No external-literature novelty is claimed.

This algebraic theorem supplies the same finite scalar numerator for later analytic chart evaluation for every original D. It does not identify a fixed external total-grade component with an unrestricted mixed-grade correlator. Whole-correlator recovery requires finite external-grade decomposition and the actual normalization. Analytic sewing, CFT realization, a Monster realization, anomalies, string theory and AdS/CFT remain separate mathematical obligations.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeSectorGeneralScalarNumerator.ordinary_actual_word_finite_scalar_numerator`
- Dependency: [D5/S3/VertexAlgebra/Energy/LatticeCoefficientEnergy](../Energy/LatticeCoefficientEnergy.md)
- Dependency: [D5/S3/VertexAlgebra/Sectors/LatticeSectorScalarNumerator](LatticeSectorScalarNumerator.md)
