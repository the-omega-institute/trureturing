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

The scalar support argument and finite numerator construction extend the repository's actual-channel results. The existing Bakalov--Kac, Matsuo--Nagatomo and Carnahan attributions remain in the field suppliers, and Mathlib retains its authorship and Apache license for finite polynomial induction, power-series truncation and coercion. No external-literature novelty is claimed. The existing sewing module supplies the finite factorial coordinate expansion. Its arbitrary-D occupation-summability theorem retains its original unrestricted hypotheses.

Zero and inhomogeneous external polynomials are included. Singular Gram forms require a separate grading argument. These are formal coefficient identities: radial analytic identities, operator convergence, invariant BPZ pairings, CFT sewing, Monster realization, anomalies, string theory and AdS/CFT remain outside the conclusion.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeSectorScalarNumerator.actual_product_coefficient_energy_le`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeSectorScalarNumerator.degreeBound`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeSectorScalarNumerator.ordinary_actual_finite_scalar_numerator`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeSectorScalarNumerator.readout`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeSectorScalarNumerator.scalar_numerator_support`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeSectorScalarNumerator.testEnergy`
- Dependency: [D5/S3/VertexAlgebra/LatticeActualLZeroGrading](../LatticeActualLZeroGrading.md)
- Dependency: [D5/S3/VertexAlgebra/Sectors/LatticeSectorChannelTransport](LatticeSectorChannelTransport.md)
- Dependency: [D5/S3/VertexAlgebra/Sewing/CanonicalOccupation](../Sewing/CanonicalOccupation.md)
