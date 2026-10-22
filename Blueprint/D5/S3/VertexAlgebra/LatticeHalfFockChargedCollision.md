# Charged Taylor Coefficients and Finite Correction

## Abstract

Finite charged Taylor coefficients on the actual half-Fock tensor module.

Let D:LatticeData, hu:IsUnit D.G.det and sigma,tau:Charge D. The source is Carrier D and the target is ActualTensor D hu. They are distinct modules. All charges, including zero, every N:Nat, every signed exponent e:Int and every actual tensor input are included. No positivity, homogeneity, eigenstate, locality, product, iterate or Jacobi premise is imposed.

Write B=bilinear D sigma tau and Q(q)=chargeNorm D q. Put h=w/v^2 and u=v*sqrt(1+h). The scalar Taylor factor is (1+h)^(a/2) times ((sqrt(1+h)+1)/2)^(-2*B). The input polynomial is translated simultaneously in the sigma and tau directions by the actual pairTranslation constructor. Each translated monomial has two natural translation degrees d(0),d(1). For total=e+Q(sigma+tau)+2*N+d(0)+d(1), its creator contribution is zero when total<0, and otherwise is the finite sum over 0<=m<=total of collisionScalar(m-d(0)-Q(sigma),B,N) times halfCreationCoeff(sigma,m) times halfCreationCoeff(tau,total-m). These are formal coefficients; no analytic substitution or convergence claim is used.

**Theorem 1.1 (Corrected source coefficients at every Taylor order).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockChargedCollision.charged_allN_draft`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockChargedCollision.charged_allN_draft` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every D:LatticeData, hu:IsUnit D.G.det, sigma,tau:Charge D, N:Nat, e:Int and x:ActualTensor D hu, the coefficient at e of correctedField D hu (Finsupp.single (sigma+tau) (creationCoeff D sigma N)), evaluated on x, equals collisionCoefficient D hu sigma tau N e x. The source belongs to Carrier D. This public comparison permits downstream coefficient calculations at arbitrary Taylor order and signed exponent, including transformed tensor inputs. Zero charges and every determinant-unit lattice remain in scope. It compares a corrected source with its finite Taylor coefficient; it does not identify the product of two physical target fields with a residue.

The coefficient comparison uses two independently derived recurrences. Let C_N(e)x=collisionCoefficient D hu sigma tau N e x, let J_tau be the tau-weighted sum of singletonLinear current insertions and let r_j=halfBinomial(j)/(j+1). Then (N+1)*C_(N+1)(e)x equals ((e+2)/2)*C_N(e+2)x minus (J_tau(collisionField_N)).coeff e x, plus Q(tau)/2 times C_N(e+2)x, plus B/2 times the finite sum over j<=N of r_j*C_(N-j)(e+2*(j+1))x. The scalar recurrence follows from power-series differentiation and the inverse square-root unit. The current moment calculation differentiates the actual translated input polynomial. Every interchange of coefficient sums uses finite support for the input after the relevant transformation.

The corrected source sequence satisfies the same recurrence through physical translation, actual annihilation on creation coefficients and the negative-current insertion formula. Current zero mode, singleton and pair corrections and their one-half factors remain in the calculation. At N=0, Corr(1) is the empty correction, the scalar coefficient is one, the two creation exponentials multiply to the exponential for sigma+tau and the pair translation restricts to the diagonal. Strong induction therefore compares every signed coefficient on every actual input. Its induction property quantifies over all transformed inputs, so it also transports the entire current insertion field.

For the ordinary source product, mode r of the sigma ground source on the tau ground source is epsilon D sigma tau times the source with charge sigma+tau and creation degree -r-1-B. Negative degrees vanish. For a nonnegative degree, its corrected coefficient is epsilon D sigma tau times the corresponding collision coefficient. The fixed chargeScalar and chosen ground action remain those of the actual corrected field. The quadratic identity Q(sigma+tau)=Q(sigma)+Q(tau)+2*B proves c_sigma*c_tau*2^(-2*B)=c_(sigma+tau) using signed powers of the nonzero scalar two. The chosen ground product is epsilon(sigma,tau) times groundAction(sigma+tau). Consequently the same complete coefficient is c_sigma*c_tau*2^(-2*B) times the tensor map with collisionOscillator and groundAction(sigma)*groundAction(tau), for every actual tensor input.

**Theorem 1.2 (The normalized ordinary source-iterate coefficient).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockChargedCollision.charged_normalized_source_product_allN`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockChargedCollision.charged_normalized_source_product_allN` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every D:LatticeData, hu:IsUnit D.G.det, sigma,tau:Charge D, r,e:Int and x:ActualTensor D hu, take mode r of LatticeAllStateField.Y D (Finsupp.single sigma 1) on Finsupp.single tau 1 in Carrier D. The coefficient at e of its correctedField, evaluated on x, is zero if k=-r-1-bilinear D sigma tau is negative. Otherwise it is (chargeScalar D sigma * chargeScalar D tau * (2:Complex)^(-2*bilinear D sigma tau)) smul TensorProduct.map (collisionOscillator D sigma tau k.toNat e) (groundAction D hu sigma * groundAction D hu tau) x. This public endpoint exposes the exact charge normalization and ordered ground product for downstream source-iterate coefficient calculations. The source pair is the two specified ground sources; the target tensor input is arbitrary. No charge or signed mode is excluded. This is a corrected source-iterate coefficient comparison, not yet a physical two-field residue identity.

The proof uses the repository's actual annihilation, finite correction, negative-current insertion, physical translation and charged product kernel constructions. These are corrected source-iterate coefficient comparisons, not yet a physical two-field residue identity. The complete charged residue law, an independently unweighted outer tail, finite inversion and arbitrary-source Borcherds reconstruction remain further obligations. The full Moonshine, VOA, CFT, anomaly, fusion, string and AdS/CFT programme remains incomplete.

## References

- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockChargedCollision.charged_allN_draft`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockChargedCollision.charged_normalized_source_product_allN`
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockChargedCollision/Current](LatticeHalfFockChargedCollision/Current.md)
