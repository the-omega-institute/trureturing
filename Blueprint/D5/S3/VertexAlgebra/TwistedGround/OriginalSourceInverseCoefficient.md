# Original source inverse and bilinear factorial transpose

## Abstract

Original source inverse and bilinear factorial transpose

These identities concern finite polynomials on the original lattice oscillator carrier. The transpose theorem allows arbitrary mode-dependent complex matrices. The corrected row application alone retains the determinant-unit hypothesis of the original operators. All charges and integer Laurent selectors remain quantified; no positivity or analytic completion is imposed.

**Definition 1.1 (Finite positive-energy sublevel).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalSourceInverseCoefficient.oscillatorSublevel`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/OriginalSourceInverseCoefficient.oscillatorSublevel` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

For every original lattice D and natural cutoff n, oscillatorSublevel is the finite set of all occupations alpha with oscillatorEnergy(alpha) at most n. Energy uses the original frequency k+1. At n=0 this set contains exactly the zero occupation, including at rank zero.

**Definition 1.2 (Normalized source Taylor polynomial).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalSourceInverseCoefficient.sourceTaylor`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/OriginalSourceInverseCoefficient.sourceTaylor` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

For any complex linear functional f on the original oscillator polynomial ring and any natural n, sourceTaylor is the sum over the positive-energy sublevel of X^delta times f(X^delta)/weight(delta). This uses the original occupation factorial product, with weight(0)=1.

**Theorem 1.3 (Chain rule with mode-dependent matrices).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalSourceInverseCoefficient.pderiv_substitution`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalSourceInverseCoefficient.pderiv_substitution` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

For arbitrary D, matrices A(k) over the complex numbers, color i, natural mode k and polynomial p, the derivative in (i,k) of substitution(A,p) is the sum over colors a of A(k)[i,a] times substitution(A, derivative in (a,k) of p). The existing variableImage sends X_(j,k) to the sum of A(k)[i,j] X_(i,k); its row and column order is retained.

**Theorem 1.4 (Ordinary bilinear factorial transpose).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalSourceInverseCoefficient.substitution_factorial_transpose`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalSourceInverseCoefficient.substitution_factorial_transpose` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

For every D, every mode-dependent family A of complex square matrices and all oscillator polynomials p and q, F(substitution(A,p),q)=F(p,substitution(k maps to transpose(A(k)),q)), where F is the existing complex bilinear factorial form. There is no complex conjugation, determinant or invertibility hypothesis; singular and zero matrices are included. Induction on p uses the chain rule and the factorial creation/derivative relation.

**Theorem 1.5 (Original inverse occupation coefficient).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalSourceInverseCoefficient.inverse_occupation_coefficient`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalSourceInverseCoefficient.inverse_occupation_coefficient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

For every D, original occupation alpha and polynomial q, the sum over delta in the support of inverseOscillator(X^alpha) of its delta coefficient times weight(delta) times q_delta equals weight(alpha) times the alpha coefficient of substitution(T transpose,q). Here T(k)=(-((k:Complex)+1)) inverse times gramComplex(D) inverse, exactly the original integer-frequency inverse covariance. No determinant-unit hypothesis is added to this polynomial identity.

**Theorem 1.6 (Exact source Taylor coefficients).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalSourceInverseCoefficient.sourceTaylor_coeff`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalSourceInverseCoefficient.sourceTaylor_coeff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

For every D, complex linear source f, natural n and occupation alpha, the alpha coefficient of sourceTaylor(D,f,n) is f(X^alpha)/weight(alpha) when oscillatorEnergy(alpha) is at most n, and zero otherwise.

**Theorem 1.7 (Energy of every inverse occupation).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalSourceInverseCoefficient.inverse_support_energy`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalSourceInverseCoefficient.inverse_support_energy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

Every delta in the polynomial support of the actual inverseOscillator(X^alpha) has oscillatorEnergy(delta)=oscillatorEnergy(alpha). This is the same-mode weighted homogeneity of SourcePairingLaws.substitution_monomial_weight, with its integer weight converted to the original natural positive energy. Consequently such a delta has no occupied frequency k with n at most k whenever alpha has energy at most n.

**Theorem 1.8 (Finite inverse occupation interchange).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalSourceInverseCoefficient.inverse_occupation_interchange`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalSourceInverseCoefficient.inverse_occupation_interchange` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

For every D and n and arbitrary complex functions F and G on occupations, the sum over alpha in oscillatorSublevel(D,n) of F(alpha) times the support sum of inverseOscillator(X^alpha)_delta G(delta) equals the sum over delta and then alpha in that same sublevel of F(alpha) inverseOscillator(X^alpha)_delta G(delta). Energy preservation justifies extending support to the common sublevel before the finite sums are exchanged. A single-occupation selector gives the finite source readout.

**Theorem 1.9 (Original dual source readout).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalSourceInverseCoefficient.dual_readout_coefficient`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalSourceInverseCoefficient.dual_readout_coefficient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

For any original complex linear functional f, occupation alpha and cutoff n at least its oscillator energy, f(dualOscillatorMonomial(D,alpha)) is the alpha coefficient of substitution(T transpose,sourceTaylor(D,f,n)). The factorial in the original dual monomial cancels the factorial in the occupation transpose identity; it is not suppressed by convention.

**Theorem 1.10 (Finite support at a fixed energy).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalSourceInverseCoefficient.energy_readout_finite`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalSourceInverseCoefficient.energy_readout_finite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

For arbitrary original linear functionals f and g and natural n, the function of alpha equal to f(X^alpha) g(dualOscillatorMonomial(D,alpha)) when oscillatorEnergy(alpha)=n and zero otherwise has finite support. This is a finite occupation statement, with no analytic summability assertion.

**Theorem 1.11 (Finite original coevaluation coefficient).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalSourceInverseCoefficient.finite_energy_inverse_coefficients`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalSourceInverseCoefficient.finite_energy_inverse_coefficients` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

For every D, original linear sources f and g and natural n, their finsum at exact oscillator energy n equals the sum on oscillatorSublevel(D,n), restricted by the same equality of energies, of weight(alpha) times sourceTaylor(D,f,n)_alpha times substitution(T transpose,sourceTaylor(D,g,n))_alpha. There is exactly one internal occupation factorial.

**Definition 1.12 (Original corrected row as a linear source).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalSourceInverseCoefficient.correctedSourceReadout`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/OriginalSourceInverseCoefficient.correctedSourceReadout` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

For every D with IsUnit(D.G.det), charge a, integer e and oscillator polynomials R and S, correctedSourceReadout sends p to wick(D,S,oscillatorCorrected(D,hu,a,e,p,R)). It uses the original corrected operator and the original bilinear Wick detector.

**Theorem 1.13 (Taylor polynomial of the corrected Gaussian row).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalSourceInverseCoefficient.corrected_sourceTaylor`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalSourceInverseCoefficient.corrected_sourceTaylor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

For arbitrary determinant-unit witness hu, charge a, integer e, external occupations beta and gamma and natural cutoff n, the corrected source Taylor polynomial is weight(beta) weight(gamma) times the finite polynomial whose delta coefficient is the original affineLaurent row. At each delta its support label is rowSupport(D,delta,beta,gamma), the matrix and mean are correctedMatrix and correctedMean, and the exact selector is e+chargeNorm(D,a). The source factorial cancels, retaining both external factorials.

**Theorem 1.14 (Two original rows with the actual source inverse).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalSourceInverseCoefficient.original_two_rows_inverse_coefficient`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalSourceInverseCoefficient.original_two_rows_inverse_coefficient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

For every original D, arbitrary IsUnit(D.G.det) witness hu, charge a, occupations alpha, betaL, gammaL, betaR and gammaR, integers eL and eR, and natural n with oscillatorEnergy(alpha) at most n, the product chargeScalar(a) chargeScalar(-a) times the left Wick corrected row at X^alpha and the right Wick corrected row at dualOscillatorMonomial(alpha) equals the product of those two charge scalars, weight(alpha), all four external weights, the original left affineLaurent row, and the alpha coefficient of substitution(T transpose, the finite sum of X^delta times the original right affineLaurent row). The right charge is -a; each row keeps its own complete support union and exact selector eL+chargeNorm(a) or eR+chargeNorm(-a). This coefficient identity includes zero occupations, empty types and n=0. It does not introduce an extra charge average or assume an affine sewing equation.

Factorial Fock and Gaussian polynomial calculus are classical. The original carrier and charged-row suppliers retain their FLM and subsequent attributions. This composition makes no claim of literature novelty. Identifying the finite transposed right polynomial uniformly with the affine Gaussian coefficient, proving external Gaussian block factorization and transporting the exact Laurent selectors into FH sewing remain separate obligations. The original identityK, independent half-L1 transport, scalar C1 kernel, modular identification and full VOA/CFT/string or AdS/CFT goals remain unresolved.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalSourceInverseCoefficient.correctedSourceReadout`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalSourceInverseCoefficient.corrected_sourceTaylor`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalSourceInverseCoefficient.dual_readout_coefficient`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalSourceInverseCoefficient.energy_readout_finite`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalSourceInverseCoefficient.finite_energy_inverse_coefficients`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalSourceInverseCoefficient.inverse_occupation_coefficient`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalSourceInverseCoefficient.inverse_occupation_interchange`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalSourceInverseCoefficient.inverse_support_energy`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalSourceInverseCoefficient.original_two_rows_inverse_coefficient`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalSourceInverseCoefficient.oscillatorSublevel`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalSourceInverseCoefficient.pderiv_substitution`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalSourceInverseCoefficient.sourceTaylor`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalSourceInverseCoefficient.sourceTaylor_coeff`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalSourceInverseCoefficient.substitution_factorial_transpose`
- Dependency: [D5/S3/VertexAlgebra/SourceBPZ/OriginalSourceCoevaluation](../SourceBPZ/OriginalSourceCoevaluation.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/OriginalAffineRecompositionSource](OriginalAffineRecompositionSource.md)
