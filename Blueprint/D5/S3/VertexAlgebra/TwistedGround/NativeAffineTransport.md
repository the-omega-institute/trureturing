# Native affine Taylor comparison and linear transport

## Abstract

Native affine Taylor comparison and linear transport

Finite complex polynomial identities for arbitrary finite index types, including empty types, rectangular, zero and singular substitutions. The native affine coefficient retains its original auxiliary-coordinate definition. Covariance is U A transpose(U), with ordinary transpose, and mean is U mu. The original charged-row application is in OriginalSourceInverseCoefficient; no full sewing or physical realization is asserted.

**Definition 1.1 (Finite linear substitution).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/NativeAffineTransport.linearSubstitution`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/NativeAffineTransport.linearSubstitution` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

For arbitrary finite types I and J, including empty types, linearSubstitution(U) sends X_j to the sum of U[i,j] X_i. Matrices are complex and may be rectangular, zero or singular.

**Definition 1.2 (Ordinary covariance transport).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/NativeAffineTransport.transportCovariance`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/NativeAffineTransport.transportCovariance` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

transportCovariance(U,A) is U A transpose(U), with ordinary transpose and no complex conjugation.

**Definition 1.3 (Affine mean transport).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/NativeAffineTransport.transportMean`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/NativeAffineTransport.transportMean` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

transportMean(U,mu) is U mu.

**Definition 1.4 (Fix the external coordinates).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/NativeAffineTransport.sourceBlock`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/NativeAffineTransport.sourceBlock` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

sourceBlock(U) is block diagonal with U on source coordinates and identity on all external coordinates.

**Theorem 1.5 (Native affine coefficient covariance).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/NativeAffineTransport.affineCoefficient_linear_substitution`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/NativeAffineTransport.affineCoefficient_linear_substitution` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

For every finite I and J, U:I by J, symmetric complex A, arbitrary complex mean mu, target occupation d and natural N with degree(d) at most N, the sum over all source occupations e of total degree at most N of affineCoefficient(A,mu,e) times the d coefficient of linearSubstitution(U,X^e) equals affineCoefficient(U A transpose(U),U mu,d). The native auxiliary-coordinate coefficient definition is retained. The native_affine_eq_taylor comparison proves its equality with ordinary Taylor coefficients from the native moment recurrence, including zero degree and empty types.

**Definition 1.6 (Finite exponential polynomial).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/NativeAffineTransport.expCut`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/NativeAffineTransport.expCut` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

For any finite type I, complex polynomial p and natural N, expCut(p,N) is the sum for k from zero through N of p^k divided by k factorial. The zero and empty-type cases are included.

**Definition 1.7 (Quadratic and linear exponent).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/NativeAffineTransport.affineExponent`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/NativeAffineTransport.affineExponent` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

For every finite I, complex square A and mean mu, affineExponent(A,mu) is quadratic(A) plus the sum over i of mu(i) X_i, with the existing half-quadratic convention. Symmetry is required by the comparison theorems, not by this definition.

**Definition 1.8 (Degree-bounded Taylor coefficient).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/NativeAffineTransport.taylorCoefficient`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/NativeAffineTransport.taylorCoefficient` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

For every finite I, complex A, mean mu and occupation d, taylorCoefficient(A,mu,d) extracts coefficient d from expCut(affineExponent(A,mu),degree(d)).

**Theorem 1.9 (Zero affine exponent constant).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/NativeAffineTransport.affineExponent_constant`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/NativeAffineTransport.affineExponent_constant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

The actual affine exponent has zero constant coefficient, including empty index types. External ordinary extraction consumes this exact original polynomial fact.

**Theorem 1.10 (Finite exponential polynomial derivative).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/NativeAffineTransport.pderiv_expCut`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/NativeAffineTransport.pderiv_expCut` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

Differentiating the finite exponential polynomial of order n+1 yields the derivative of its exponent times the finite exponential polynomial of order n. The ordinary factorial ratios are exact.

**Theorem 1.11 (Stable Taylor cutoff).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/NativeAffineTransport.taylorCoefficient_cut`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/NativeAffineTransport.taylorCoefficient_cut` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

For every finite I, complex A, arbitrary mean mu, occupation d and natural N with degree(d) at most N, taylorCoefficient(A,mu,d) equals the d coefficient of expCut(affineExponent(A,mu),N). The zero constant term forces all powers above degree(d) to vanish at d. The original-row proof consumes this equality with N=n+degree(betaR)+degree(gammaR).

**Theorem 1.12 (Native recurrence equals Taylor coefficients).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/NativeAffineTransport.native_affine_eq_taylor`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/NativeAffineTransport.native_affine_eq_taylor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

For every finite I, symmetric complex A, arbitrary mean mu and occupation d, the original affineCoefficient(A,mu,d) equals taylorCoefficient(A,mu,d). Strong occupation induction compares the native affine moment recurrence with the factorial-normalized derivative recurrence. It includes d=0 and empty I, and is used by transport and the original-row readout.

**Definition 1.13 (Extract fixed external occupations).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/NativeAffineTransport.externalSection`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/NativeAffineTransport.externalSection` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

For finite I and J, polynomial p on I plus J and external occupation h on J, externalSection(p,h) is the polynomial on I obtained by extracting h through the swapped sum-ring equivalence. No evaluation of external variables at one is performed.

**Theorem 1.14 (Joint occupation coefficient).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/NativeAffineTransport.externalSection_coeff`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/NativeAffineTransport.externalSection_coeff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

For every finite I and J, complex polynomial p on I plus J, h on J and d on I, the d coefficient of externalSection(p,h) equals the coefficient of p at d.sumElim(h).

**Theorem 1.15 (Native transport with external occupations).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/NativeAffineTransport.externalSection_native`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/NativeAffineTransport.externalSection_native` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

For every finite I and J, complex square U on I, symmetric complex A on I plus J, arbitrary mean mu, occupations d and h and N at least degree(d.sumElim(h)), the d coefficient of linearSubstitution(U,externalSection(expCut(affineExponent(A,mu),N),h)) equals affineCoefficient(transportCovariance(sourceBlock(U),A),transportMean(sourceBlock(U),mu),d.sumElim(h)). The block fixes every external coordinate and ordinary transpose is used. This supplies the original-row proof with both external occupations intact.

**Theorem 1.16 (Ordinary symmetry under transport).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/NativeAffineTransport.transportCovariance_symm`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/NativeAffineTransport.transportCovariance_symm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

For arbitrary finite types, a complex rectangular substitution transports a symmetric covariance to a symmetric covariance by ordinary transpose. No positivity, invertibility or nonempty-type hypothesis is required.

The native moment recurrence is compared with the finite exponential polynomial by strong occupation induction. Total target degree controls the Taylor cutoff. Gaussian polynomial calculus is classical, and this reusable transport makes no literature novelty claim.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/NativeAffineTransport.affineCoefficient_linear_substitution`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/NativeAffineTransport.affineExponent`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/NativeAffineTransport.affineExponent_constant`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/NativeAffineTransport.expCut`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/NativeAffineTransport.externalSection`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/NativeAffineTransport.externalSection_coeff`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/NativeAffineTransport.externalSection_native`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/NativeAffineTransport.linearSubstitution`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/NativeAffineTransport.native_affine_eq_taylor`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/NativeAffineTransport.pderiv_expCut`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/NativeAffineTransport.sourceBlock`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/NativeAffineTransport.taylorCoefficient`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/NativeAffineTransport.taylorCoefficient_cut`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/NativeAffineTransport.transportCovariance`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/NativeAffineTransport.transportCovariance_symm`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/NativeAffineTransport.transportMean`
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/OriginalChargedRowSource](OriginalChargedRowSource.md)
