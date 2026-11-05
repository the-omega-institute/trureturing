# All orders in the formal parameter

## Abstract

Original corrected-field formal Mobius covariance

**Theorem 1.1 (All-source original Mobius coefficient identity).**

Lean statement: `D5/S3/VertexAlgebra/HalfFock/ActualMobiusAllOrder.corrected_field_mobius_coefficient`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/HalfFock/ActualMobiusAllOrder.corrected_field_mobius_coefficient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

Let T be the original actual tensor mode L1, let Sj be the original source Sugawara mode j with inverse complex Gram matrix, and write A_e(a) for the coefficient of the original corrected field. For every natural n, signed integer e and arbitrary original source a, the sum over i from zero to n of (-1)^(n-i)/(i!(n-i)!) times T^i A_e(a) T^(n-i) equals the sum over the actual finite state energies h and k from zero to n of choose(2h+e/2-k-1,n-k)/k! times A_(e-2n+2k)(S1^k gradeProjection(h,a)). Endomorphisms act right to left. The integer determinant-unit hypothesis supplies the actual inverse; no positivity, primary-state, homogeneity, rank or target nilpotence assumption is present.

The source Virasoro relation gives [S0,S1]=-S1 and hence S0 S1^k a=(h-k)S1^k a for a source of energy h. The original infinitesimal L1 identity then gives the two adjacent descendant coefficients. With alpha=2h+e/2-1, c(n,k)=choose(alpha-k,n-k)/k! satisfies (n+1)c(n+1,k)=c(n,k-1)+(alpha-n-k)c(n,k), with out-of-range indices zero. Induction in n and the actual finite grade projections establish the stated all-source identity. At order two the mixed coefficient is alpha-1.

**Definition 1.2 (Original field at each fixed formal order).**

Lean statement: `D5/S3/VertexAlgebra/HalfFock/ActualMobiusAllOrder.formalMobiusOrder`

*Formalization.* `D5/S3/VertexAlgebra/HalfFock/ActualMobiusAllOrder.formalMobiusOrder` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

For every n and original source, the conjugation coefficient is an actual Hahn vertex operator on the original tensor space. On input x, take the minimum of the original field orders at T^j x for j from zero to n. Below this minimum every summand vanishes. Only finitely many original supports enter; no fixed-mode target power nilpotence is used.

**Definition 1.3 (Normalized formal half-coordinate unit).**

Lean statement: `D5/S3/VertexAlgebra/HalfFock/ActualMobiusAllOrder.normalizedRawHalfUnit`

*Formalization.* `D5/S3/VertexAlgebra/HalfFock/ActualMobiusAllOrder.normalizedRawHalfUnit` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

The unit is the binomial series for (1-X)^(-1/2). Its type includes constant coefficient one and the identity root^2(1-X)=1. All signed integer powers are identified with the corresponding binomial powers. In the raw half-coordinate, X represents u t^2.

**Definition 1.4 (Independent coordinate-product coefficient extraction).**

Lean statement: `D5/S3/VertexAlgebra/HalfFock/ActualMobiusAllOrder.rawHalfCoordinateReadout`

*Formalization.* `D5/S3/VertexAlgebra/HalfFock/ActualMobiusAllOrder.rawHalfCoordinateReadout` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

For each actual source grade h, sum the finite original S1 exponential through its oscillator cutoff. A raw monomial t^d contributes the normalized half-unit to the signed power d, multiplied by the binomial unit (1-X)^(k-2h). The coefficient of u^n t^e has d=e-2(n-k); the scalar is the n-th coefficient of X^k times that unit product, divided by k!. The X^k here tracks the exterior factor u^k; the other n-k powers contribute the raw-coordinate shift 2(n-k). This definition uses power-series multiplication and the normalized root, independently of the commutator coefficients.

**Theorem 1.5 (Equality with the normalized raw-coordinate product).**

Lean statement: `D5/S3/VertexAlgebra/HalfFock/ActualMobiusAllOrder.formal_mobius_raw_coordinate`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/HalfFock/ActualMobiusAllOrder.formal_mobius_raw_coordinate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

At every formal order and signed raw exponent, the original conjugated field coefficient equals the independently defined coordinate-product readout. Binomial multiplication combines the factors k-2h and -d/2. Reflection of the binomial coefficient gives choose(2h+e/2-k-1,n-k). Terms k greater than n vanish by formal order; terms beyond the original source oscillator cutoff vanish by the actual Sugawara L1 bound. Finite grade projections give the arbitrary mixed-source statement.

The coordinate is the normalized raw half-coordinate f_u(t)=t(1-u t^2)^(-1/2), whose unit factor has constant coefficient one. For a homogeneous source of signed energy h, the source action is exp(u(1-u t^2)S1)(1-u t^2)^(-2S0), with the right factor applied first. Thus its k-th descendant contribution is u^k/k! times (1-u t^2)^(k-2h) A(S1^k a)(f_u(t)). The original oscillator cutoff makes the source exponential finite on each source. This formula is interpreted order by order in u; it asserts no convergence or numeric target exponential.

The scope includes mixed source energies, signed charges, odd raw exponents, indefinite Gram forms and rank zero. Fixed formal orders are fields on the original actual tensor space: after application to x, their support is bounded below using finitely many original fields at T^j x. The formal parameter is independent of the raw half-coordinate. A global group action, analytic resummation and the full Monster, VOA, CFT, anomaly, fusion, string theory and AdS/CFT constructions require further mathematics.

The classical conventions are those of Frenkel, Lepowsky and Meurman and the original lattice-field suppliers. The binomial power series comes from Scott Carnahan's mathlib construction, with its Apache 2.0 attribution retained. The argument combines the original current, corrected-field, source Virasoro and energy decomposition results; it makes no claim of literature novelty.

## References

- Truth anchor: `D5/S3/VertexAlgebra/HalfFock/ActualMobiusAllOrder.corrected_field_mobius_coefficient`
- Truth anchor: `D5/S3/VertexAlgebra/HalfFock/ActualMobiusAllOrder.formalMobiusOrder`
- Truth anchor: `D5/S3/VertexAlgebra/HalfFock/ActualMobiusAllOrder.formal_mobius_raw_coordinate`
- Truth anchor: `D5/S3/VertexAlgebra/HalfFock/ActualMobiusAllOrder.normalizedRawHalfUnit`
- Truth anchor: `D5/S3/VertexAlgebra/HalfFock/ActualMobiusAllOrder.rawHalfCoordinateReadout`
- Dependency: [D5/S3/VertexAlgebra/HalfFock/ActualMobiusCovariance](ActualMobiusCovariance.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeActualLZeroGrading](../LatticeActualLZeroGrading.md)
- Dependency: [D5/S3/VertexAlgebra/SourceMobius/OriginalCarrier](../SourceMobius/OriginalCarrier.md)
