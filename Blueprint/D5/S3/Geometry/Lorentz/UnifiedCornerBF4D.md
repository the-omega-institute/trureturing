# Unified corner symmetry and chiral BF reduction

## Abstract

Corner currents, area and rapidity, and the signed auxiliary-field BF reduction.

The normal and Yang–Mills currents share a tangential derivation action. The normal moment map admits an explicit canonical area–rapidity extension. A metric determines the signed Hodge operator on the auxiliary two-form sector, whose exact stationary elimination yields the curvature quadratic density.

**Definition 1.1 (Internal Lie algebra).**

Lean statement: `D5/S3/Geometry/Lorentz/UnifiedCornerBF4D.CornerInternal`

*Formalization.* `D5/S3/Geometry/Lorentz/UnifiedCornerBF4D.CornerInternal` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The internal Lie algebra is the direct product of the trace-zero two-by-two matrices and the Yang–Mills Lie algebra.

**Definition 1.2 (Current Lie algebra).**

Lean statement: `D5/S3/Geometry/Lorentz/UnifiedCornerBF4D.CornerCurrent`

*Formalization.* `D5/S3/Geometry/Lorentz/UnifiedCornerBF4D.CornerCurrent` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Scalar extension gives the tensor product with the commutative coefficient algebra, with bracket [a⊗u,b⊗v]=ab⊗[u,v].

**Definition 1.3 (Differentiating currents).**

Lean statement: `D5/S3/Geometry/Lorentz/UnifiedCornerBF4D.currentDerivation`

*Formalization.* `D5/S3/Geometry/Lorentz/UnifiedCornerBF4D.currentDerivation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The derivation acts on the coefficient factor and leaves the internal factor fixed. The product rule proves the Lie derivation law on pure tensors, and additivity extends it to all currents.

**Definition 1.4 (Tangential Lie action).**

Lean statement: `D5/S3/Geometry/Lorentz/UnifiedCornerBF4D.cornerDerivationHom`

*Formalization.* `D5/S3/Geometry/Lorentz/UnifiedCornerBF4D.cornerDerivationHom` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

On pure tensors the commutator of two induced derivations acts by the commutator on the coefficient. Tensor induction extends the linear and Lie homomorphism laws.

**Definition 1.5 (Semidirect corner Lie algebra).**

Lean statement: `D5/S3/Geometry/Lorentz/UnifiedCornerBF4D.CornerAlgebra`

*Formalization.* `D5/S3/Geometry/Lorentz/UnifiedCornerBF4D.CornerAlgebra` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* W. Donnelly and L. Freidel (2016). *Local subsystems in gauge theory and gravity*. DOI: [10.1007/JHEP09(2016)102](https://doi.org/10.1007/JHEP09(2016)102). URL: <https://arxiv.org/abs/1601.04744>.

*Commentary.*

The tensor product of the coefficient and internal Lie algebras is acted upon by the selected Lie subalgebra of coefficient derivations. The resulting semidirect sum has its current component first.

**Definition 1.6 (Tangential charges).**

Lean statement: `D5/S3/Geometry/Lorentz/UnifiedCornerBF4D.P`

*Formalization.* `D5/S3/Geometry/Lorentz/UnifiedCornerBF4D.P` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The acting Lie algebra is included in the semidirect sum.

**Definition 1.7 (Pure current charges).**

Lean statement: `D5/S3/Geometry/Lorentz/UnifiedCornerBF4D.J`

*Formalization.* `D5/S3/Geometry/Lorentz/UnifiedCornerBF4D.J` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The coefficient and the internal generator define a pure tensor and its inclusion into the semidirect sum.

**Definition 1.8 (Gravitational currents).**

Lean statement: `D5/S3/Geometry/Lorentz/UnifiedCornerBF4D.G`

*Formalization.* `D5/S3/Geometry/Lorentz/UnifiedCornerBF4D.G` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Scalar extension of the first product inclusion defines a Lie homomorphism on all normal frame currents.

**Definition 1.9 (Yang–Mills currents).**

Lean statement: `D5/S3/Geometry/Lorentz/UnifiedCornerBF4D.Y`

*Formalization.* `D5/S3/Geometry/Lorentz/UnifiedCornerBF4D.Y` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Scalar extension of the second product inclusion defines a Lie homomorphism on all Yang–Mills currents.

**Theorem 1.10 (Corner bracket table).**

$$\forall A \in \operatorname{CommAlgebra}\left(\mathbb{R}\right), gYM \in \operatorname{LieAlgebra}\left(\mathbb{R}\right), L \in \operatorname{LieSubalgebra}\left(\operatorname{Der}\left(\mathbb{R}, A\right)\right),\; \forall X \in L, Z \in L, a \in A, b \in A, u \in \operatorname{sl}\left(2, \mathbb{R}\right) \times gYM, v \in \operatorname{sl}\left(2, \mathbb{R}\right) \times gYM,\; [\operatorname{P}\left(X\right), \operatorname{P}\left(Z\right)] = \operatorname{P}\left([X, Z]\right) \land \left([\operatorname{P}\left(X\right), \operatorname{J}\left(a, u\right)] = \operatorname{J}\left(X\left(a\right), u\right) \land [\operatorname{J}\left(a, u\right), \operatorname{J}\left(b, v\right)] = \operatorname{J}\left(a \cdot b, [u, v]\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/UnifiedCornerBF4D.corner_bracket` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The bracket of tangential generators is their commutator. A tangential generator acts on a current by differentiation of its coefficient. Two pure currents bracket by multiplying coefficients and taking the internal bracket.

**Theorem 1.11 (Normal and gauge charge brackets).**

$$\forall A \in \operatorname{CommAlgebra}\left(\mathbb{R}\right), gYM \in \operatorname{LieAlgebra}\left(\mathbb{R}\right), L \in \operatorname{LieSubalgebra}\left(\operatorname{Der}\left(\mathbb{R}, A\right)\right),\; \forall X \in L, u \in \operatorname{Tensor}\left(A, \operatorname{sl}\left(2, \mathbb{R}\right)\right), v \in \operatorname{Tensor}\left(A, \operatorname{sl}\left(2, \mathbb{R}\right)\right), l \in \operatorname{Tensor}\left(A, gYM\right), eta \in \operatorname{Tensor}\left(A, gYM\right),\; [\operatorname{P}\left(X\right), \operatorname{G}\left(u\right)] = \operatorname{G}\left(\operatorname{Tensor}\left(X, I\right)\left(u\right)\right) \land \left([\operatorname{P}\left(X\right), \operatorname{Y}\left(l\right)] = \operatorname{Y}\left(\operatorname{Tensor}\left(X, I\right)\left(l\right)\right) \land \left([\operatorname{G}\left(u\right), \operatorname{G}\left(v\right)] = \operatorname{G}\left([u, v]\right) \land \left([\operatorname{Y}\left(l\right), \operatorname{Y}\left(eta\right)] = \operatorname{Y}\left([l, eta]\right) \land [\operatorname{G}\left(u\right), \operatorname{Y}\left(l\right)] = 0\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/UnifiedCornerBF4D.corner_internal_brackets` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* W. Donnelly and L. Freidel (2016). *Local subsystems in gauge theory and gravity*. DOI: [10.1007/JHEP09(2016)102](https://doi.org/10.1007/JHEP09(2016)102). URL: <https://arxiv.org/abs/1601.04744>.

*Commentary.*

Tangential derivations differentiate each coefficient factor. Within each internal summand the charge maps preserve the full tensor Lie bracket. The mixed bracket vanishes because the two internal factors commute.

**Theorem 1.12 (Corner Jacobi identity).**

$$\forall A \in \operatorname{CommAlgebra}\left(\mathbb{R}\right), gYM \in \operatorname{LieAlgebra}\left(\mathbb{R}\right), L \in \operatorname{LieSubalgebra}\left(\operatorname{Der}\left(\mathbb{R}, A\right)\right),\; \forall x \in \operatorname{CornerAlgebra}\left(A, L, gYM\right), y \in \operatorname{CornerAlgebra}\left(A, L, gYM\right), z \in \operatorname{CornerAlgebra}\left(A, L, gYM\right),\; [x, [y, z]] + [y, [z, x]] + [z, [x, y]] = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/UnifiedCornerBF4D.corner_jacobi` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The derivation action and its commutator law give a semidirect Lie algebra. The cyclic Jacobi sum vanishes by the Lie derivation identity and skew symmetry.

**Definition 1.13 (Associative charge map).**

Lean statement: `D5/S3/Geometry/Lorentz/UnifiedCornerBF4D.quantumCharge`

*Formalization.* `D5/S3/Geometry/Lorentz/UnifiedCornerBF4D.quantumCharge` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The universal enveloping algebra gives the Lie homomorphism from corner generators into its associative commutator algebra.

**Theorem 1.14 (Enveloping commutator algebra).**

$$\forall A \in \operatorname{CommAlgebra}\left(\mathbb{R}\right), gYM \in \operatorname{LieAlgebra}\left(\mathbb{R}\right), L \in \operatorname{LieSubalgebra}\left(\operatorname{Der}\left(\mathbb{R}, A\right)\right),\; \forall u \in \operatorname{Tensor}\left(A, \operatorname{sl}\left(2, \mathbb{R}\right)\right), v \in \operatorname{Tensor}\left(A, \operatorname{sl}\left(2, \mathbb{R}\right)\right), l \in \operatorname{Tensor}\left(A, gYM\right), eta \in \operatorname{Tensor}\left(A, gYM\right),\; [\operatorname{Q}\left(\operatorname{G}\left(u\right)\right), \operatorname{Q}\left(\operatorname{G}\left(v\right)\right)] = \operatorname{Q}\left(\operatorname{G}\left([u, v]\right)\right) \land \left([\operatorname{Q}\left(\operatorname{Y}\left(l\right)\right), \operatorname{Q}\left(\operatorname{Y}\left(eta\right)\right)] = \operatorname{Q}\left(\operatorname{Y}\left([l, eta]\right)\right) \land [\operatorname{Q}\left(\operatorname{G}\left(u\right)\right), \operatorname{Q}\left(\operatorname{Y}\left(l\right)\right)] = 0\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/UnifiedCornerBF4D.enveloping_commutators` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The Lie homomorphism sends the normal and Yang–Mills brackets to the corresponding associative commutators, including vanishing mixed commutators.

**Definition 1.15 (Laurent derivations).**

Lean statement: `D5/S3/Geometry/Lorentz/UnifiedCornerBF4D.witt`

*Formalization.* `D5/S3/Geometry/Lorentz/UnifiedCornerBF4D.witt` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

On a Laurent monomial r zⁿ the mode indexed by m acts as −nr zᵐ⁺ⁿ. Finitely supported linear extension and the additive exponent law give the product rule.

**Theorem 1.16 (Laurent action on monomials).**

$$\forall m \in \mathbb{Z}, n \in \mathbb{Z}, r \in \mathbb{R},\; \left(L_{m}\right)\left(r \cdot z^{n}\right) = (-n \cdot r) \cdot z^{m + n}$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/UnifiedCornerBF4D.witt_monomial` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Application of the coefficient derivation to the Laurent monomial gives the shifted exponent and the factor −n.

**Theorem 1.17 (Witt bracket).**

$$\forall m \in \mathbb{Z}, n \in \mathbb{Z},\; [L_{m}, L_{n}] = (m - n) \cdot L_{m + n}$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/UnifiedCornerBF4D.witt_bracket` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Evaluating the commutator on every Laurent monomial yields the factor m−n multiplying the mode at m+n. Additive induction proves the equality on all Laurent polynomials.

**Theorem 1.18 (Laurent corner current modes).**

$$\forall gYM \in \operatorname{LieAlgebra}\left(\mathbb{R}\right), m \in \mathbb{Z}, n \in \mathbb{Z}, u \in \operatorname{sl}\left(2, \mathbb{R}\right) \times gYM, v \in \operatorname{sl}\left(2, \mathbb{R}\right) \times gYM,\; [\operatorname{P}\left(L_{m}\right), \operatorname{J}\left(z^{n}, u\right)] = (-n) \cdot \operatorname{J}\left(z^{m + n}, u\right) \land [\operatorname{J}\left(z^{m}, u\right), \operatorname{J}\left(z^{n}, v\right)] = \operatorname{J}\left(z^{m + n}, [u, v]\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/UnifiedCornerBF4D.laurent_current_modes` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The derivative of zⁿ under a Witt generator is −nzᵐ⁺ⁿ. The tangential-current bracket is thus the shifted current multiplied by −n, while the current-current bracket adds exponents and takes the internal commutator.

**Definition 1.19 (Finite jet coefficient algebra).**

Lean statement: `D5/S3/Geometry/Lorentz/UnifiedCornerBF4D.Jet`

*Formalization.* `D5/S3/Geometry/Lorentz/UnifiedCornerBF4D.Jet` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The polynomial ring is quotiented by the principal ideal generated by zᴺ.

**Definition 1.20 (Jet derivations).**

Lean statement: `D5/S3/Geometry/Lorentz/UnifiedCornerBF4D.jetWitt`

*Formalization.* `D5/S3/Geometry/Lorentz/UnifiedCornerBF4D.jetWitt` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The nonnegative Witt derivations on polynomials preserve the ideal generated by zᴺ, so they descend through the quotient map.

**Definition 1.21 (Jet monomials).**

Lean statement: `D5/S3/Geometry/Lorentz/UnifiedCornerBF4D.jetMonomial`

*Formalization.* `D5/S3/Geometry/Lorentz/UnifiedCornerBF4D.jetMonomial` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The residue class of the nth power of the polynomial variable is the nth jet monomial.

**Theorem 1.22 (Truncated multiplication and differentiation).**

$$\forall m \in \mathbb{N}, n \in \mathbb{N}, N \in \mathbb{N},\; \operatorname{jetWitt}\left(m, N\right)\left(\operatorname{jetMonomial}\left(N, n\right)\right) = (-n) \cdot \operatorname{jetMonomial}\left(N, m + n\right) \land \left(\operatorname{jetMonomial}\left(N, m\right) \cdot \operatorname{jetMonomial}\left(N, n\right) = \operatorname{jetMonomial}\left(N, m + n\right) \land \left(N \le n \Rightarrow \operatorname{jetMonomial}\left(N, n\right) = 0\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/UnifiedCornerBF4D.jet_rules` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Quotient multiplication adds exponents, and each monomial with exponent at least N vanishes. The descended derivation acts by −n times the monomial of degree m+n.

**Definition 1.23 (Normal quadratic invariant).**

Lean statement: `D5/S3/Geometry/Lorentz/UnifiedCornerBF4D.gravitationalCasimir`

*Formalization.* `D5/S3/Geometry/Lorentz/UnifiedCornerBF4D.gravitationalCasimir` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The normal quadratic invariant is one half of the trace of the square of a trace-zero matrix.

**Theorem 1.24 (Area Casimir polynomial).**

$$\forall M \in \operatorname{sl}\left(2, \mathbb{R}\right),\; \operatorname{CG}\left(M\right) = -\operatorname{det}\left(M\right) \land \operatorname{CG}\left(M\right) = M\left(0, 0\right)^{2} + M\left(0, 1\right) \cdot M\left(1, 0\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/UnifiedCornerBF4D.normal_area_casimir` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* W. Donnelly and L. Freidel (2016). *Local subsystems in gauge theory and gravity*. DOI: [10.1007/JHEP09(2016)102](https://doi.org/10.1007/JHEP09(2016)102). URL: <https://arxiv.org/abs/1601.04744>.

*Commentary.*

Trace zero determines the second diagonal entry to be minus the first. Expanding the trace of the square and determinant then gives a²+bc and minus the determinant.

**Theorem 1.25 (Infinitesimal adjoint invariance).**

$$\forall U \in \operatorname{sl}\left(2, \mathbb{R}\right), M \in \operatorname{sl}\left(2, \mathbb{R}\right),\; \frac{\operatorname{tr}\left([U, M] \cdot M + M \cdot [U, M]\right)}{2} = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/UnifiedCornerBF4D.normal_area_adjoint_invariant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Cyclic invariance of matrix trace cancels the linear variation of the quadratic invariant along a commutator.

**Theorem 1.26 (Exact quadratic adjoint variation).**

$$\forall U \in \operatorname{sl}\left(2, \mathbb{R}\right), M \in \operatorname{sl}\left(2, \mathbb{R}\right), t \in \mathbb{R},\; \operatorname{CG}\left(M + (t) \cdot [U, M]\right) = \operatorname{CG}\left(M\right) + t^{2} \cdot \operatorname{CG}\left([U, M]\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/UnifiedCornerBF4D.normal_area_variation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Expansion of the quadratic invariant along the affine line through the commutator direction has its linear term zero by cyclic trace.

**Definition 1.27 (Yang–Mills quadratic invariant).**

Lean statement: `D5/S3/Geometry/Lorentz/UnifiedCornerBF4D.ymCasimir`

*Formalization.* `D5/S3/Geometry/Lorentz/UnifiedCornerBF4D.ymCasimir` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The quadratic function on an internal momentum is its pairing with itself under the chosen invariant bilinear form.

**Theorem 1.28 (Yang–Mills infinitesimal invariance).**

$$\forall Y \in \operatorname{LieAlgebra}\left(\mathbb{R}\right), kappa \in \operatorname{Bilin}\left(\mathbb{R}, Y\right), u \in Y, nu \in Y, t \in \mathbb{R},\; \left(\forall x \in Y, a \in Y, b \in Y,\; kappa\left([x, a], b\right) = -kappa\left(a, [x, b]\right)\right) \Rightarrow \operatorname{CY}\left(kappa, nu + (t) \cdot [u, nu]\right) = \operatorname{CY}\left(kappa, nu\right) + t^{2} \cdot \operatorname{CY}\left(kappa, [u, nu]\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/UnifiedCornerBF4D.internal_casimir_invariant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Expand the quadratic function along the adjoint direction. Lie invariance of the pairing cancels the two linear terms, leaving the original value and the quadratic term.

**Definition 1.29 (Coordinate observables).**

Lean statement: `D5/S3/Geometry/Lorentz/UnifiedCornerBF4D.CornerObservable`

*Formalization.* `D5/S3/Geometry/Lorentz/UnifiedCornerBF4D.CornerObservable` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An observable takes the four real coordinates q, p, relative rapidity and area.

**Definition 1.30 (Darboux bracket).**

Lean statement: `D5/S3/Geometry/Lorentz/UnifiedCornerBF4D.cornerPoisson`

*Formalization.* `D5/S3/Geometry/Lorentz/UnifiedCornerBF4D.cornerPoisson` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The bracket is the sum of the antisymmetric products of the actual coordinate derivatives in the q,p and rapidity,area pairs.

**Definition 1.31 (Darboux generator H).**

Lean statement: `D5/S3/Geometry/Lorentz/UnifiedCornerBF4D.chartH`

*Formalization.* `D5/S3/Geometry/Lorentz/UnifiedCornerBF4D.chartH` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The diagonal generator is −2p.

**Definition 1.32 (Darboux generator E).**

Lean statement: `D5/S3/Geometry/Lorentz/UnifiedCornerBF4D.chartE`

*Formalization.* `D5/S3/Geometry/Lorentz/UnifiedCornerBF4D.chartE` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The positive generator is exp(q).

**Definition 1.33 (Darboux generator F).**

Lean statement: `D5/S3/Geometry/Lorentz/UnifiedCornerBF4D.chartF`

*Formalization.* `D5/S3/Geometry/Lorentz/UnifiedCornerBF4D.chartF` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The opposite generator is (area²−p²)exp(−q).

**Definition 1.34 (Relative rapidity).**

Lean statement: `D5/S3/Geometry/Lorentz/UnifiedCornerBF4D.chartRapidity`

*Formalization.* `D5/S3/Geometry/Lorentz/UnifiedCornerBF4D.chartRapidity` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The third coordinate is the relative rapidity.

**Definition 1.35 (Area coordinate).**

Lean statement: `D5/S3/Geometry/Lorentz/UnifiedCornerBF4D.chartArea`

*Formalization.* `D5/S3/Geometry/Lorentz/UnifiedCornerBF4D.chartArea` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The fourth coordinate is the area parameter.

**Theorem 1.36 (Exact Darboux brackets and area).**

$$\forall q \in \mathbb{R}, p \in \mathbb{R}, Gamma \in \mathbb{R}, A \in \mathbb{R},\; \{H, E\} = 2 \cdot E \land \left(\{H, F\} = -2 \cdot F \land \left(\{E, F\} = H \land \left(\frac{H^{2} + 4 \cdot E \cdot F}{4} = A^{2} \land \left(\{Gamma, A\} = 1 \land \{Gamma, F\} = 2 \cdot A \cdot \operatorname{exp}\left(-q\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/UnifiedCornerBF4D.area_boost_pair` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The coordinate derivatives of the generators give the three normal Lie brackets and the canonical rapidity–area bracket. The identity exp(q)exp(−q)=1 gives the quadratic Casimir equal to area squared. The rapidity bracket with F equals 2 area exp(−q).

**Definition 1.37 (Trace-dual moment matrix).**

Lean statement: `D5/S3/Geometry/Lorentz/UnifiedCornerBF4D.chartMoment`

*Formalization.* `D5/S3/Geometry/Lorentz/UnifiedCornerBF4D.chartMoment` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The moment matrix has diagonal entries H/2 and −H/2, upper entry F and lower entry E.

**Theorem 1.38 (Moment-map area).**

$$\forall q \in \mathbb{R}, p \in \mathbb{R}, Gamma \in \mathbb{R}, A \in \mathbb{R},\; \operatorname{CG}\left(\operatorname{chartMoment}\left(q, p, Gamma, A\right)\right) = A^{2}$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/UnifiedCornerBF4D.chart_moment_casimir` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The normal area formula applied to the trace-dual moment matrix yields area squared by the Darboux realization.

**Definition 1.39 (Real metric Hodge star).**

Lean statement: `D5/S3/Geometry/Lorentz/UnifiedCornerBF4D.realHodge`

*Formalization.* `D5/S3/Geometry/Lorentz/UnifiedCornerBF4D.realHodge` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The volume is the positive square root of the absolute metric determinant. The star is this volume times the wedge matrix times the exterior square of the inverse metric.

**Definition 1.40 (Determinant sign).**

Lean statement: `D5/S3/Geometry/Lorentz/UnifiedCornerBF4D.metricSign`

*Formalization.* `D5/S3/Geometry/Lorentz/UnifiedCornerBF4D.metricSign` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The sign parameter equals minus one for a negative metric determinant and plus one for a positive determinant.

**Theorem 1.41 (Real Hodge square and wedge adjoint).**

$$\forall g \in \operatorname{Mat}\left(4, 4, \mathbb{R}\right),\; \left(g^{T} = g \land \operatorname{det}\left(g\right) \ne 0\right) \Rightarrow \left(\operatorname{realHodge}\left(g\right) = \operatorname{hodge}\left(g, \sqrt{\left|\operatorname{det}\left(g\right)\right|}\right) \land \left(\left(\operatorname{metricSign}\left(g\right) = -1 \lor \operatorname{metricSign}\left(g\right) = 1\right) \land \left(\operatorname{realHodge}\left(g\right)^{2} = (\operatorname{metricSign}\left(g\right)) \cdot I \land \operatorname{realHodge}\left(g\right)^{T} \cdot \operatorname{W}\left(\mathbb{R}\right) = \operatorname{W}\left(\mathbb{R}\right) \cdot \operatorname{realHodge}\left(g\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/UnifiedCornerBF4D.real_hodge_structure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Urbantke (1984). *On integrability properties of SU(2) Yang-Mills fields. I. Infinitesimal part*. DOI: [10.1063/1.526402](https://doi.org/10.1063/1.526402). URL: <https://doi.org/10.1063/1.526402>.

*Commentary.*

Multiplicativity and the complementary-minor determinant identity for exterior squares give the Hodge square. Symmetry of the inverse metric and the wedge involution give wedge self-adjointness. The square is negative identity for negative determinant and positive identity for positive determinant, which includes Euclidean metrics.

**Theorem 1.42 (Chiral phase conversion).**

$$\forall B \in \operatorname{Mat}\left(6, 3, \mathbb{C}\right),\; \left(\operatorname{det}\left(\operatorname{Q}\left(B\right)\right) \ne 0 \land B^{T} \cdot \operatorname{W}\left(\mathbb{C}\right) \cdot \overline{B} = 0\right) \Rightarrow \left(\exists g \in \operatorname{Mat}\left(4, 4, \mathbb{R}\right), l \in \mathbb{C}, phase \in \mathbb{C},\; l \ne 0 \land \left(g^{T} = g \land \left(\operatorname{det}\left(g\right) < 0 \land \left(\operatorname{U}\left(B\right) = (l) \cdot \operatorname{complexify}\left(g\right) \land \left(\left(phase = i \lor phase = -i\right) \land \left(\operatorname{hodge}\left(\operatorname{U}\left(B\right), \operatorname{density}\left(B\right)\right) = (phase^{-1}) \cdot \operatorname{complexify}\left(\operatorname{realHodge}\left(g\right)\right) \land \operatorname{complexify}\left(\operatorname{realHodge}\left(g\right)\right) \cdot B = (phase) \cdot B\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/UnifiedCornerBF4D.urbantke_lorentz_phase` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Urbantke (1984). *On integrability properties of SU(2) Yang-Mills fields. I. Infinitesimal part*. DOI: [10.1063/1.526402](https://doi.org/10.1063/1.526402). URL: <https://doi.org/10.1063/1.526402>.

*Commentary.*

For a nondegenerate complex triple wedge-orthogonal to its conjugate, the Urbantke reconstruction supplies a real representative with negative determinant. If its complex scale is l and the oriented positive real volume is v, the chiral phase is l²v divided by the Urbantke density. Its square is −1 by the determinant identity, so the phase is either i or −i. Exterior scaling gives the real Hodge map times the inverse phase as the complex chiral star, and the triple is the corresponding eigenspace.

**Theorem 1.43 (Real triple and positive Hodge square).**

$$\forall B \in \operatorname{Mat}\left(6, 3, \mathbb{R}\right),\; \operatorname{det}\left(\operatorname{Q}\left(B\right)\right) \ne 0 \Rightarrow \left(0 < \operatorname{det}\left(\operatorname{U}\left(B\right)\right) \land \operatorname{realHodge}\left(\operatorname{U}\left(B\right)\right)^{2} = I\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/UnifiedCornerBF4D.urbantke_real_hodge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Urbantke (1984). *On integrability properties of SU(2) Yang-Mills fields. I. Infinitesimal part*. DOI: [10.1063/1.526402](https://doi.org/10.1063/1.526402). URL: <https://doi.org/10.1063/1.526402>.

*Commentary.*

The determinant of the cubic reconstruction is the square of the wedge Gram determinant divided by 64. A real nondegenerate triple therefore has a positive determinant and a Hodge operator squaring to the identity.

**Theorem 1.44 (Lorentzian null screen).**

$$\forall r \in \operatorname{FutureNullRay}\left(\mathbb{C}\right),\; \operatorname{realHodge}\left(\operatorname{diag}\left(-1, 1, 1, 1\right)\right)^{2} = -I \land \left(\left(\forall a \in \operatorname{Fin}\left(2\right),\; \operatorname{screenFrame}\left(r, a\right)^{T} \cdot \operatorname{diag}\left(-1, 1, 1, 1\right) \cdot \operatorname{nullGenerator}\left(r\right) = 0\right) \land \left(\forall a \in \operatorname{Fin}\left(2\right), b \in \operatorname{Fin}\left(2\right),\; \left(a = b \Rightarrow \operatorname{screenFrame}\left(r, a\right)^{T} \cdot \operatorname{diag}\left(-1, 1, 1, 1\right) \cdot \operatorname{screenFrame}\left(r, b\right) = 1\right) \land \left(a \ne b \Rightarrow \operatorname{screenFrame}\left(r, a\right)^{T} \cdot \operatorname{diag}\left(-1, 1, 1, 1\right) \cdot \operatorname{screenFrame}\left(r, b\right) = 0\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/UnifiedCornerBF4D.null_screen_hodge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the diagonal metric with entries −1,1,1,1, the real Hodge operator squares to minus identity. The screen vectors are orthogonal to the null generator and have Euclidean Gram matrix in this metric.

**Definition 1.45 (Block-split BF density).**

Lean statement: `D5/S3/Geometry/Lorentz/UnifiedCornerBF4D.bfDensity`

*Formalization.* `D5/S3/Geometry/Lorentz/UnifiedCornerBF4D.bfDensity` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

With the gravitational term fixed, the Yang–Mills term is the wedge pairing of the auxiliary field with curvature minus half the squared coupling times the pairing with its Hodge transform.

**Definition 1.46 (Auxiliary-field stationarity).**

Lean statement: `D5/S3/Geometry/Lorentz/UnifiedCornerBF4D.bfStationary`

*Formalization.* `D5/S3/Geometry/Lorentz/UnifiedCornerBF4D.bfStationary` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Stationarity requires the first variation coefficient to vanish against every variation of the auxiliary field.

**Theorem 1.47 (Exact BF variation).**

$$\forall V \in \operatorname{VectorSpace}\left(\mathbb{R}\right), W \in \operatorname{Bilin}\left(\mathbb{R}, V\right), J \in \operatorname{End}\left(\mathbb{R}, V\right),\; \forall LG \in \mathbb{R}, g \in \mathbb{R}, t \in \mathbb{R}, F \in V, B \in V, v \in V,\; \left(\left(\forall x \in V, y \in V,\; W\left(x, y\right) = W\left(y, x\right)\right) \land \left(\forall x \in V, y \in V,\; W\left(J\left(x\right), y\right) = W\left(x, J\left(y\right)\right)\right)\right) \Rightarrow \operatorname{bfDensity}\left(W, J, LG, g, F, B + (t) \cdot v\right) = \operatorname{bfDensity}\left(W, J, LG, g, F, B\right) + t \cdot W\left(v, F - (g^{2}) \cdot J\left(B\right)\right) - \frac{g^{2}}{2} \cdot t^{2} \cdot W\left(v, J\left(v\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/UnifiedCornerBF4D.bf_variation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Bilinearity, symmetry and wedge self-adjointness give the full quadratic variation in the scalar parameter. The coefficient of the linear term is the pairing with F−g²JB.

**Definition 1.48 (Critical field).**

Lean statement: `D5/S3/Geometry/Lorentz/UnifiedCornerBF4D.bfCritical`

*Formalization.* `D5/S3/Geometry/Lorentz/UnifiedCornerBF4D.bfCritical` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The candidate stationary field is the signed Hodge transform of the curvature divided by the squared coupling.

**Theorem 1.49 (Unique stationary auxiliary field).**

$$\forall V \in \operatorname{VectorSpace}\left(\mathbb{R}\right), W \in \operatorname{Bilin}\left(\mathbb{R}, V\right), J \in \operatorname{End}\left(\mathbb{R}, V\right),\; \forall s \in \mathbb{R}, g \in \mathbb{R}, F \in V, B \in V,\; \left(\left(\forall x \in V,\; \left(\forall v \in V,\; W\left(v, x\right) = 0\right) \Rightarrow x = 0\right) \land \left(s^{2} = 1 \land \left(\left(\forall x \in V,\; J\left(J\left(x\right)\right) = (s) \cdot x\right) \land g \ne 0\right)\right)\right) \Rightarrow \left(\operatorname{bfStationary}\left(W, J, g, F, B\right) \Leftrightarrow B = \operatorname{bfCritical}\left(J, s, g, F\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/UnifiedCornerBF4D.bf_stationary_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Nondegeneracy reduces all vanishing first coefficients to g²JB=F. The star squares to the sign times identity, so when the coupling is nonzero this equation has the stated unique solution.

**Theorem 1.50 (BF completion of the square).**

$$\forall V \in \operatorname{VectorSpace}\left(\mathbb{R}\right), W \in \operatorname{Bilin}\left(\mathbb{R}, V\right), J \in \operatorname{End}\left(\mathbb{R}, V\right),\; \forall s \in \mathbb{R}, g \in \mathbb{R}, LG \in \mathbb{R}, F \in V, B \in V,\; \left(\left(\forall x \in V, y \in V,\; W\left(x, y\right) = W\left(y, x\right)\right) \land \left(\left(\forall x \in V, y \in V,\; W\left(J\left(x\right), y\right) = W\left(x, J\left(y\right)\right)\right) \land \left(s^{2} = 1 \land \left(\left(\forall x \in V,\; J\left(J\left(x\right)\right) = (s) \cdot x\right) \land g \ne 0\right)\right)\right)\right) \Rightarrow \operatorname{bfDensity}\left(W, J, LG, g, F, B\right) = LG + \frac{s}{2 \cdot g^{2}} \cdot W\left(F, J\left(F\right)\right) - \frac{g^{2}}{2} \cdot W\left(B - \operatorname{bfCritical}\left(J, s, g, F\right), J\left(B - \operatorname{bfCritical}\left(J, s, g, F\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/UnifiedCornerBF4D.bf_complete_square` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Translate the auxiliary field by the stationary field. The exact variation has no linear term, and its constant term uses g²JB*=F. Symmetry converts the stationary BF pairing into the signed curvature pairing divided by the squared coupling.

**Theorem 1.51 (Zero coupling degeneracy).**

$$\forall V \in \operatorname{VectorSpace}\left(\mathbb{R}\right), W \in \operatorname{Bilin}\left(\mathbb{R}, V\right), J \in \operatorname{End}\left(\mathbb{R}, V\right),\; \forall F \in V, B \in V,\; \left(\forall x \in V,\; \left(\forall v \in V,\; W\left(v, x\right) = 0\right) \Rightarrow x = 0\right) \Rightarrow \left(\operatorname{bfStationary}\left(W, J, 0, F, B\right) \Leftrightarrow F = 0\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/UnifiedCornerBF4D.bf_zero_coupling` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At zero coupling the first variation is independent of the auxiliary field. Nondegeneracy then makes it vanish precisely when the curvature is zero.

**Definition 1.52 (Yang–Mills wedge metric).**

Lean statement: `D5/S3/Geometry/Lorentz/UnifiedCornerBF4D.colorWedge`

*Formalization.* `D5/S3/Geometry/Lorentz/UnifiedCornerBF4D.colorWedge` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The wedge matrix is tensored with the symmetric color pairing using the Kronecker product.

**Definition 1.53 (Hodge on colored forms).**

Lean statement: `D5/S3/Geometry/Lorentz/UnifiedCornerBF4D.colorHodge`

*Formalization.* `D5/S3/Geometry/Lorentz/UnifiedCornerBF4D.colorHodge` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The real Hodge matrix acts on form indices while the identity acts on color indices.

**Theorem 1.54 (Metric BF reduction).**

$$\forall iota \in FiniteIndexType, metric \in \operatorname{Mat}\left(4, 4, \mathbb{R}\right), kappa \in \operatorname{Mat}\left(iota, iota, \mathbb{R}\right),\; \forall g \in \mathbb{R}, LG \in \mathbb{R}, F \in \mathbb{R}^{6 \times card\left(iota\right)}, B \in \mathbb{R}^{6 \times card\left(iota\right)},\; \left(metric^{T} = metric \land \left(\operatorname{det}\left(metric\right) \ne 0 \land \left(kappa^{T} = kappa \land \left(\operatorname{det}\left(kappa\right) \ne 0 \land g \ne 0\right)\right)\right)\right) \Rightarrow \left(\left(\operatorname{bfStationary}\left(\operatorname{colorWedge}\left(kappa\right), \operatorname{colorHodge}\left(metric\right), g, F, B\right) \Leftrightarrow B = \operatorname{bfCritical}\left(\operatorname{colorHodge}\left(metric\right), \operatorname{metricSign}\left(metric\right), g, F\right)\right) \land \operatorname{bfDensity}\left(\operatorname{colorWedge}\left(kappa\right), \operatorname{colorHodge}\left(metric\right), LG, g, F, B\right) = LG + \frac{\operatorname{metricSign}\left(metric\right)}{2 \cdot g^{2}} \cdot \operatorname{colorWedge}\left(kappa\right)\left(F, \operatorname{colorHodge}\left(metric\right)\left(F\right)\right) - \frac{g^{2}}{2} \cdot \operatorname{colorWedge}\left(kappa\right)\left(B - \operatorname{bfCritical}\left(\operatorname{colorHodge}\left(metric\right), \operatorname{metricSign}\left(metric\right), g, F\right), \operatorname{colorHodge}\left(metric\right)\left(B - \operatorname{bfCritical}\left(\operatorname{colorHodge}\left(metric\right), \operatorname{metricSign}\left(metric\right), g, F\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/UnifiedCornerBF4D.urbantke_bf_yang_mills` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Urbantke (1984). *On integrability properties of SU(2) Yang-Mills fields. I. Infinitesimal part*. DOI: [10.1063/1.526402](https://doi.org/10.1063/1.526402). URL: <https://doi.org/10.1063/1.526402>.

*Commentary.*

The determinant of the wedge matrix is nonzero because it squares to identity. Kronecker multiplication transports symmetry, nondegeneracy, wedge adjointness and the Hodge square to the color space. The abstract BF stationarity and completion identities therefore apply for every symmetric invertible real metric and symmetric invertible color pairing.

**Theorem 1.55 (Signed on-shell density).**

$$\forall iota \in FiniteIndexType, metric \in \operatorname{Mat}\left(4, 4, \mathbb{R}\right), kappa \in \operatorname{Mat}\left(iota, iota, \mathbb{R}\right),\; \forall g \in \mathbb{R}, LG \in \mathbb{R}, F \in \mathbb{R}^{6 \times card\left(iota\right)},\; \left(metric^{T} = metric \land \left(\operatorname{det}\left(metric\right) \ne 0 \land \left(kappa^{T} = kappa \land \left(\operatorname{det}\left(kappa\right) \ne 0 \land g \ne 0\right)\right)\right)\right) \Rightarrow \left(\left(\operatorname{det}\left(metric\right) < 0 \Rightarrow \operatorname{bfDensity}\left(\operatorname{colorWedge}\left(kappa\right), \operatorname{colorHodge}\left(metric\right), LG, g, F, \operatorname{bfCritical}\left(\operatorname{colorHodge}\left(metric\right), \operatorname{metricSign}\left(metric\right), g, F\right)\right) = LG - \frac{1}{2 \cdot g^{2}} \cdot \operatorname{colorWedge}\left(kappa\right)\left(F, \operatorname{colorHodge}\left(metric\right)\left(F\right)\right)\right) \land \left(0 \le \operatorname{det}\left(metric\right) \Rightarrow \operatorname{bfDensity}\left(\operatorname{colorWedge}\left(kappa\right), \operatorname{colorHodge}\left(metric\right), LG, g, F, \operatorname{bfCritical}\left(\operatorname{colorHodge}\left(metric\right), \operatorname{metricSign}\left(metric\right), g, F\right)\right) = LG + \frac{1}{2 \cdot g^{2}} \cdot \operatorname{colorWedge}\left(kappa\right)\left(F, \operatorname{colorHodge}\left(metric\right)\left(F\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/UnifiedCornerBF4D.urbantke_bf_on_shell` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Urbantke (1984). *On integrability properties of SU(2) Yang-Mills fields. I. Infinitesimal part*. DOI: [10.1063/1.526402](https://doi.org/10.1063/1.526402). URL: <https://doi.org/10.1063/1.526402>.

*Commentary.*

Substituting the stationary field makes the translated quadratic term vanish. A negative determinant gives coefficient −1/(2g²), and a positive determinant gives coefficient +1/(2g²).

## References

- Truth anchor: `D5/S3/Geometry/Lorentz/UnifiedCornerBF4D.CornerAlgebra`
- Truth anchor: `D5/S3/Geometry/Lorentz/UnifiedCornerBF4D.CornerCurrent`
- Truth anchor: `D5/S3/Geometry/Lorentz/UnifiedCornerBF4D.CornerInternal`
- Truth anchor: `D5/S3/Geometry/Lorentz/UnifiedCornerBF4D.CornerObservable`
- Truth anchor: `D5/S3/Geometry/Lorentz/UnifiedCornerBF4D.G`
- Truth anchor: `D5/S3/Geometry/Lorentz/UnifiedCornerBF4D.J`
- Truth anchor: `D5/S3/Geometry/Lorentz/UnifiedCornerBF4D.Jet`
- Truth anchor: `D5/S3/Geometry/Lorentz/UnifiedCornerBF4D.P`
- Truth anchor: `D5/S3/Geometry/Lorentz/UnifiedCornerBF4D.Y`
- Truth anchor: `D5/S3/Geometry/Lorentz/UnifiedCornerBF4D.area_boost_pair`
- Truth anchor: `D5/S3/Geometry/Lorentz/UnifiedCornerBF4D.bfCritical`
- Truth anchor: `D5/S3/Geometry/Lorentz/UnifiedCornerBF4D.bfDensity`
- Truth anchor: `D5/S3/Geometry/Lorentz/UnifiedCornerBF4D.bfStationary`
- Truth anchor: `D5/S3/Geometry/Lorentz/UnifiedCornerBF4D.bf_complete_square`
- Truth anchor: `D5/S3/Geometry/Lorentz/UnifiedCornerBF4D.bf_stationary_iff`
- Truth anchor: `D5/S3/Geometry/Lorentz/UnifiedCornerBF4D.bf_variation`
- Truth anchor: `D5/S3/Geometry/Lorentz/UnifiedCornerBF4D.bf_zero_coupling`
- Truth anchor: `D5/S3/Geometry/Lorentz/UnifiedCornerBF4D.chartArea`
- Truth anchor: `D5/S3/Geometry/Lorentz/UnifiedCornerBF4D.chartE`
- Truth anchor: `D5/S3/Geometry/Lorentz/UnifiedCornerBF4D.chartF`
- Truth anchor: `D5/S3/Geometry/Lorentz/UnifiedCornerBF4D.chartH`
- Truth anchor: `D5/S3/Geometry/Lorentz/UnifiedCornerBF4D.chartMoment`
- Truth anchor: `D5/S3/Geometry/Lorentz/UnifiedCornerBF4D.chartRapidity`
- Truth anchor: `D5/S3/Geometry/Lorentz/UnifiedCornerBF4D.chart_moment_casimir`
- Truth anchor: `D5/S3/Geometry/Lorentz/UnifiedCornerBF4D.colorHodge`
- Truth anchor: `D5/S3/Geometry/Lorentz/UnifiedCornerBF4D.colorWedge`
- Truth anchor: `D5/S3/Geometry/Lorentz/UnifiedCornerBF4D.cornerDerivationHom`
- Truth anchor: `D5/S3/Geometry/Lorentz/UnifiedCornerBF4D.cornerPoisson`
- Truth anchor: `D5/S3/Geometry/Lorentz/UnifiedCornerBF4D.corner_bracket`
- Truth anchor: `D5/S3/Geometry/Lorentz/UnifiedCornerBF4D.corner_internal_brackets`
- Truth anchor: `D5/S3/Geometry/Lorentz/UnifiedCornerBF4D.corner_jacobi`
- Truth anchor: `D5/S3/Geometry/Lorentz/UnifiedCornerBF4D.currentDerivation`
- Truth anchor: `D5/S3/Geometry/Lorentz/UnifiedCornerBF4D.enveloping_commutators`
- Truth anchor: `D5/S3/Geometry/Lorentz/UnifiedCornerBF4D.gravitationalCasimir`
- Truth anchor: `D5/S3/Geometry/Lorentz/UnifiedCornerBF4D.internal_casimir_invariant`
- Truth anchor: `D5/S3/Geometry/Lorentz/UnifiedCornerBF4D.jetMonomial`
- Truth anchor: `D5/S3/Geometry/Lorentz/UnifiedCornerBF4D.jetWitt`
- Truth anchor: `D5/S3/Geometry/Lorentz/UnifiedCornerBF4D.jet_rules`
- Truth anchor: `D5/S3/Geometry/Lorentz/UnifiedCornerBF4D.laurent_current_modes`
- Truth anchor: `D5/S3/Geometry/Lorentz/UnifiedCornerBF4D.metricSign`
- Truth anchor: `D5/S3/Geometry/Lorentz/UnifiedCornerBF4D.normal_area_adjoint_invariant`
- Truth anchor: `D5/S3/Geometry/Lorentz/UnifiedCornerBF4D.normal_area_casimir`
- Truth anchor: `D5/S3/Geometry/Lorentz/UnifiedCornerBF4D.normal_area_variation`
- Truth anchor: `D5/S3/Geometry/Lorentz/UnifiedCornerBF4D.null_screen_hodge`
- Truth anchor: `D5/S3/Geometry/Lorentz/UnifiedCornerBF4D.quantumCharge`
- Truth anchor: `D5/S3/Geometry/Lorentz/UnifiedCornerBF4D.realHodge`
- Truth anchor: `D5/S3/Geometry/Lorentz/UnifiedCornerBF4D.real_hodge_structure`
- Truth anchor: `D5/S3/Geometry/Lorentz/UnifiedCornerBF4D.urbantke_bf_on_shell`
- Truth anchor: `D5/S3/Geometry/Lorentz/UnifiedCornerBF4D.urbantke_bf_yang_mills`
- Truth anchor: `D5/S3/Geometry/Lorentz/UnifiedCornerBF4D.urbantke_lorentz_phase`
- Truth anchor: `D5/S3/Geometry/Lorentz/UnifiedCornerBF4D.urbantke_real_hodge`
- Truth anchor: `D5/S3/Geometry/Lorentz/UnifiedCornerBF4D.witt`
- Truth anchor: `D5/S3/Geometry/Lorentz/UnifiedCornerBF4D.witt_bracket`
- Truth anchor: `D5/S3/Geometry/Lorentz/UnifiedCornerBF4D.witt_monomial`
- Truth anchor: `D5/S3/Geometry/Lorentz/UnifiedCornerBF4D.ymCasimir`
- Dependency: [D5/S3/Geometry/Lorentz/Urbantke](Urbantke.md)
- Dependency: [D5/S3/Geometry/Lorentz/WeylNullScreen](WeylNullScreen.md)
