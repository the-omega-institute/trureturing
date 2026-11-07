# Complete Common Phase Polynomial Invariants

## Abstract

Faithful actual common-phase polynomial invariants, quadratic generation and unique Hermitian representation.

**Theorem 1.1 (Diagonal coefficient formula).**

$$(\forall sigma: Type, (\forall R: Type, [\operatorname{CommRing}(R)] (\forall d: (sigma \to R), (\forall f: \operatorname{MvPolynomial}(sigma, R), (\forall m: \operatorname{Exponent}(sigma), (\operatorname{coeff}(\operatorname{aevalDiag}(d, f), m) = (\operatorname{exponentProduct}(m, d) \cdot \operatorname{coeff}(f, m))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/CommonPhasePolynomial.coeff_aeval_diag` (`✓ std3`). ∎

*Citation.* Joseph Tooby-Smith (2026). *Physlib charge balance and infinite-order unitary phase*. URL: <https://github.com/leanprover-community/physlib/tree/a8823c76303bab825824ddecb7bd540880c4ae62/PhyslibAlpha/Particles/BeyondTheStandardModel/TwoHDM>.

*Commentary.*

For any commutative ring R and any variable type sigma, aevalDiag(d,f) substitutes C(d(i))*X(i) into f. Exponent(sigma) is sigma to finitely supported natural numbers. ExponentProduct(m,d) is the product over the support of m of d(i) raised to m(i). The coefficient of m after substitution is that product times the original coefficient.

**Theorem 1.2 (Charge balance).**

$$(\forall sigma: Type, (\forall K: Type, [\operatorname{Field}(K)] (\forall w: (sigma \to \mathbb{Z}), (\forall c: K, ((c \neq 0) \implies ((\forall n: \mathbb{Z}, ((\operatorname{zpow}(c, n) = 1) \implies (n = 0))) \implies (\forall f: \operatorname{MvPolynomial}(sigma, K), ((\operatorname{chargeSubstitution}(w, c, f) = f) \implies (\forall m: \operatorname{Exponent}(sigma), ((\operatorname{charge}(w, m) \neq 0) \implies (\operatorname{coeff}(f, m) = 0)))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/CommonPhasePolynomial.coeff_eq_zero_of_charge_ne_zero` (`✓ std3`). ∎

*Citation.* Joseph Tooby-Smith (2026). *Physlib charge balance and infinite-order unitary phase*. URL: <https://github.com/leanprover-community/physlib/tree/a8823c76303bab825824ddecb7bd540880c4ae62/PhyslibAlpha/Particles/BeyondTheStandardModel/TwoHDM>.

*Commentary.*

For a field K, integer weights w and a nonzero scalar c, assume c^n=1 only for n=0 among all integers. ChargeSubstitution substitutes C(c raised to w(i))*X(i). Formal invariance under this substitution forces a coefficient to vanish whenever the sum over its finite exponent support of m(i)*w(i) is nonzero. No assumption about actual conjugate evaluation belongs to this supplier; that bridge is established separately.

**Theorem 1.3 (An infinite-order complex unitary phase).**

$$(\exists w: \operatorname{unitary}(\mathbb{C}), (\forall n: \mathbb{Z}, ((\operatorname{zpow}(w, n) = 1) \implies (n = 0))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/CommonPhasePolynomial.exists_infiniteOrder_unitary` (`✓ std3`). ∎

*Citation.* Joseph Tooby-Smith (2026). *Physlib charge balance and infinite-order unitary phase*. URL: <https://github.com/leanprover-community/physlib/tree/a8823c76303bab825824ddecb7bd540880c4ae62/PhyslibAlpha/Particles/BeyondTheStandardModel/TwoHDM>.

*Commentary.*

There exists a complex unitary scalar with no nontrivial integer power equal to one. The phase exp(i) has this property by irrationality of pi.

**Theorem 1.4 (Actual evaluation).**

$$(\forall iota: Type, (\forall p: \operatorname{Poly}(iota), (\forall z: (iota \to \mathbb{C}), (\operatorname{eval}(\operatorname{cartesian}(z), \operatorname{toCartesian}(p)) = \operatorname{actual}(p, z)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/CommonPhasePolynomial.actual_cartesian` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Poly(iota) is the polynomial algebra over the complex numbers on iota plus a second copy of iota. Coefficients and finite supports are unrestricted. The first copy represents z and the second its conjugate. Cartesian substitution sends these variables to x+iy and x-iy. Actual evaluation sets the second copy to the complex conjugate of the first. For every vector, Cartesian evaluation after substitution equals actual evaluation.

**Theorem 1.5 (Faithfulness on the actual conjugate diagonal).**

$$(\forall iota: Type, \operatorname{Injective}(\operatorname{actual}(iota)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/CommonPhasePolynomial.actual_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Two paired-variable polynomials agreeing at every actual complex vector are equal. This follows by the invertible Cartesian substitution and polynomial extensionality on a product of infinite real axes. No injectivity on the conjugate diagonal is assumed. The coordinate type may be empty and need not be finite for this statement.

**Theorem 1.6 (Total degree correspondence).**

$$(\forall iota: Type, (\forall p: \operatorname{Poly}(iota), (\operatorname{totalDegree}(\operatorname{toCartesian}(p)) = \operatorname{totalDegree}(p))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/CommonPhasePolynomial.cartesian_totalDegree` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Both inverse substitutions are linear homogeneous substitutions. Each weakly decreases total degree, so invertibility gives equality. The natural total-degree convention includes degree zero for the zero polynomial. Constants and arbitrary degrees remain in scope.

**Theorem 1.7 (Unique expansion of real-coordinate polynomials).**

$$(\forall iota: Type, (\forall q: \operatorname{Poly}(iota), (\exists! p: \operatorname{Poly}(iota), (\forall z: (iota \to \mathbb{C}), (\operatorname{actual}(p, z) = \operatorname{eval}(\operatorname{cartesian}(z), q))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/CommonPhasePolynomial.real_coordinates_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every polynomial in the real and imaginary coordinates has exactly one expansion in z and its conjugate with the same actual values. Complex coefficients permit all complex-valued polynomial functions on the underlying real coordinate space; real coefficients are included through their canonical embedding. The inverse substitution is x=(z+w)/2 and y=(z-w)/(2i).

**Theorem 1.8 (Homogeneous degree correspondence).**

$$(\forall iota: Type, (\forall p: \operatorname{Poly}(iota), (\forall n: \mathbb{N}, (\operatorname{IsHomogeneous}(\operatorname{toCartesian}(p), n) \iff \operatorname{IsHomogeneous}(p, n)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/CommonPhasePolynomial.cartesian_homogeneous` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural n, the polynomial is homogeneous of degree n exactly when its Cartesian image is. This uses the homogeneous substitution theorem in both directions. The zero polynomial is homogeneous of every degree, and no nonzero hypothesis is imposed.

**Theorem 1.9 (Unrestricted balanced-monomial generation).**

$$(\forall iota: Type, [\operatorname{Fintype}(iota)] (\forall m: \operatorname{PairedExponent}(iota), ((\operatorname{holo}(m) = \operatorname{anti}(m)) \implies (\operatorname{monomial}(m, 1) \in \operatorname{quadraticAlgebra}(iota)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/CommonPhasePolynomial.balanced_monomial_mem_quadratic_adjoin` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

PairedExponent(iota) denotes finitely supported natural exponents on the two copies of iota. Holo and anti are the sums on the first and second copy. QuadraticAlgebra is the complex subalgebra generated by all X(inl i) times X(inr j). Equal totals give membership by induction: when the common total is positive, select one positive exponent on each side, subtract that pair, and multiply the inductively obtained element by its quadratic generator. At total zero the monomial is one. The proof requires no supplied factorization certificate and includes empty coordinate types.

**Theorem 1.10 (Actual invariance, balance and generation).**

$$(\forall iota: Type, [\operatorname{Fintype}(iota)] (\forall p: \operatorname{Poly}(iota), ((\operatorname{Invariant}(p) \iff \operatorname{Balanced}(p)) \land (\operatorname{Invariant}(p) \iff (p \in \operatorname{quadraticAlgebra}(iota))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/CommonPhasePolynomial.common_phase_polynomial_theorem` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Invariant means equality of actual values under multiplication of every coordinate by exp(i theta), for every complex vector and every real theta. Balanced means every nonzero coefficient has equal holomorphic and antiholomorphic totals. Faithful actual evaluation converts phase invariance into formal diagonal invariance. The diagonal charge theorem eliminates nonzero charges using an infinite-order unitary phase. Every balanced monomial then lies in the quadratic algebra by constructive pairing. Conversely every generator and hence every element of its generated algebra is invariant. Zero, constants, empty support and unrestricted degrees are included.

**Theorem 1.11 (Generation in the algebra of actual functions).**

$$(\forall iota: Type, [\operatorname{Fintype}(iota)] (\forall p: \operatorname{Poly}(iota), (\operatorname{Invariant}(p) \implies (\operatorname{actual}(p) \in \operatorname{actualQuadraticAlgebra}(iota)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/CommonPhasePolynomial.actual_quadratic_generation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

ActualQuadraticAlgebra is the complex subalgebra of all functions from complex coordinate vectors to complex values generated by the functions z_i times conjugate(z_j), with ordinary pointwise operations. Every invariant actual polynomial belongs to this algebra. The evaluation algebra homomorphism sends the formal generated algebra to this actual generated algebra.

**Theorem 1.12 (Lower bound for nonconstant invariants).**

$$(\forall iota: Type, [\operatorname{Fintype}(iota)] (\forall p: \operatorname{Poly}(iota), (\operatorname{Invariant}(p) \implies (\neg (\exists c: \mathbb{C}, (p = \operatorname{C}(c))) \implies (2 \leq \operatorname{totalDegree}(p))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/CommonPhasePolynomial.invariant_minimum_degree` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every invariant which is not a constant polynomial has total degree at least two. Under balance, a nonzero supported exponent has total degree twice its holomorphic total. Degree less than two therefore leaves only the constant monomial. This implication makes no positive-dimension assumption.

**Theorem 1.13 (Attainment in positive dimension).**

$$(\forall iota: Type, [\operatorname{Fintype}(iota)] (\forall i: iota, (\operatorname{Invariant}(\operatorname{quadraticGenerator}(i, i)) \land (\operatorname{totalDegree}(\operatorname{quadraticGenerator}(i, i)) = 2))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/CommonPhasePolynomial.invariant_degree_two` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Any supplied coordinate i gives the invariant z_i times its conjugate with degree exactly two. Supplying i expresses positive dimension; no nonconstant polynomial is asserted to exist when the coordinate type is empty.

**Theorem 1.14 (Uniqueness from actual values).**

$$(\forall iota: Type, [\operatorname{Fintype}(iota)] (\forall H: \operatorname{Matrix}(iota, iota, \mathbb{C}), (\forall K: \operatorname{Matrix}(iota, iota, \mathbb{C}), ((\forall z: (iota \to \mathbb{C}), (\operatorname{starDotMul}(H, z) = \operatorname{starDotMul}(K, z))) \implies (H = K)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/CommonPhasePolynomial.actual_quadratic_matrix_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

StarDotMul(H,z) denotes star(z) dot (H times z). Equality of this value for every actual complex vector forces equality of H and K, with no Hermitian assumption. The proof identifies each matrix with its complex-linear map on the finite Euclidean space and directly applies Mathlib's ext_inner_map supplier to the normalized inner-product equality. The empty matrix case is included.

**Theorem 1.15 (Unique Hermitian representation).**

$$(\forall iota: Type, [\operatorname{Fintype}(iota)] (\forall p: \operatorname{Poly}(iota), (\operatorname{Invariant}(p) \implies (\operatorname{IsHomogeneous}(p, 2) \implies ((\forall z: (iota \to \mathbb{C}), (\operatorname{im}(\operatorname{actual}(p, z)) = 0)) \implies (\exists! H: \operatorname{Matrix}(iota, iota, \mathbb{C}), (\operatorname{IsHermitian}(H) \land (\forall z: (iota \to \mathbb{C}), (\operatorname{actual}(p, z) = \operatorname{starDotMul}(H, z))) \land (\forall i: iota, (\forall j: iota, (\operatorname{entry}(H, j, i) = \operatorname{coeff}(p, \operatorname{pairExponent}(i, j))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/CommonPhasePolynomial.invariant_quadratic_hermitian` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any finite coordinate type, every actual common-phase invariant polynomial which is homogeneous of degree two and real-valued at every complex vector has exactly one Hermitian matrix H whose quadratic form equals its actual values. The coefficient c_ij of z_i times conjugate(z_j) is placed at H_ji. Balanced degree-two exponents contain exactly one variable from each copy, so these coefficients construct the matrix. Real-valuedness gives symmetry of the associated Euclidean linear map and hence the Hermitian property through the existing inner-product and matrix theorems. Uniqueness uses equality of actual values alone. Zero and dimension zero remain included.

**Theorem 1.16 (Nonnegative values and positive semidefiniteness).**

$$(\forall iota: Type, [\operatorname{Fintype}(iota)] (\forall p: \operatorname{Poly}(iota), (\operatorname{Invariant}(p) \implies (\operatorname{IsHomogeneous}(p, 2) \implies ((\forall z: (iota \to \mathbb{C}), (\operatorname{im}(\operatorname{actual}(p, z)) = 0)) \implies ((\forall z: (iota \to \mathbb{C}), (0 \leq \operatorname{re}(\operatorname{actual}(p, z)))) \iff \operatorname{PosSemidef}(\operatorname{coefficientMatrix}(p))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/CommonPhasePolynomial.invariant_quadratic_nonnegative_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an actual real-valued homogeneous quadratic phase invariant, nonnegativity of the real part of every value is equivalent to Matrix.PosSemidef of its coefficient matrix. Reality makes the imaginary part zero. Complex.nonneg_iff then converts real nonnegativity into the complex order used by the matrix predicate. The proof applies the existing Hermitian dot-product characterization of positive semidefiniteness.

**Theorem 1.17 (Complete polynomial statement).**

$$(\forall iota: Type, [\operatorname{Fintype}(iota)] (\forall p: \operatorname{Poly}(iota), ((\exists! q: \operatorname{Poly}(iota), (\forall z: (iota \to \mathbb{C}), (\operatorname{actual}(q, z) = \operatorname{eval}(\operatorname{cartesian}(z), p)))) \land (\operatorname{totalDegree}(\operatorname{toCartesian}(p)) = \operatorname{totalDegree}(p)) \land (\forall n: \mathbb{N}, (\operatorname{IsHomogeneous}(\operatorname{toCartesian}(p), n) \iff \operatorname{IsHomogeneous}(p, n))) \land (\operatorname{Invariant}(p) \iff \operatorname{Balanced}(p)) \land (\operatorname{Invariant}(p) \iff (p \in \operatorname{quadraticAlgebra}(iota))) \land (\operatorname{Invariant}(p) \implies (\operatorname{actual}(p) \in \operatorname{actualQuadraticAlgebra}(iota))) \land (\operatorname{Invariant}(p) \implies (\neg (\exists c: \mathbb{C}, (p = \operatorname{C}(c))) \implies (2 \leq \operatorname{totalDegree}(p)))) \land (\forall i: iota, (\operatorname{Invariant}(\operatorname{quadraticGenerator}(i, i)) \land (\operatorname{totalDegree}(\operatorname{quadraticGenerator}(i, i)) = 2))) \land (\operatorname{IsHomogeneous}(p, 2) \implies ((\forall z: (iota \to \mathbb{C}), (\operatorname{im}(\operatorname{actual}(p, z)) = 0)) \implies (\operatorname{Invariant}(p) \implies (\exists! H: \operatorname{Matrix}(iota, iota, \mathbb{C}), (\operatorname{IsHermitian}(H) \land (\forall z: (iota \to \mathbb{C}), (\operatorname{actual}(p, z) = \operatorname{starDotMul}(H, z))) \land (\forall i: iota, (\forall j: iota, (\operatorname{entry}(H, j, i) = \operatorname{coeff}(p, \operatorname{pairExponent}(i, j))))) \land ((\forall z: (iota \to \mathbb{C}), (0 \leq \operatorname{re}(\operatorname{actual}(p, z)))) \iff \operatorname{PosSemidef}(H)) \land (\forall K: \operatorname{Matrix}(iota, iota, \mathbb{C}), ((\forall z: (iota \to \mathbb{C}), (\operatorname{actual}(p, z) = \operatorname{starDotMul}(K, z))) \implies (K = H)))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/CommonPhasePolynomial.complete_common_phase_polynomial_theorem` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

All coordinate types in this statement are arbitrary finite types, including the empty type. Poly(iota) has arbitrary complex coefficients, finite support and degree. Holo and anti sum exponents over the two copies of the coordinate type. Balanced requires equal totals for every nonzero monomial coefficient. Invariant quantifies over every actual complex vector and every real phase angle. QuadraticAlgebra is generated by every z_i times conjugate(z_j); its generation assertion is proved by constructive monomial pairing. The statement retains the unique real-coordinate correspondence, actual evaluation, total and homogeneous degree correspondence, both invariant characterizations, the degree lower bound, degree-two attainment for any supplied coordinate, and the unique Hermitian and nonnegative/PSD conclusions for real-valued homogeneous quadratics. PairExponent(i,j) is single(inl i,1)+single(inr j,1), and entry(coefficientMatrix(p),j,i)=coeff(p,pairExponent(i,j)). Empty dimension gives constants and the unique empty matrix, with no assertion of a nonconstant invariant. StarDotMul(H,z) means star(z) dot (H times z). The statement concerns polynomial functions on the whole coordinate space and introduces no physical probability or quotient-topology assumption.

## References

- Truth anchor: `D5/S3/Quantum/Algebra/CommonPhasePolynomial.actual_cartesian`
- Truth anchor: `D5/S3/Quantum/Algebra/CommonPhasePolynomial.actual_injective`
- Truth anchor: `D5/S3/Quantum/Algebra/CommonPhasePolynomial.actual_quadratic_generation`
- Truth anchor: `D5/S3/Quantum/Algebra/CommonPhasePolynomial.actual_quadratic_matrix_unique`
- Truth anchor: `D5/S3/Quantum/Algebra/CommonPhasePolynomial.balanced_monomial_mem_quadratic_adjoin`
- Truth anchor: `D5/S3/Quantum/Algebra/CommonPhasePolynomial.cartesian_homogeneous`
- Truth anchor: `D5/S3/Quantum/Algebra/CommonPhasePolynomial.cartesian_totalDegree`
- Truth anchor: `D5/S3/Quantum/Algebra/CommonPhasePolynomial.coeff_aeval_diag`
- Truth anchor: `D5/S3/Quantum/Algebra/CommonPhasePolynomial.coeff_eq_zero_of_charge_ne_zero`
- Truth anchor: `D5/S3/Quantum/Algebra/CommonPhasePolynomial.common_phase_polynomial_theorem`
- Truth anchor: `D5/S3/Quantum/Algebra/CommonPhasePolynomial.complete_common_phase_polynomial_theorem`
- Truth anchor: `D5/S3/Quantum/Algebra/CommonPhasePolynomial.exists_infiniteOrder_unitary`
- Truth anchor: `D5/S3/Quantum/Algebra/CommonPhasePolynomial.invariant_degree_two`
- Truth anchor: `D5/S3/Quantum/Algebra/CommonPhasePolynomial.invariant_minimum_degree`
- Truth anchor: `D5/S3/Quantum/Algebra/CommonPhasePolynomial.invariant_quadratic_hermitian`
- Truth anchor: `D5/S3/Quantum/Algebra/CommonPhasePolynomial.invariant_quadratic_nonnegative_iff`
- Truth anchor: `D5/S3/Quantum/Algebra/CommonPhasePolynomial.real_coordinates_unique`
