# Actual Hecke Coefficient Field Degree

## Abstract

The exact first-m Fourier-coefficient field of a normalized actual prime-Hecke eigenform has degree at most m.

Let m>=1, s in {0,4,6,8,10,14}, and f be an actual Mathlib level-one cusp form of weight 12m+s. Write c_n for its qExpansion at period 1. Assume c_1=1 and, for every prime p, the actual operator primeHecke p satisfies T_p f=eigenvalue_p*f. The same f, operator and all-prime eigenvalue family are used throughout.

**Theorem 1.1 (Finite-dimensionality and the exact cusp-dimension degree bound).**

Lean statement: `D5/S3/Arith/ModularForms/HeckeCoefficientFieldDegree.normalized_primeHecke_coefficient_field_degree`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/ModularForms/HeckeCoefficientFieldDegree.normalized_primeHecke_coefficient_field_degree` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The concrete intermediate field K=adjoin Q {c_1,...,c_m} inside C is finite-dimensional over Q and satisfies finrank Q K<=m. The conclusion concerns this exact first-m field, not an existential replacement number field or a bound only on each individual eigenvalue.

The proof first establishes K=adjoin Q {eigenvalue_p:p prime}. Public integralMillerBasis reconstruction and millerForm_coefficient express every c_n as an integer-coefficient linear combination of the first m coefficients, so every c_n lies in K. The actual primeHecke_qExpansion_coeff at index 1 gives eigenvalue_p=c_p, placing the eigenvalue field inside K.

Conversely, for an arbitrary rational intermediate field E containing every eigenvalue, strong induction puts every c_n in E. The bases are the cusp identity c_0=0 and normalization c_1=1. For n>=2 choose a prime divisor p and r=n/p<n. The actual Hecke law expresses c_n as eigenvalue_p*c_r minus p^(weight-1) times c_(r/p) when p divides r. Both smaller indices are covered by induction, and a rational intermediate field is closed under the actual integer power, including inverses. No nonzero-eigenvalue assumption or division by an eigenvalue is used.

Take the first-m vector x=millerCoefficientEquiv f and the rational casts of integerMillerHeckeMatrix. The existing millerHecke_conjugacy gives exactly the common eigenpairs of those same actual analytic operators. Normalization makes x nonzero. CommonEigenvalueFieldDegree bounds the full prime-eigenvalue field by card(Fin m)=m, and the proved equality transfers the bound and finite-dimensionality to K.

The actual field-equality connection is new content on the live proof path, in addition to the generic row-character supplier. The existing integral-lattice-preservation theorem is not repackaged. This degree theorem does not assert algebraic integrality of the coefficients, irreducibility of Hecke characteristic polynomials, Maeda's conjecture or mathematical originality.

## References

- Truth anchor: `D5/S3/Arith/ModularForms/HeckeCoefficientFieldDegree.normalized_primeHecke_coefficient_field_degree`
- Dependency: [D5/S1/Eigenstructure/CommonEigenvalueFieldDegree](../../../S1/Eigenstructure/CommonEigenvalueFieldDegree.md)
- Dependency: [D5/S3/Arith/ModularForms/FiniteHeckeArray](FiniteHeckeArray.md)
