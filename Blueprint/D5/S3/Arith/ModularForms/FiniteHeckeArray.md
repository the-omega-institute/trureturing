# Finite Hecke coefficient arrays

## Abstract

Finite q-expansion arrays transport the project's actual prime Hecke operator to the first Miller coordinates.

**Definition 1.1 (Finite coefficient array).**

Lean statement: `D5/S3/Arith/ModularForms/FiniteHeckeArray.finiteCoefficientArray_apply`

*Formalization.* `D5/S3/Arith/ModularForms/FiniteHeckeArray.finiteCoefficientArray_apply` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

finiteCoefficientArray f N is the coefficient table indexed by Fin (N+1), so index i stores the actual analytic q-expansion coefficient a(f,i). The table includes the constant term and every coefficient through q^N.

**Theorem 1.2 (Prime Hecke coordinate from finite precision).**

Lean statement: `D5/S3/Arith/ModularForms/FiniteHeckeArray.primeHeckeFiniteCoordinate_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/ModularForms/FiniteHeckeArray.primeHeckeFiniteCoordinate_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a prime p and i in Fin m, the coefficient a(T_p f,i+1) is exactly read from the source array of length p*m+1: use entry p*(i+1), and, when p divides i+1, add p^(k-1) times entry (i+1)/p. The proof rewrites the existing actual analytic coefficient law; the array indices are proved to lie below p*m+1.

**Theorem 1.3 (The first m Hecke coefficients use only q^(p*m)).**

Lean statement: `D5/S3/Arith/ModularForms/FiniteHeckeArray.primeHecke_first_coefficients_from_array`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/ModularForms/FiniteHeckeArray.primeHecke_first_coefficients_from_array` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The first m nonconstant coefficients of T_p f are therefore determined by the finite source table through q^(p*m), equivalently by truncation modulo q^(p*m+1). For p=2 this is the 2*m+1 precision required by the T_2 matrix route.

**Theorem 1.4 (Finite Hecke entries on the Miller basis).**

Lean statement: `D5/S3/Arith/ModularForms/FiniteHeckeArray.primeHeckeMillerMatrix_apply_basis`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/ModularForms/FiniteHeckeArray.primeHeckeMillerMatrix_apply_basis` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Using the constructed integral Miller basis and its coefficient equivalence, each entry of primeHeckeMillerMatrix is the first-coordinate value of the project's actual analytic T_p applied to the corresponding Miller form. This is a complex matrix transport statement; integer-entry and characteristic-polynomial integrality remain subsequent obligations.

The module does not define a substitute coefficient operator and does not claim a Maeda result. It only packages the existing analytic Hecke law into a finite, executable index interface suitable for the next integer matrix and characteristic-polynomial step.

## References

- Truth anchor: `D5/S3/Arith/ModularForms/FiniteHeckeArray.finiteCoefficientArray_apply`
- Truth anchor: `D5/S3/Arith/ModularForms/FiniteHeckeArray.primeHeckeFiniteCoordinate_eq`
- Truth anchor: `D5/S3/Arith/ModularForms/FiniteHeckeArray.primeHeckeMillerMatrix_apply_basis`
- Truth anchor: `D5/S3/Arith/ModularForms/FiniteHeckeArray.primeHecke_first_coefficients_from_array`
- Dependency: [D5/S3/Arith/ModularForms/ActualPrimeHecke](ActualPrimeHecke.md)
- Dependency: [D5/S3/Arith/ModularForms/IntegralMillerBasis](IntegralMillerBasis.md)
