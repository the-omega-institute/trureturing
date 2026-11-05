# Homogeneous and parity representatives for sums of squares

## Abstract

Homogeneous and parity representatives for sums of squares

These are polynomial prerequisites for the genuine all-level GNP characterization. They do not themselves establish the tensor-moment bridge or any extension-cone characterization. The full package remains incomplete until those proofs and the normal acceptance are present.

**Theorem 1.1 (Homogeneous square representatives).**

Lean statement: `D5/S3/QuadraticForms/HomogeneousSOS.homogeneous_sos_iff`

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/HomogeneousSOS.homogeneous_sos_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real homogeneous polynomial of degree twice d, the native unrestricted IsSumSq predicate is equivalent to a finite sum of squares of homogeneous degree-d forms. Positivity of real evaluations removes all lower-degree components; zero forms and d=0 are retained.

**Theorem 1.2 (Parity square representatives).**

Lean statement: `D5/S3/QuadraticForms/HomogeneousSOS.homogeneous_parity_sos_iff`

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/HomogeneousSOS.homogeneous_parity_sos_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In a finite grading group with a+a=0, a polynomial in the zero sector has an SOS representation whose half-degree forms each lie in an individual sector. Projecting a square to sector zero cancels all cross-sector products. The predicate remains the native unrestricted sum of squares.

**Theorem 1.3 (Even-form SOS decomposition).**

Lean statement: `D5/S3/QuadraticForms/HomogeneousSOS.even_form_sos_iff`

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/HomogeneousSOS.even_form_sos_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The genuine substitution X_i to X_i squared converts a homogeneous real form to a native sum of squares exactly when the original form is a finite sum of binary square-free monomials times squares of homogeneous forms. Every nonzero summand has the exact degree relation. Multiple square terms in one parity sector are retained. This formalizes the polynomial decomposition underlying GNP Proposition 8.10; it is not the full GNP tensor characterization.

## References

- Truth anchor: `D5/S3/QuadraticForms/HomogeneousSOS.even_form_sos_iff`
- Truth anchor: `D5/S3/QuadraticForms/HomogeneousSOS.homogeneous_parity_sos_iff`
- Truth anchor: `D5/S3/QuadraticForms/HomogeneousSOS.homogeneous_sos_iff`
