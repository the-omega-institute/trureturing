# Homogeneous and parity representatives for sums of squares

## Abstract

Homogeneous and parity representatives for sums of squares

These polynomial results supply the homogeneous and parity decompositions used by the all-level GNP characterization in BoseHierarchy. The tensor-operator bridge is constructed in BoseSOSCertificates and BoseSOSDuality.

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

Let sigma be any variable type, Gamma a finite additive commutative group satisfying a+a=0 for every a, and w : sigma to Gamma any grading. For every real polynomial p : MvPolynomial sigma Real and natural number d, assume p.IsHomogeneous (2*d) and p.IsWeightedHomogeneous w 0. Then the native unrestricted IsSumSq p holds if and only if there exist a natural number m and q : Fin m to Gamma to MvPolynomial sigma Real such that, for every i and a, q(i,a) is homogeneous of degree d and weighted-homogeneous for w in sector a, and p is the finite sum over i : Fin m and a : Gamma of q(i,a) times q(i,a).

Projecting each homogeneous square to sector zero cancels all cross-sector products; conversely the displayed finite sum is a native sum of squares. The zero polynomial, d=0 and an empty square family m=0 remain in scope.

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
