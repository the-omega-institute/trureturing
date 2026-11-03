# Finite-degree sesquilinear pairing

## Abstract

Finite degree support makes a raising-power geometric inclusion an isometry for a sesquilinear basis pairing.

The full-telescope escape audit remains unfinished for every public theorem in this source, including its support and expansion helpers. The missing realization, exact reconstruction, lawful template application, whole-family variation, sensitivity and observational-dependence evidence is disclosed at https://github.com/the-omega-institute/trureturing/issues/25857. The issue is not a validated registration. The original BRST operators have not been shown here to satisfy hH or hA; cohomology, no-ghost and the full programme remain outside this result.

Let b be a genuine basis of a complex module V. Supported b P x means that every nonzero basis coefficient of x satisfies P. A sesquilinear form is expanded over the finite supports of both arguments, with conjugation in its first coefficient. The degree map d is integer-valued, so the selection rule d i + d j = 0 remains valid for signed degrees.

**Theorem 1.1 (Finite double expansion).**

Lean statement: `D5/S3/VertexAlgebra/Pairing/FiniteDegreePairing.form_expansion`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Pairing/FiniteDegreePairing.form_expansion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The form of two arbitrary vectors is the finite double sum of basis coefficients and basis pairings. The first coefficient is conjugated by the semilinear map.

**Theorem 1.2 (Sector-preserving degree growth).**

Lean statement: `D5/S3/VertexAlgebra/Pairing/FiniteDegreePairing.raising_power_support`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Pairing/FiniteDegreePairing.raising_power_support` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An operator whose basis transitions preserve the sector and raise d by at least one sends a d=0 sector-supported vector through (-A)^r into the same sector with degree at least r. This is an algebraic support statement and does not construct the operator from BRST data.

**Theorem 1.3 (All positive cross terms vanish).**

Lean statement: `D5/S3/VertexAlgebra/Pairing/FiniteDegreePairing.powers_orthogonal`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Pairing/FiniteDegreePairing.powers_orthogonal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The signed degree selection rule and the two lower degree bounds force every pairing H ((-A)^r x) ((-A)^s y) to vanish when r+s is positive. The proof expands the finite supports and cancels every basis cross term individually.

**Theorem 1.4 (Finite geometric inclusion isometry).**

Lean statement: `D5/S3/VertexAlgebra/Pairing/FiniteDegreePairing.finite_inclusion_isometry`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Pairing/FiniteDegreePairing.finite_inclusion_isometry` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For n at least one, the finite geometric sum from r=0 through n-1 has the same pairing as its r=0 inclusion on d=0 sector-supported vectors. The preceding cross-term theorem removes every summand except (0,0); no positivity, nondegeneracy, inverse, nilpotence or analytic completion is assumed.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Pairing/FiniteDegreePairing.finite_inclusion_isometry`
- Truth anchor: `D5/S3/VertexAlgebra/Pairing/FiniteDegreePairing.form_expansion`
- Truth anchor: `D5/S3/VertexAlgebra/Pairing/FiniteDegreePairing.powers_orthogonal`
- Truth anchor: `D5/S3/VertexAlgebra/Pairing/FiniteDegreePairing.raising_power_support`
