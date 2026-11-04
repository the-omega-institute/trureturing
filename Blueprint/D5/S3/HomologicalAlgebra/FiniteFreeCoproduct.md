# Finite coordinates for an integer coproduct

## Abstract

Finite coordinates for an integer coproduct.

**Definition 1.1 (Concrete finite coordinates).**

Lean statement: `D5/S3/HomologicalAlgebra/FiniteFreeCoproduct.coordinateIso`

*Formalization.* `D5/S3/HomologicalAlgebra/FiniteFreeCoproduct.coordinateIso` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For decidable types I and J with I finite and a bijection e from I to J, the categorical coproduct of copies of the integer module indexed by J is isomorphic to integer-valued functions on I. The construction uses the concrete finitely supported coproduct cocone, reindexes by e, and passes to finite function coordinates.

**Theorem 1.2 (Every summand inclusion).**

Lean statement: `D5/S3/HomologicalAlgebra/FiniteFreeCoproduct.ι_coordinateIso`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/FiniteFreeCoproduct.ι_coordinateIso` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every j in J, the summand map followed by the coordinate isomorphism sends z to the function equal to z at the unique i with e(i)=j and zero elsewhere. This identifies the actual categorical inclusion with the finite basis map.

**Theorem 1.3 (Standard basis vectors).**

Lean statement: `D5/S3/HomologicalAlgebra/FiniteFreeCoproduct.coordinateIso_basis`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/FiniteFreeCoproduct.coordinateIso_basis` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each i in I, one in the e(i) summand maps to Pi.single i 1. The formula identifies the basis vectors in the signed boundary comparisons.

## References

- Truth anchor: `D5/S3/HomologicalAlgebra/FiniteFreeCoproduct.coordinateIso`
- Truth anchor: `D5/S3/HomologicalAlgebra/FiniteFreeCoproduct.coordinateIso_basis`
- Truth anchor: `D5/S3/HomologicalAlgebra/FiniteFreeCoproduct.ι_coordinateIso`
