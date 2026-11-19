# Part II Unitriangular Lang Linear

## Abstract

Root weights and terminating coordinate dynamics for the unitriangular Lang map.

Let F be any field, n a natural rank and a a unit of F. A matrix has depth r when its entries below the r-th superdiagonal vanish. Multiplication adds depths. On strict-upper matrices, delta multiplies the (i,j) entry by a^(j-i)-1; nonresonance permits division by every such root weight.

Under nonresonance, for a strict-upper target b the coordinate equation delta(a)(X) = b + b*X becomes X = deltaInv(a)(b) + T_b(X), where T_b is deltaInv after left multiplication by b. Division preserves depth and left multiplication by b raises it, so T_b^(n-1) vanishes on strict-upper inputs. The inverse coordinate is therefore the finite sum over range(n-1). In ranks zero and one, strict-upper inputs are zero and this sum is empty.

**Definition 1.1 (Nonresonant).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIUnitriangularLangLinear.Nonresonant`

*Formalization.* `D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIUnitriangularLangLinear.Nonresonant` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Nonresonance means a^d != 1 for every positive distance d < n over the given field. In ranks zero and one this condition is vacuous.

**Theorem 1.2 (finite solution equation).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIUnitriangularLangLinear.finiteSolution_equation`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIUnitriangularLangLinear.finiteSolution_equation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under nonresonance, for a strict-upper target b put T_b(X) = deltaInv(a)(b*X), with multiplication by b performed first on the left. The sum of T_b^k(deltaInv(a)(b)) over 0 <= k < n-1 solves delta(a)(X) = b + b*X. Each application raises depth by one, so the terminal iterate vanishes.

**Theorem 1.3 (finite solution unique).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIUnitriangularLangLinear.finiteSolution_unique`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIUnitriangularLangLinear.finiteSolution_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under nonresonance, every strict-upper solution of the coordinate equation equals the finite Neumann sum. The two geometric telescoping identities give existence and uniqueness on strict-upper inputs.

## References

- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIUnitriangularLangLinear.Nonresonant`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIUnitriangularLangLinear.finiteSolution_equation`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIUnitriangularLangLinear.finiteSolution_unique`
- Dependency: [D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIUnitriangularLayers](PartIIUnitriangularLayers.md)
