# Exact positive expansivity on circles glued along the Cantor set

## Abstract

Exact positive expansivity on circles glued along the Cantor set

Tripling on the additive circle preserves the image of the ternary Cantor set. The induced map on finitely many copies glued along that image is continuous and surjective.

**Theorem 1.1 (Points enter the Cantor image after one iterate).**

Lean statement: `D5/S1/Dynamics/Shadowing/CantorCircleExpansivity.exists_near_coalescing_point`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/CantorCircleExpansivity.exists_near_coalescing_point` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Take positive Cantor points x approaching zero. The points (1 + x)/3 lie in the open middle third, approach the Cantor endpoint 1/3, and triple to x modulo one.

**Theorem 1.2 (The least expansion order is the number of circles).**

Lean statement: `D5/S1/Dynamics/Shadowing/CantorCircleExpansivity.exact_order`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/CantorCircleExpansivity.exact_order` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Take N at least two. At a small scale a strict forward Bowen ball projects to one point of the circle. Its fiber contains at most N points. At every positive scale there is a fiber of N distinct points with arbitrarily small diameter whose points all agree after one iterate.

The carrier is compact and connected because it is a finite union of compact connected circles sharing the image of the Cantor set.

## References

- Truth anchor: `D5/S1/Dynamics/Shadowing/CantorCircleExpansivity.exact_order`
- Truth anchor: `D5/S1/Dynamics/Shadowing/CantorCircleExpansivity.exists_near_coalescing_point`
- Dependency: [D5/S1/Dynamics/Shadowing/CircleFinitePositiveExpansiveness/Basic](CircleFinitePositiveExpansiveness/Basic.md)
- Dependency: [D5/S1/Dynamics/Shadowing/InvarianceGluedSheets](InvarianceGluedSheets.md)
