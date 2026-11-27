# One-dimensional continua of every finite positive expansivity order

## Abstract

One-dimensional continua of every finite positive expansivity order

**Theorem 1.1 (Finite graph sheets over a circle have covering dimension at most one).**

Lean statement: `D5/S3/Topology/CoveringDimension/GluedCircle.atMost_one_gluedCircle`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/CoveringDimension/GluedCircle.atMost_one_gluedCircle` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A metric sphere on the circle has at most two points. Balls therefore give a basis of open sets with finite frontiers. The projection of finitely many compact graph sheets onto the base is closed with finite fibers, so the covering-dimension bound pulls back.

**Theorem 1.2 (Every order N at least two occurs on a one-dimensional continuum).**

Lean statement: `D5/S3/Topology/CoveringDimension/GluedCircle.cantorCircle_exactOrder_oneDimensional`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/CoveringDimension/GluedCircle.cantorCircle_exactOrder_oneDimensional` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Glue N circles along the ternary Cantor image and apply tripling on each circle. The carrier is a nontrivial connected compact metric space. Its covering dimension is exactly one by the closed finite-to-one projection and the connectedness lower bound.

The induced continuous surjection has a positive scale at which every strict forward Bowen ball contains at most N points. At each positive scale some ball contains at least N points. This is an existence result within Gangloff, Guillon and Oprocha's Question 3.2, which asks for a classification of one-dimensional continua.

## References

- Truth anchor: `D5/S3/Topology/CoveringDimension/GluedCircle.atMost_one_gluedCircle`
- Truth anchor: `D5/S3/Topology/CoveringDimension/GluedCircle.cantorCircle_exactOrder_oneDimensional`
- Dependency: [D5/S1/Dynamics/Shadowing/CantorCircleExpansivity](../../../S1/Dynamics/Shadowing/CantorCircleExpansivity.md)
- Dependency: [D5/S3/Topology/CoveringDimension/FiniteFrontier](FiniteFrontier.md)
