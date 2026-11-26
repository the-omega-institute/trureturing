# Saturation and integral basis extension

## Abstract

Integral bases of primitive intersections

**Definition 1.1 (Three compatible integral bases).**

Lean statement: `D5/S3/Combinatorics/Lattices/EuclideanSaturation.Adapted`

*Formalization.* `D5/S3/Combinatorics/Lattices/EuclideanSaturation.Adapted` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Daniel R. Grayson (1984). *Reduction theory using semistability*. DOI: [10.1007/BF02566369](https://doi.org/10.1007/BF02566369).

*Commentary.*

Given integral submodules A and B and an integral basis c of their intersection, adapted bases are a basis (c,a) of A, a basis (c,b) of B and a basis (c,a,b) of their sum. The bases have exactly the same vectors in their common blocks.

**Definition 1.2 (Simultaneous bases for saturated submodules).**

Lean statement: `D5/S3/Combinatorics/Lattices/EuclideanSaturation.adaptedBasesOfSaturated`

*Formalization.* `D5/S3/Combinatorics/Lattices/EuclideanSaturation.adaptedBasesOfSaturated` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Daniel R. Grayson (1984). *Reduction theory using semistability*. DOI: [10.1007/BF02566369](https://doi.org/10.1007/BF02566369).

*Commentary.*

Let A and B be finitely generated saturated submodules of an integral submodule L in a characteristic-zero vector space. Any basis c of their intersection extends to compatible bases of A and B and to a basis of their sum. No topology or finite dimension of the ambient vector space is required.

Saturation makes the quotients of A and B by their intersection torsion-free. These finite modules over the integers are free, so both quotient maps admit linear sections. Take the product of the intersection and the two quotients, and map a triple to its intersection vector plus its two lifted quotient vectors. Decomposing a vector of the sum into vectors of A and B proves surjectivity.

For injectivity, a triple mapping to zero has its lifted A vector in B, hence in the intersection. Its quotient coordinate vanishes. The B coordinate then vanishes for the same reason, followed by the intersection coordinate. Transport the product of the three integral bases through this linear equivalence. The corresponding two-factor equivalences give the bases of A and B with the same lifted vectors.

## References

- Truth anchor: `D5/S3/Combinatorics/Lattices/EuclideanSaturation.Adapted`
- Truth anchor: `D5/S3/Combinatorics/Lattices/EuclideanSaturation.adaptedBasesOfSaturated`
