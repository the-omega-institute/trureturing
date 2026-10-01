# Isometric orbit metrics

## Abstract

Compatible metrics and compact closed balls for quotients of isometric representations.

For a group represented by isometries of a metric space, the distance between two orbits is the infimum of the distances to translates of one representative. Proper discontinuity makes this a metric with the existing quotient topology. If the original metric space is proper, the quotient is proper as well. Neither freeness nor compactness of the quotient is assumed. These statements do not establish a smooth hyperbolic structure, finite volume or rigidity.

**Definition 1.1 (Distance between orbits).**

Lean statement: `D5/S3/Geometry/IsometricOrbitMetric.orbitDistance`

*Formalization.* `D5/S3/Geometry/IsometricOrbitMetric.orbitDistance` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* M. Kapovich (2023). *A note on properly discontinuous actions*. DOI: [10.1007/s40863-023-00353-z](https://doi.org/10.1007/s40863-023-00353-z). URL: <https://www.math.ucdavis.edu/~kapovich/EPR/prop-disc.pdf>.

*Commentary.*

Changing either representative reindexes the group orbit. Isometry invariance of distance to a set then gives a well-defined real-valued function on orbit classes.

**Definition 1.2 (Metric with the quotient topology).**

Lean statement: `D5/S3/Geometry/IsometricOrbitMetric.orbitMetricSpace`

*Formalization.* `D5/S3/Geometry/IsometricOrbitMetric.orbitMetricSpace` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* M. Kapovich (2023). *A note on properly discontinuous actions*. DOI: [10.1007/s40863-023-00353-z](https://doi.org/10.1007/s40863-023-00353-z). URL: <https://www.math.ucdavis.edu/~kapovich/EPR/prop-disc.pdf>.

*Commentary.*

Inverting a group element gives symmetry; composing two group elements and taking infima gives the triangle inequality. Open quotient sets contain orbit-distance balls, and their preimages contain ordinary metric balls. The Hausdorff orbit quotient of a properly discontinuous action has closed orbit fibers, so zero distance identifies the same orbit.

**Definition 1.3 (Compact closed balls in the quotient).**

Lean statement: `D5/S3/Geometry/IsometricOrbitMetric.orbitProperSpace`

*Formalization.* `D5/S3/Geometry/IsometricOrbitMetric.orbitProperSpace` (`✓ std3`).

*Citation.* M. Kapovich (2023). *A note on properly discontinuous actions*. DOI: [10.1007/s40863-023-00353-z](https://doi.org/10.1007/s40863-023-00353-z). URL: <https://www.math.ucdavis.edu/~kapovich/EPR/prop-disc.pdf>.

*Commentary.*

For a proper ambient space, distance to a nonempty closed orbit is attained. Consequently each quotient closed ball is exactly the projection of the closed ball about any chosen representative. The continuous projection maps that compact ball to a compact quotient ball. Kapovich, Lemma 21(2), gives this classical properness argument; the Library note records its hypotheses and the representation convention.

## References

- Truth anchor: `D5/S3/Geometry/IsometricOrbitMetric.orbitDistance`
- Truth anchor: `D5/S3/Geometry/IsometricOrbitMetric.orbitMetricSpace`
- Truth anchor: `D5/S3/Geometry/IsometricOrbitMetric.orbitProperSpace`
- Dependency: [D5/S3/Geometry/MostowPrasadCovering](MostowPrasadCovering.md)
