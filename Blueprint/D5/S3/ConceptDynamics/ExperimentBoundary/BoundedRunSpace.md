# Bounded Runs and Coherent Prefixes

## Abstract

Run restrictions, finite words, and coherent prefixes share one Boolean coordinate alphabet.

**Definition 1.1 (Infinite run restriction).**

Lean statement: `D5/S3/ConceptDynamics/ExperimentBoundary/BoundedRunSpace.bounded`

*Formalization.* `D5/S3/ConceptDynamics/ExperimentBoundary/BoundedRunSpace.bounded` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A stream is a function from the natural numbers to Bool. For every starting coordinate j, bounded(read,k) requires an index i less than k whose observed bit read(x(j+i)) is false. The identity readout forbids k consecutive true bits.

**Definition 1.2 (Finite run language).**

Lean statement: `D5/S3/ConceptDynamics/ExperimentBoundary/BoundedRunSpace.language`

*Formalization.* `D5/S3/ConceptDynamics/ExperimentBoundary/BoundedRunSpace.language` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A word of length n is a function from Fin n to Bool. The same run condition is checked precisely at starts j with j+k at most n. Length zero has the unique empty word. Truncation restricts coordinates; zeroExtend appends false bits.

**Definition 1.3 (Union over run bounds).**

Lean statement: `D5/S3/ConceptDynamics/ExperimentBoundary/BoundedRunSpace.union`

*Formalization.* `D5/S3/ConceptDynamics/ExperimentBoundary/BoundedRunSpace.union` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The union ranges over every natural k at least two. A member has one bound that controls all starting coordinates, rather than a bound chosen separately at each finite length.

**Definition 1.4 (Coherent prefixes).**

Lean statement: `D5/S3/ConceptDynamics/ExperimentBoundary/BoundedRunSpace.Threads`

*Formalization.* `D5/S3/ConceptDynamics/ExperimentBoundary/BoundedRunSpace.Threads` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A thread contains one word of every natural length, including zero. Restricting the word at length n+1 to length n gives the preceding word. prefixes sends a stream to its prefixes; threadStream reads coordinate j at length j+1.

**Definition 1.5 (Comparison of the two limits).**

Lean statement: `D5/S3/ConceptDynamics/ExperimentBoundary/BoundedRunSpace.comparison`

*Formalization.* `D5/S3/ConceptDynamics/ExperimentBoundary/BoundedRunSpace.comparison` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

fixedLimit requires every word in a thread to satisfy one fixed run bound. unionLimits takes their ordinary union over bounds at least two. limitUnions allows a separate bound at each length. comparison retains exactly the same thread and only changes its membership proof.

**Definition 1.6 (Fair independent product law).**

Lean statement: `D5/S3/ConceptDynamics/ExperimentBoundary/BoundedRunSpace.fairMeasure`

*Formalization.* `D5/S3/ConceptDynamics/ExperimentBoundary/BoundedRunSpace.fairMeasure` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The measure is productLaw at success probability one half, on the ambient Boolean stream space with its product topology and Borel sigma algebra. It is the independent product of equal point masses at true and false.

**Definition 1.7 (Aligned block event).**

Lean statement: `D5/S3/ConceptDynamics/ExperimentBoundary/BoundedRunSpace.aligned`

*Formalization.* `D5/S3/ConceptDynamics/ExperimentBoundary/BoundedRunSpace.aligned` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The event checks m disjoint blocks of length k, at starts r*k for r in Fin m. Each checked block contains a false observed bit. Sliding windows that cross block boundaries impose additional conditions in bounded(read,k).

**Definition 1.8 (Complete union boundary).**

Lean statement: `D5/S3/ConceptDynamics/ExperimentBoundary/BoundedRunSpace.Boundary`

*Formalization.* `D5/S3/ConceptDynamics/ExperimentBoundary/BoundedRunSpace.Boundary` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Boundary collects strict inclusion, closedness, exact prefix images, finite language and truncation compatibility, density, properness, Borel measurability, the null measure and full-measure closure, the continuous coherent-prefix identification, the non-surjective comparison, both quantifier orders, and the exact aligned-block probability.

## References

- Truth anchor: `D5/S3/ConceptDynamics/ExperimentBoundary/BoundedRunSpace.Boundary`
- Truth anchor: `D5/S3/ConceptDynamics/ExperimentBoundary/BoundedRunSpace.Threads`
- Truth anchor: `D5/S3/ConceptDynamics/ExperimentBoundary/BoundedRunSpace.aligned`
- Truth anchor: `D5/S3/ConceptDynamics/ExperimentBoundary/BoundedRunSpace.bounded`
- Truth anchor: `D5/S3/ConceptDynamics/ExperimentBoundary/BoundedRunSpace.comparison`
- Truth anchor: `D5/S3/ConceptDynamics/ExperimentBoundary/BoundedRunSpace.fairMeasure`
- Truth anchor: `D5/S3/ConceptDynamics/ExperimentBoundary/BoundedRunSpace.language`
- Truth anchor: `D5/S3/ConceptDynamics/ExperimentBoundary/BoundedRunSpace.union`
- Dependency: [D5/S3/ConceptDynamics/Experiment/InfiniteIdentificationFiniteInexactness](../Experiment/InfiniteIdentificationFiniteInexactness.md)
- Dependency: [D5/S3/ConceptDynamics/InformationEscape/RegistrationTemplates](../InformationEscape/RegistrationTemplates.md)
