# Gap weights for peaks, ties and descents

## Abstract

Two ordered boundary gaps, three single comparisons and the paired comparisons at each old strict peak determine the insertion weight.

**Definition 1.1 (Adjacent comparisons).**

Lean statement: `D5/S3/Combinatorics/Parking/DescentGapKernel.Edge`

*Formalization.* `D5/S3/Combinatorics/Parking/DescentGapKernel.Edge` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Per Alexandersson (2026). *Real-rootedness and interlacing for parking functions and Chow polynomials*. DOI: [10.48550/arXiv.2609.05131](https://doi.org/10.48550/arXiv.2609.05131). URL: <https://arxiv.org/html/2609.05131v2>.

*Commentary.*

An adjacent pair is a strict ascent, a tie or a strict descent.

**Definition 1.2 (Read the comparisons).**

Lean statement: `D5/S3/Combinatorics/Parking/DescentGapKernel.edges`

*Formalization.* `D5/S3/Combinatorics/Parking/DescentGapKernel.edges` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Per Alexandersson (2026). *Real-rootedness and interlacing for parking functions and Chow polynomials*. DOI: [10.48550/arXiv.2609.05131](https://doi.org/10.48550/arXiv.2609.05131). URL: <https://arxiv.org/html/2609.05131v2>.

*Commentary.*

Read one comparison for every consecutive pair in the literal word.

**Definition 1.3 (Strict interior peaks).**

Lean statement: `D5/S3/Combinatorics/Parking/DescentGapKernel.peaks`

*Formalization.* `D5/S3/Combinatorics/Parking/DescentGapKernel.peaks` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Per Alexandersson (2026). *Real-rootedness and interlacing for parking functions and Chow polynomials*. DOI: [10.48550/arXiv.2609.05131](https://doi.org/10.48550/arXiv.2609.05131). URL: <https://arxiv.org/html/2609.05131v2>.

*Commentary.*

For each consecutive triple a, b, c, count the middle letter once when both a < b and c < b.

**Definition 1.4 (Adjacent ties).**

Lean statement: `D5/S3/Combinatorics/Parking/DescentGapKernel.ties`

*Formalization.* `D5/S3/Combinatorics/Parking/DescentGapKernel.ties` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Per Alexandersson (2026). *Real-rootedness and interlacing for parking functions and Chow polynomials*. DOI: [10.48550/arXiv.2609.05131](https://doi.org/10.48550/arXiv.2609.05131). URL: <https://arxiv.org/html/2609.05131v2>.

*Commentary.*

Count equal consecutive pairs using the word and its one-letter tail.

**Definition 1.5 (The literal trivariate weight).**

Lean statement: `D5/S3/Combinatorics/Parking/DescentGapKernel.wordWeight`

*Formalization.* `D5/S3/Combinatorics/Parking/DescentGapKernel.wordWeight` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Per Alexandersson (2026). *Real-rootedness and interlacing for parking functions and Chow polynomials*. DOI: [10.48550/arXiv.2609.05131](https://doi.org/10.48550/arXiv.2609.05131). URL: <https://arxiv.org/html/2609.05131v2>.

*Commentary.*

A word of p strict interior peaks, k adjacent ties and d strict adjacent descents has weight t^p u^k v^d.

**Theorem 1.6 (Weight of the constant one word).**

Lean statement: `D5/S3/Combinatorics/Parking/DescentGapKernel.wordWeight_replicate`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Parking/DescentGapKernel.wordWeight_replicate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Per Alexandersson (2026). *Real-rootedness and interlacing for parking functions and Chow polynomials*. DOI: [10.48550/arXiv.2609.05131](https://doi.org/10.48550/arXiv.2609.05131). URL: <https://arxiv.org/html/2609.05131v2>.

*Commentary.*

The word of n ones has no peaks or descents and exactly n − 1 adjacent ties.

**Definition 1.7 (Prepend a gap size).**

Lean statement: `D5/S3/Combinatorics/Parking/DescentGapKernel.consEmbedding`

*Formalization.* `D5/S3/Combinatorics/Parking/DescentGapKernel.consEmbedding` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Per Alexandersson (2026). *Real-rootedness and interlacing for parking functions and Chow polynomials*. DOI: [10.48550/arXiv.2609.05131](https://doi.org/10.48550/arXiv.2609.05131). URL: <https://arxiv.org/html/2609.05131v2>.

*Commentary.*

An injective map prepends a fixed natural number to a list.

**Definition 1.8 (Profiles of fixed arity and mass).**

Lean statement: `D5/S3/Combinatorics/Parking/DescentGapKernel.profiles`

*Formalization.* `D5/S3/Combinatorics/Parking/DescentGapKernel.profiles` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Per Alexandersson (2026). *Real-rootedness and interlacing for parking functions and Chow polynomials*. DOI: [10.48550/arXiv.2609.05131](https://doi.org/10.48550/arXiv.2609.05131). URL: <https://arxiv.org/html/2609.05131v2>.

*Commentary.*

Enumerate all lists of k gap sizes totaling r by splitting r between the first size and the remaining list.

**Theorem 1.9 (Meaning of profile membership).**

Lean statement: `D5/S3/Combinatorics/Parking/DescentGapKernel.mem_profiles`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Parking/DescentGapKernel.mem_profiles` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Per Alexandersson (2026). *Real-rootedness and interlacing for parking functions and Chow polynomials*. DOI: [10.48550/arXiv.2609.05131](https://doi.org/10.48550/arXiv.2609.05131). URL: <https://arxiv.org/html/2609.05131v2>.

*Commentary.*

A list lies in the finite profile set exactly when its length equals k and its sum equals r.

**Definition 1.10 (Positive boundary run).**

Lean statement: `D5/S3/Combinatorics/Parking/DescentGapKernel.boundarySeries`

*Formalization.* `D5/S3/Combinatorics/Parking/DescentGapKernel.boundarySeries` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Per Alexandersson (2026). *Real-rootedness and interlacing for parking functions and Chow polynomials*. DOI: [10.48550/arXiv.2609.05131](https://doi.org/10.48550/arXiv.2609.05131). URL: <https://arxiv.org/html/2609.05131v2>.

*Commentary.*

A boundary run of j ≥ 1 new maxima contributes u^(j−1) at degree j.

**Definition 1.11 (Occupied internal gap).**

Lean statement: `D5/S3/Combinatorics/Parking/DescentGapKernel.occupiedSeries`

*Formalization.* `D5/S3/Combinatorics/Parking/DescentGapKernel.occupiedSeries` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Per Alexandersson (2026). *Real-rootedness and interlacing for parking functions and Chow polynomials*. DOI: [10.48550/arXiv.2609.05131](https://doi.org/10.48550/arXiv.2609.05131). URL: <https://arxiv.org/html/2609.05131v2>.

*Commentary.*

A single inserted maximum contributes t at degree one. A run of j ≥ 2 new maxima contributes u^(j−1) at degree j.

**Definition 1.12 (Left boundary factor).**

Lean statement: `D5/S3/Combinatorics/Parking/DescentGapKernel.leftSeries`

*Formalization.* `D5/S3/Combinatorics/Parking/DescentGapKernel.leftSeries` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Per Alexandersson (2026). *Real-rootedness and interlacing for parking functions and Chow polynomials*. DOI: [10.48550/arXiv.2609.05131](https://doi.org/10.48550/arXiv.2609.05131). URL: <https://arxiv.org/html/2609.05131v2>.

*Commentary.*

The empty left gap contributes one. A nonempty run has an additional descent into the first old letter.

**Definition 1.13 (Right boundary factor).**

Lean statement: `D5/S3/Combinatorics/Parking/DescentGapKernel.rightSeries`

*Formalization.* `D5/S3/Combinatorics/Parking/DescentGapKernel.rightSeries` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Per Alexandersson (2026). *Real-rootedness and interlacing for parking functions and Chow polynomials*. DOI: [10.48550/arXiv.2609.05131](https://doi.org/10.48550/arXiv.2609.05131). URL: <https://arxiv.org/html/2609.05131v2>.

*Commentary.*

The empty right gap contributes one. A nonempty run contributes its ties and has an ascent from the last old letter.

**Definition 1.14 (Unpaired interior comparison).**

Lean statement: `D5/S3/Combinatorics/Parking/DescentGapKernel.singleSeries`

*Formalization.* `D5/S3/Combinatorics/Parking/DescentGapKernel.singleSeries` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Per Alexandersson (2026). *Real-rootedness and interlacing for parking functions and Chow polynomials*. DOI: [10.48550/arXiv.2609.05131](https://doi.org/10.48550/arXiv.2609.05131). URL: <https://arxiv.org/html/2609.05131v2>.

*Commentary.*

An empty gap keeps its original ascent, descent or tie weight. A nonempty gap contributes the occupied internal gap weight and a descent.

**Definition 1.15 (The paired gaps at an old peak).**

Lean statement: `D5/S3/Combinatorics/Parking/DescentGapKernel.peakSeries`

*Formalization.* `D5/S3/Combinatorics/Parking/DescentGapKernel.peakSeries` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Per Alexandersson (2026). *Real-rootedness and interlacing for parking functions and Chow polynomials*. DOI: [10.48550/arXiv.2609.05131](https://doi.org/10.48550/arXiv.2609.05131). URL: <https://arxiv.org/html/2609.05131v2>.

*Commentary.*

If neither gap is occupied, the old peak and descent contribute tv. With just one gap occupied, the two orientations contribute vS and v²S for the occupied series S. If both are occupied they contribute v²S².

**Definition 1.16 (Series from ordered comparison blocks).**

Lean statement: `D5/S3/Combinatorics/Parking/DescentGapKernel.insertionSeries`

*Formalization.* `D5/S3/Combinatorics/Parking/DescentGapKernel.insertionSeries` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Per Alexandersson (2026). *Real-rootedness and interlacing for parking functions and Chow polynomials*. DOI: [10.48550/arXiv.2609.05131](https://doi.org/10.48550/arXiv.2609.05131). URL: <https://arxiv.org/html/2609.05131v2>.

*Commentary.*

Scan the comparisons and pair each ascent immediately followed by a descent. Multiply their two-gap factors, the remaining comparison factors and the two boundary factors.

**Definition 1.17 (Six-factor kernel).**

Lean statement: `D5/S3/Combinatorics/Parking/DescentGapKernel.closedKernel`

*Formalization.* `D5/S3/Combinatorics/Parking/DescentGapKernel.closedKernel` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Per Alexandersson (2026). *Real-rootedness and interlacing for parking functions and Chow polynomials*. DOI: [10.48550/arXiv.2609.05131](https://doi.org/10.48550/arXiv.2609.05131). URL: <https://arxiv.org/html/2609.05131v2>.

*Commentary.*

For a nonempty word of length ℓ, use one factor per boundary, ℓ − 1 − d − k − p unpaired ascents, d − p unpaired descents, k ties and p old peak blocks.

**Theorem 1.18 (Counting the six types).**

Lean statement: `D5/S3/Combinatorics/Parking/DescentGapKernel.insertionSeries_closed`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Parking/DescentGapKernel.insertionSeries_closed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Per Alexandersson (2026). *Real-rootedness and interlacing for parking functions and Chow polynomials*. DOI: [10.48550/arXiv.2609.05131](https://doi.org/10.48550/arXiv.2609.05131). URL: <https://arxiv.org/html/2609.05131v2>.

*Commentary.*

Each paired block consumes one ascent and one descent. Block counts therefore reduce the ordered product to the six-factor kernel.

**Theorem 1.19 (Local coefficient formula).**

Lean statement: `D5/S3/Combinatorics/Parking/DescentGapKernel.closedKernel_coeff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Parking/DescentGapKernel.closedKernel_coeff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Per Alexandersson (2026). *Real-rootedness and interlacing for parking functions and Chow polynomials*. DOI: [10.48550/arXiv.2609.05131](https://doi.org/10.48550/arXiv.2609.05131). URL: <https://arxiv.org/html/2609.05131v2>.

*Commentary.*

For a nonempty word whose letters are below m, the coefficient of z^r in the six-factor kernel equals the sum of the literal word weights obtained by inserting r copies of m into its ordered gaps.

**Definition 1.20 (The geometric unit).**

Lean statement: `D5/S3/Combinatorics/Parking/DescentGapKernel.geometricDenominator`

*Formalization.* `D5/S3/Combinatorics/Parking/DescentGapKernel.geometricDenominator` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Per Alexandersson (2026). *Real-rootedness and interlacing for parking functions and Chow polynomials*. DOI: [10.48550/arXiv.2609.05131](https://doi.org/10.48550/arXiv.2609.05131). URL: <https://arxiv.org/html/2609.05131v2>.

*Commentary.*

The series 1 − uz is a unit. Rescaling the geometric identity by u gives the inverse with coefficient u^j at degree j.

**Definition 1.21 (Bivariate boundary factor).**

Lean statement: `D5/S3/Combinatorics/Parking/DescentGapKernel.bivarE`

*Formalization.* `D5/S3/Combinatorics/Parking/DescentGapKernel.bivarE` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Per Alexandersson (2026). *Real-rootedness and interlacing for parking functions and Chow polynomials*. DOI: [10.48550/arXiv.2609.05131](https://doi.org/10.48550/arXiv.2609.05131). URL: <https://arxiv.org/html/2609.05131v2>.

*Commentary.*

E is one plus the positive boundary series.

**Definition 1.22 (Bivariate comparison factor).**

Lean statement: `D5/S3/Combinatorics/Parking/DescentGapKernel.bivarA`

*Formalization.* `D5/S3/Combinatorics/Parking/DescentGapKernel.bivarA` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Per Alexandersson (2026). *Real-rootedness and interlacing for parking functions and Chow polynomials*. DOI: [10.48550/arXiv.2609.05131](https://doi.org/10.48550/arXiv.2609.05131). URL: <https://arxiv.org/html/2609.05131v2>.

*Commentary.*

A is one plus the occupied internal gap series.

**Definition 1.23 (Bivariate tie factor).**

Lean statement: `D5/S3/Combinatorics/Parking/DescentGapKernel.bivarC`

*Formalization.* `D5/S3/Combinatorics/Parking/DescentGapKernel.bivarC` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Per Alexandersson (2026). *Real-rootedness and interlacing for parking functions and Chow polynomials*. DOI: [10.48550/arXiv.2609.05131](https://doi.org/10.48550/arXiv.2609.05131). URL: <https://arxiv.org/html/2609.05131v2>.

*Commentary.*

C is u plus the occupied internal gap series.

**Definition 1.24 (Bivariate old-peak factor).**

Lean statement: `D5/S3/Combinatorics/Parking/DescentGapKernel.bivarB`

*Formalization.* `D5/S3/Combinatorics/Parking/DescentGapKernel.bivarB` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Per Alexandersson (2026). *Real-rootedness and interlacing for parking functions and Chow polynomials*. DOI: [10.48550/arXiv.2609.05131](https://doi.org/10.48550/arXiv.2609.05131). URL: <https://arxiv.org/html/2609.05131v2>.

*Commentary.*

B is A² + t − 1.

**Theorem 1.25 (The four series of equation (10)).**

Lean statement: `D5/S3/Combinatorics/Parking/DescentGapKernel.bivariateFactors_eq10`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Parking/DescentGapKernel.bivariateFactors_eq10` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Per Alexandersson (2026). *Real-rootedness and interlacing for parking functions and Chow polynomials*. DOI: [10.48550/arXiv.2609.05131](https://doi.org/10.48550/arXiv.2609.05131). URL: <https://arxiv.org/html/2609.05131v2>.

*Commentary.*

E is 1 + z/(1 − uz), A is 1 + tz + uz²/(1 − uz), C is u + tz + uz²/(1 − uz), and B is A² + t − 1. The geometric denominator is the specified power-series unit.

**Definition 1.26 (The comparison factor as a unit).**

Lean statement: `D5/S3/Combinatorics/Parking/DescentGapKernel.ascentUnit`

*Formalization.* `D5/S3/Combinatorics/Parking/DescentGapKernel.ascentUnit` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Per Alexandersson (2026). *Real-rootedness and interlacing for parking functions and Chow polynomials*. DOI: [10.48550/arXiv.2609.05131](https://doi.org/10.48550/arXiv.2609.05131). URL: <https://arxiv.org/html/2609.05131v2>.

*Commentary.*

A has constant coefficient one and uses the formal inverse determined by that unit coefficient.

**Theorem 1.27 (Equation (11) on each word weight).**

Lean statement: `D5/S3/Combinatorics/Parking/DescentGapKernel.insertionSeries_eq11`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Parking/DescentGapKernel.insertionSeries_eq11` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Per Alexandersson (2026). *Real-rootedness and interlacing for parking functions and Chow polynomials*. DOI: [10.48550/arXiv.2609.05131](https://doi.org/10.48550/arXiv.2609.05131). URL: <https://arxiv.org/html/2609.05131v2>.

*Commentary.*

At v = 1 the boundary factors coincide and the ascent and descent factors both become A. Cancelling the inverse powers of A gives E² A^(ℓ−1) (B/A²)^p (C/A)^k.

## References

- Truth anchor: `D5/S3/Combinatorics/Parking/DescentGapKernel.Edge`
- Truth anchor: `D5/S3/Combinatorics/Parking/DescentGapKernel.ascentUnit`
- Truth anchor: `D5/S3/Combinatorics/Parking/DescentGapKernel.bivarA`
- Truth anchor: `D5/S3/Combinatorics/Parking/DescentGapKernel.bivarB`
- Truth anchor: `D5/S3/Combinatorics/Parking/DescentGapKernel.bivarC`
- Truth anchor: `D5/S3/Combinatorics/Parking/DescentGapKernel.bivarE`
- Truth anchor: `D5/S3/Combinatorics/Parking/DescentGapKernel.bivariateFactors_eq10`
- Truth anchor: `D5/S3/Combinatorics/Parking/DescentGapKernel.boundarySeries`
- Truth anchor: `D5/S3/Combinatorics/Parking/DescentGapKernel.closedKernel`
- Truth anchor: `D5/S3/Combinatorics/Parking/DescentGapKernel.closedKernel_coeff`
- Truth anchor: `D5/S3/Combinatorics/Parking/DescentGapKernel.consEmbedding`
- Truth anchor: `D5/S3/Combinatorics/Parking/DescentGapKernel.edges`
- Truth anchor: `D5/S3/Combinatorics/Parking/DescentGapKernel.geometricDenominator`
- Truth anchor: `D5/S3/Combinatorics/Parking/DescentGapKernel.insertionSeries`
- Truth anchor: `D5/S3/Combinatorics/Parking/DescentGapKernel.insertionSeries_closed`
- Truth anchor: `D5/S3/Combinatorics/Parking/DescentGapKernel.insertionSeries_eq11`
- Truth anchor: `D5/S3/Combinatorics/Parking/DescentGapKernel.leftSeries`
- Truth anchor: `D5/S3/Combinatorics/Parking/DescentGapKernel.mem_profiles`
- Truth anchor: `D5/S3/Combinatorics/Parking/DescentGapKernel.occupiedSeries`
- Truth anchor: `D5/S3/Combinatorics/Parking/DescentGapKernel.peakSeries`
- Truth anchor: `D5/S3/Combinatorics/Parking/DescentGapKernel.peaks`
- Truth anchor: `D5/S3/Combinatorics/Parking/DescentGapKernel.profiles`
- Truth anchor: `D5/S3/Combinatorics/Parking/DescentGapKernel.rightSeries`
- Truth anchor: `D5/S3/Combinatorics/Parking/DescentGapKernel.singleSeries`
- Truth anchor: `D5/S3/Combinatorics/Parking/DescentGapKernel.ties`
- Truth anchor: `D5/S3/Combinatorics/Parking/DescentGapKernel.wordWeight`
- Truth anchor: `D5/S3/Combinatorics/Parking/DescentGapKernel.wordWeight_replicate`
- Dependency: [D5/S1/Words/UnaryGapWords](../../../S1/Words/UnaryGapWords.md)
- Dependency: [D5/S3/Combinatorics/ShankarWords/ActualWordExtremal](../ShankarWords/ActualWordExtremal.md)
