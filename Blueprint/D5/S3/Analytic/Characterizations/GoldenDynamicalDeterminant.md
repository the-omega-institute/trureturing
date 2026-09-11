# Golden Dynamical Determinant

## Abstract

The golden rational continuation has two simple poles, the exact trace-series convergence radius, and the Perron rate of independently defined forbidden-11 words.

The source is Part1739 of OBSERVER_ADELIC_COMPLETION_CONSTANT_THEORY. The local trace logarithm identifies the positive exponential with the rational continuation on its disk. The continuation and independently recursive forbidden-11 words determine the poles, Perron rate, and parity.

**Definition 1.1 (Independently grounded words).**

Lean statement: `D5/S3/Analytic/Characterizations/GoldenDynamicalDeterminant.wordCount`

*Formalization.* `D5/S3/Analytic/Characterizations/GoldenDynamicalDeterminant.wordCount` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The count is the cardinality of the recursive Adm subtype. Admissibility is equivalent to no two adjacent letters being both true, including the empty and one-letter cases. These free word counts differ from the traces, which count marked closed walks.

**Definition 1.2 (Continuation and Perron contract).**

Lean statement: `D5/S3/Analytic/Characterizations/GoldenDynamicalDeterminant.continuationContract`

*Formalization.* `D5/S3/Analytic/Characterizations/GoldenDynamicalDeterminant.continuationContract` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The continuation is analytic off the roots and meromorphic everywhere, with order minus one at both roots and no other poles. The positive pole is the unique nearest pole. A harmonic term plus an absolutely summable correction gives boundary divergence and the greatest centered disk of absolute summability. The spectrum consists of the golden ratio and its negative reciprocal. The golden ratio is the spectral radius and has a positive Perron eigenvector.

**Definition 1.3 (Integrality, growth, and parity contract).**

Lean statement: `D5/S3/Analytic/Characterizations/GoldenDynamicalDeterminant.wordContract`

*Formalization.* `D5/S3/Analytic/Characterizations/GoldenDynamicalDeterminant.wordContract` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every length the true finite cardinality is the Fibonacci number at length plus two. The actual nth-root limit is the irrational golden ratio. The radical scalar definitions, reciprocal conjugate relation, and alternating conjugate powers are exact. The Binet word correction has a minus sign and exponent length plus two; it is negative at even lengths and positive at odd lengths.

**Theorem 1.4 (Golden continuation and poles).**

Lean statement: `D5/S3/Analytic/Characterizations/GoldenDynamicalDeterminant.golden_continuation`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Characterizations/GoldenDynamicalDeterminant.golden_continuation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Factor orders prove genuine simple poles at the reciprocal golden ratio and at minus the golden ratio. The negative eigenvalue is minus the reciprocal golden ratio, not the negative pole coordinate. The positive pole is nearest to zero. The harmonic boundary obstruction proves the exact centered convergence radius without claiming divergence at every other boundary point.

**Theorem 1.5 (Golden word growth and parity).**

Lean statement: `D5/S3/Analytic/Characterizations/GoldenDynamicalDeterminant.golden_words`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Characterizations/GoldenDynamicalDeterminant.golden_words` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Induction relates the recursive word carrier to all adjacent transitions. The cardinality and Binet formula give a positive normalized limit; continuity of real powers then gives the nth-root growth. Integrality holds at each finite length while the irrational rate is an asymptotic invariant.

**Theorem 1.6 (Complete mathematical specialization).**

Lean statement: `D5/S3/Analytic/Characterizations/GoldenDynamicalDeterminant.golden_dynamical_determinant`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Characterizations/GoldenDynamicalDeterminant.golden_dynamical_determinant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The local infinite trace sum is the negative principal logarithm of the determinant, and its positive exponential agrees with the rational continuation on the open disk. The continuation has two simple poles. The golden ratio is both the Perron rate and the irrational nth-root word-growth limit; its reciprocal is the positive principal pole coordinate. Every finite word count is an integer, and the negative conjugate eigenvalue gives the alternating correction in the Binet formula.

## References

- Truth anchor: `D5/S3/Analytic/Characterizations/GoldenDynamicalDeterminant.continuationContract`
- Truth anchor: `D5/S3/Analytic/Characterizations/GoldenDynamicalDeterminant.golden_continuation`
- Truth anchor: `D5/S3/Analytic/Characterizations/GoldenDynamicalDeterminant.golden_dynamical_determinant`
- Truth anchor: `D5/S3/Analytic/Characterizations/GoldenDynamicalDeterminant.golden_words`
- Truth anchor: `D5/S3/Analytic/Characterizations/GoldenDynamicalDeterminant.wordContract`
- Truth anchor: `D5/S3/Analytic/Characterizations/GoldenDynamicalDeterminant.wordCount`
- Dependency: [D5/S1/Words/AdmissibleWords/AdmissibleCount](../../../S1/Words/AdmissibleWords/AdmissibleCount.md)
- Dependency: [D5/S3/Analytic/Characterizations/GoldenTraceLog](GoldenTraceLog.md)
