# Finite Label Threshold Evolution

## Abstract

An exponential absolute-distance Schur evolution on any finite labelled matrix algebra is a continuous CPTP scale semigroup with a finite threshold generator.

Take any finite type of logical labels and any real value a(s) on each label. Every original label is retained, including repeated values. At real scale u the matrix entry (s,t) is multiplied by exp(-u abs(a(s)-a(t))/2). The completely positive trace-preserving channels are constructed for u>=0. The entry formula also defines the differentiable extension on the full real line.

**Definition 1.1 (Logical matrix evolution).**

Lean statement: `D5/S3/Quantum/Semigroups/ThresholdSchurSemigroup.evolution`

*Formalization.* `D5/S3/Quantum/Semigroups/ThresholdSchurSemigroup.evolution` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The fixed logical carrier supports all input matrices, not only diagonal states or populations.

**Definition 1.2 (Distinct label image).**

Lean statement: `D5/S3/Quantum/Semigroups/ThresholdSchurSemigroup.labelSet`

*Formalization.* `D5/S3/Quantum/Semigroups/ThresholdSchurSemigroup.labelSet` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The finite image contains each distinct real label value exactly once.

**Definition 1.3 (Ordered distinct image data).**

Lean statement: `D5/S3/Quantum/Semigroups/ThresholdSchurSemigroup.ThresholdData`

*Formalization.* `D5/S3/Quantum/Semigroups/ThresholdSchurSemigroup.ThresholdData` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The data contain a monotonically extended sequence, strictly increasing on its first count+1 entries, and a rank map retaining every original label. Every site belongs to the label image when the carrier is nonempty. The number of cuts is the image cardinality minus one, truncated at zero.

**Definition 1.4 (Increasing image choice).**

Lean statement: `D5/S3/Quantum/Semigroups/ThresholdSchurSemigroup.thresholds`

*Formalization.* `D5/S3/Quantum/Semigroups/ThresholdSchurSemigroup.thresholds` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Choose the proved ordered image data; an empty carrier uses zero cuts.

**Definition 1.5 (Threshold projections).**

Lean statement: `D5/S3/Quantum/Semigroups/ThresholdSchurSemigroup.projection`

*Formalization.* `D5/S3/Quantum/Semigroups/ThresholdSchurSemigroup.projection` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Sort the distinct image of a in increasing order. For each adjacent pair, the projection is diagonal with entry one exactly when the original label value is at or below the lower site. The gap is the next site minus the current site. An all-equal family has no thresholds.

**Definition 1.6 (Adjacent gap).**

Lean statement: `D5/S3/Quantum/Semigroups/ThresholdSchurSemigroup.gap`

*Formalization.* `D5/S3/Quantum/Semigroups/ThresholdSchurSemigroup.gap` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The gap is the upper adjacent image value minus the lower one.

**Definition 1.7 (Finite threshold generator).**

Lean statement: `D5/S3/Quantum/Semigroups/ThresholdSchurSemigroup.generator`

*Formalization.* `D5/S3/Quantum/Semigroups/ThresholdSchurSemigroup.generator` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For each cut, multiply the whole expression P(i) X P(i) - (P(i) X + X P(i))/2 by gap(i), and sum these terms. The generator superoperator matrix is diagonal in the matrix-unit basis indexed by ordered logical-label pairs.

**Definition 1.8 (Generator in matrix-unit coordinates).**

Lean statement: `D5/S3/Quantum/Semigroups/ThresholdSchurSemigroup.generatorMatrix`

*Formalization.* `D5/S3/Quantum/Semigroups/ThresholdSchurSemigroup.generatorMatrix` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The superoperator matrix indexed by pairs of original labels is diagonal, with diagonal value minus half their absolute real-label separation.

**Theorem 1.9 (CPTP semigroup, exact rates and exponential).**

Lean statement: `D5/S3/Quantum/Semigroups/ThresholdSchurSemigroup.result`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/ThresholdSchurSemigroup.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

There is a family of canonical QuantumChannel maps at every nonnegative real scale with exactly the stated action on every logical matrix. The channels compose by adding scales, and the zero-scale bundled linear map is the identity. Every matrix trajectory is continuous. Each gap is nonnegative, and each threshold matrix is self-adjoint and idempotent.

The generator multiplies entry (s,t), and hence matrix unit E(s,t), by -abs(a(s)-a(t))/2. The evolution is the actual matrix exponential of u times this generator in matrix-unit coordinates. Its derivative at every real scale is the generator applied to the evolved matrix. Equal-value blocks have zero rate, zero scale preserves every entry, and a single distinct value gives identity evolution.

For a binary threshold p and q in [0,1], three diagonal Kraus operators are sqrt(q) I, sqrt(1-q) P and sqrt(1-q) (I-P). Their squares sum to the identity. The factor preserves entries on each side of the cut and multiplies separated entries by q. Composing the factors with q=exp(-u gap/2) gives the claimed channel. The sum of exactly the separating adjacent gaps telescopes to the absolute label separation. This same identity evaluates the finite generator sum.

The parameter is scale, not physical time. This fixed logical-algebra construction supplies no encoding of a noninteger Schmidt rank. For the integer-rank tower of ARITHMETIC_HOLOGRAPHIC_RT section 34.3, set a(s)=log(b(s)) and compare at integer differences n-j. An actual flat physical channel correspondence and its optimality are separate requirements; this theorem does not establish the integer physical tower, its endpoint partial traces or the asymptotic optimum.

## References

- Truth anchor: `D5/S3/Quantum/Semigroups/ThresholdSchurSemigroup.ThresholdData`
- Truth anchor: `D5/S3/Quantum/Semigroups/ThresholdSchurSemigroup.evolution`
- Truth anchor: `D5/S3/Quantum/Semigroups/ThresholdSchurSemigroup.gap`
- Truth anchor: `D5/S3/Quantum/Semigroups/ThresholdSchurSemigroup.generator`
- Truth anchor: `D5/S3/Quantum/Semigroups/ThresholdSchurSemigroup.generatorMatrix`
- Truth anchor: `D5/S3/Quantum/Semigroups/ThresholdSchurSemigroup.labelSet`
- Truth anchor: `D5/S3/Quantum/Semigroups/ThresholdSchurSemigroup.projection`
- Truth anchor: `D5/S3/Quantum/Semigroups/ThresholdSchurSemigroup.result`
- Truth anchor: `D5/S3/Quantum/Semigroups/ThresholdSchurSemigroup.thresholds`
- Dependency: [D5/S3/Quantum/Foundation/FiniteKrausChannel](../Foundation/FiniteKrausChannel.md)
