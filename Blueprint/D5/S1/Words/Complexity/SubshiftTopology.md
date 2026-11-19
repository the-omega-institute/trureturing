# Topology and Cardinality of Word Subshifts

## Abstract

Word subshifts are closed orbit closures, and the golden subshift is perfect with cardinality continuum.

For a one-sided word x, let X_x contain the infinite words whose prefixes all occur as factors of x. Product cylinders expose both the topology of X_x and the approximation supplied by the forward shift orbit.

**Theorem 1.1 (Every word subshift is closed).**

$$\operatorname{Closed}(X_x)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/SubshiftTopology.isClosed_wordSubshift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At each prefix length, the admissible words form a finite union of closed FullShift cylinders. Intersecting these closed level conditions over all natural lengths gives exactly X_x.

**Theorem 1.2 (The forward orbit closure equals the word subshift).**

$$\operatorname{cl}(\operatorname{Orb}^+(x)) = X_x$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/SubshiftTopology.closure_shift_orbit_eq_wordSubshift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Closedness and shift invariance place the orbit closure inside X_x. For the reverse inclusion, every prefix admitted by X_x occurs at some starting position of x, so the corresponding shift enters the required PiNat cylinder neighborhood.

**Theorem 1.3 (The golden word subshift is perfect).**

$$\operatorname{Perfect}(X_g)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/SubshiftTopology.golden_wordSubshift_perfect` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Golden recurrence realizes every admitted prefix at arbitrarily late positions, producing orbit points in every cylinder neighborhood.

The exact factor count n+1 rules out equal golden suffixes: equality of two suffixes would make all length-j factors representable by fewer than j+1 starts. Two recurrent occurrences therefore provide a point different from the prescribed center in every neighborhood.

**Theorem 1.4 (The golden word subshift has cardinality continuum).**

$$\operatorname{card}(X_g) = c$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/SubshiftTopology.golden_wordSubshift_cardinal_eq_continuum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Mathlib's perfect-set injection embeds Cantor space into the nonempty golden subshift after equipping Bool sequences with the compatible complete PiNat metric. This gives the continuum lower bound.

The ambient function space from natural numbers to Bool has cardinality continuum, so subtype monotonicity supplies the matching upper bound. Here c denotes the continuum cardinal.

## References

- Truth anchor: `D5/S1/Words/Complexity/SubshiftTopology.closure_shift_orbit_eq_wordSubshift`
- Truth anchor: `D5/S1/Words/Complexity/SubshiftTopology.golden_wordSubshift_cardinal_eq_continuum`
- Truth anchor: `D5/S1/Words/Complexity/SubshiftTopology.golden_wordSubshift_perfect`
- Truth anchor: `D5/S1/Words/Complexity/SubshiftTopology.isClosed_wordSubshift`
- Dependency: [D5/S1/Words/Complexity/SubshiftHausdorffDimension](SubshiftHausdorffDimension.md)
