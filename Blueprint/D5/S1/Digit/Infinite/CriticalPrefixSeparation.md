# Sharp separation and critical prefix recovery

## Abstract

Sharp separation and critical prefix recovery.

**Theorem 1.1 (Golden scalar identities).**

Lean statement: `D5/S1/Digit/Infinite/CriticalPrefixSeparation.golden_facts`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/CriticalPrefixSeparation.golden_facts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The reciprocal golden ratio t lies strictly between zero and one, satisfies t^2+t=1, and obeys 1+t^3=2t.

**Theorem 1.2 (Exact sample residual).**

Lean statement: `D5/S1/Digit/Infinite/CriticalPrefixSeparation.residual`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/CriticalPrefixSeparation.residual` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every legal source x and every window index j, the scalar after deleting 3j bits plus t^3 times the scalar after deleting 3(j+1) bits equals the translation of the jth window.

**Theorem 1.3 (Sharp separation and critical prefix recovery).**

Lean statement: `D5/S1/Digit/Infinite/CriticalPrefixSeparation.result`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/CriticalPrefixSeparation.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A source is an infinite Boolean stream with no adjacent occupied bits. One time step deletes three bits. Its first h windows form the target prefix, and the response consists of h+1 real scalar samples from that same source. The reciprocal golden ratio is t, and the signed window contraction is -t^3.

For every h>=1, the sources with one fixed prefix have exactly the closed affine response segment obtained by letting the final scalar range through the legal terminal guard interval. Distinct prefix segments have global minimum distance t/2 in the supremum metric. The empty source and the infinite repetition of five attain it, and both are legal under either incoming guard.

In increasing order the five translations are -t, 0, t^2, 1, and 1+t^2, with successive gaps t, t^2, t, and t^2. Thus distinct window translations differ by at least t^2. Let d_i be the difference of the two sources' samples at time i. At a differing window j the translation difference is d_j+t^3 d_(j+1). Thus the maximum sample difference M satisfies t^2 <= (1+t^3)M = 2tM.

For eventually empty sources each scalar belongs to the embedded golden integer ring. Irrationality excludes t/2 from that ring. The attained maximum coordinate difference therefore cannot equal t/2, and distinct finite-tail prefixes are strictly farther apart. Their distance infimum is nevertheless t/2: for N>h, N repetitions of five followed by the empty tail have coordinate j equal to (t/2)(1-(-t^3)^(N-j)), and converge to the constant t/2 response.

For every nonnegative closed error radius epsilon, a uniformly correct prefix decoder on the actual finite-tail observation domain exists exactly when epsilon <= t/4. Strict source separation makes every compatible prefix unique at that radius. Above it, a sufficiently long finite five run and the empty source admit a common midpoint observation with different prefixes.

Give prefix values the discrete topology. At the constant observation t/4 every correct decoder returns the all-null prefix of length h. The finite five-run responses minus the constant t/4 vector are actual critical observations converging to that same point, while their decoded prefixes are all five. Hence every correct decoder is discontinuous there.

## References

- Truth anchor: `D5/S1/Digit/Infinite/CriticalPrefixSeparation.golden_facts`
- Truth anchor: `D5/S1/Digit/Infinite/CriticalPrefixSeparation.residual`
- Truth anchor: `D5/S1/Digit/Infinite/CriticalPrefixSeparation.result`
- Dependency: [D5/S1/Digit/Infinite/ClosedObservationGraphRealization](ClosedObservationGraphRealization.md)
- Dependency: [D5/S1/Digit/Infinite/FixedTailClosedBudget](FixedTailClosedBudget.md)
- Dependency: [D5/S1/Digit/Infinite/LateLabelStateBound](LateLabelStateBound.md)
- Dependency: [D5/S1/Digit/Infinite/OddColorThreeSource](OddColorThreeSource.md)
- Dependency: [D5/S1/Digit/Infinite/SevenCycleCoherenceRefutation](SevenCycleCoherenceRefutation.md)
