# Disjoint close-pair defects and a strict Lorentz cap

## Abstract

Disjoint close pairs amplify local phase defects into the ordered Lorentz sum. The finite result is stated for a finite collection of copies, so repeated ordinates remain separate rows and the cutoff is inclusive.

**Theorem 1.1 (Finite matching defect inequality).**

Lean statement `D5/S3/Analytic/Oscillation/MontgomeryMatchingCap.finite_matching_defect`.

*Proof.* Machine-checked in Lean. ∎

Let `lorentzKernel d = 4 / (4 + d²)` and `phaseResidual a b = 1 - cos(a-b)`. A matching consists of two maps from a finite pair set to row owners. Each map is injective on the matching and the two images are disjoint. If the pair endpoints are at distance at most one, every column in the first endpoint's inclusive closed radius-one neighborhood is at distance at most two from both endpoints. Both Lorentz weights are therefore at least one half.

For three unit phases on the circle, the squared triangle inequality gives
`phaseResidual(a,c) + phaseResidual(b,c) ≥ phaseResidual(a,b)/2`.
The two endpoint rows consequently contribute at least one quarter of the pair residual per neighborhood copy. Injectivity and cross-disjointness allow these row contributions to be summed without duplication. A row budget bounds the zero-phase Lorentz sum, giving the stated defect cap.

**Theorem 1.2 (Multiplicity and normalized conditional cap).**

Lean statements `D5/S3/Analytic/Oscillation/MontgomeryMatchingCap.spectrum_matching_defect` and `D5/S3/Analytic/Oscillation/MontgomeryMatchingCap.strict_normalized_cap_of_matching`.

The finite sigma type `Σ j, Fin (mult j)` expands every retained multiplicity copy through the inclusive cutoff. Counting its fibers rewrites the finite pair sum exactly as the existing `MontgomeryCountUpper.pairSum`. If at least `c₁ H log H` disjoint pairs have residual at least `c₂`, and each first-endpoint neighborhood has at least `c₃ log H` copies, the matching defect has normalized size at least `c₁ c₂ c₃ / 4`.

The conditional cap theorem takes the row budget and its normalized baseline as hypotheses. The baseline may exceed the target coefficient by the matching margin, which the finite defect removes. The row budget is the local form supplied by the existing Lorentz interval upper-bound machinery. Actual hypotheses that produce these close-pair families for the zeta spectrum remain open.

## References

- Truth anchors `D5/S3/Analytic/Oscillation/MontgomeryMatchingCap.finite_matching_defect` and `D5/S3/Analytic/Oscillation/MontgomeryMatchingCap.strict_normalized_cap_of_matching`.
- Dependency `D5/S3/Analytic/Oscillation/MontgomeryCountUpper`.
- The inclusive multiplicity-copy representation is `D5.S3.Analytic.Oscillation.SmoothedSpectrumCounting.CutDensity.copies`.
