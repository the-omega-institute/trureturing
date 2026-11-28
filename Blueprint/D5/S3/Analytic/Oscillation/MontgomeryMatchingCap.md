# Disjoint close-pair defects and a strict Lorentz cap

## Abstract

Disjoint close-pair defects amplify into a strict Lorentz cap under a zero-phase bound.

**Theorem 1.1 (Finite matching defect inequality).**

Lean statement: `D5/S3/Analytic/Oscillation/MontgomeryMatchingCap.finite_matching_defect`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Oscillation/MontgomeryMatchingCap.finite_matching_defect` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Take any finite set of copies with real ordinates γ(u). Repeated ordinates are allowed. Let M be a matching of ordered pairs (u,v) of these copies, with all endpoints distinct and |γ(u)−γ(v)| ≤ 1 for every pair. Let C(u) count all copies whose ordinate is within distance one of γ(u), including the boundary.

For real t, let G(t) be the sum of K(γ(i)−γ(j)) cos(t(γ(i)−γ(j))) over all ordered pairs (i,j) of copies, where K(d) = 4/(4+d²). Then

$$
\frac{4}{13}\sum_{(u,v)\in M}\operatorname{C}\left(u\right)[1-\operatorname{cos}(t(\gamma(u)-\gamma(v)))]\leq\operatorname{G}\left(0\right)-\operatorname{G}\left(t\right)
$$

For each column in the first endpoint's neighborhood, the two Lorentz weights are at least four fifths and one half, respectively. The square of the sum of the chord lengths from the two endpoint phases to the column phase is at most thirteen fourths of their weighted squared sum. The triangle inequality and the squared chord identity give the stated lower bound per column. Disjoint endpoints let us sum distinct rows. All omitted terms are nonnegative.

**Theorem 1.2 (Defect for a spectrum with multiplicities).**

Lean statement: `D5/S3/Analytic/Oscillation/MontgomeryMatchingCap.spectrum_matching_defect`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Oscillation/MontgomeryMatchingCap.spectrum_matching_defect` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a spectrum truncated at a real height H, retain each ordinate at or below H with its full multiplicity. Use the same oriented matching of distinct retained endpoints at distance at most one, and count neighborhoods among the retained copies. For this cutoff, G(t) is the ordered Montgomery sum, with each ordinate pair weighted by the product of its multiplicities. At every real t the deficit satisfies

$$
\frac{4}{13}\sum_{(u,v)\in M}\operatorname{C}\left(u\right)[1-\operatorname{cos}(t(\gamma(u)-\gamma(v)))]\leq\operatorname{G}\left(0\right)-\operatorname{G}\left(t\right)
$$

Expanding every multiplicity into distinct copies identifies both Montgomery sums with the corresponding finite sums at zero and at t.

**Theorem 1.3 (Conditional normalized cap).**

Lean statement: `D5/S3/Analytic/Oscillation/MontgomeryMatchingCap.strict_normalized_cap_of_matching`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Oscillation/MontgomeryMatchingCap.strict_normalized_cap_of_matching` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Suppose H > 1, c₂ ≥ 0 and c₃ ≥ 0. At the tested frequency t the same matching has at least c₁ H log H pairs. Each pair has phase residual at least c₂, and its first endpoint's closed neighborhood contains at least c₃ log H copies.

Divide both ordered sums by H(log H)². If the normalized zero-frequency sum is at most κ − η + 4c₁c₂c₃/13, the normalized sum at t is at most κ − η. A positive η gives a strict bound below κ. Obtaining sufficiently many such close pairs with a uniform phase residual for actual zeta zeros across a long frequency band remains open.

## References

- Truth anchor: `D5/S3/Analytic/Oscillation/MontgomeryMatchingCap.finite_matching_defect`
- Truth anchor: `D5/S3/Analytic/Oscillation/MontgomeryMatchingCap.spectrum_matching_defect`
- Truth anchor: `D5/S3/Analytic/Oscillation/MontgomeryMatchingCap.strict_normalized_cap_of_matching`
- Dependency: [D5/S3/Analytic/Oscillation/MontgomeryAutocorrelationLimit](MontgomeryAutocorrelationLimit.md)
- Dependency: [D5/S3/Analytic/Oscillation/MontgomeryCountUpper](MontgomeryCountUpper.md)
- Dependency: [D5/S3/Analytic/Oscillation/SmoothedSpectrumCounting](SmoothedSpectrumCounting.md)
