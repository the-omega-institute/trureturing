# Off-Line Toy Spectrum

## Abstract

Four explicit off-line points retain mirror and polynomial symmetries, while their thirty-first Li coefficient has negative real part.

**Theorem 1.1 (The toy spectrum has four points).**

$$\lvert \operatorname{toySpectrum} \rvert = 4$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/ToySpectrum/OffLineToySpectrum.toy_spectrum_cardinality` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The spectrum consists of the four distinct complex numbers 7/10 + 5i, 7/10 - 5i, 3/10 + 5i, and 3/10 - 5i. This cardinality certificate rules out collapse or vacuity in the subsequent universal statements.

**Theorem 1.2 (Mirror invariance does not force fixed points).**

$$(\forall s \in \operatorname{toySpectrum},\ \operatorname{mirror}(s) \in \operatorname{toySpectrum}) \land (\forall s \in \operatorname{toySpectrum},\ \Re(s) \neq \operatorname{criticalAbscissa})$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/ToySpectrum/OffLineToySpectrum.explicit_off_line_j_invariant_four_point_counterexample` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every point s in the four-point spectrum, the repository's frozen mirror mirror(s) = 1 - conjugate(s) is also in the spectrum. Every one of the four real parts is nevertheless different from the critical abscissa 1/2.

In particular, setwise invariance under the frozen involution does not imply that the set is contained in its fixed locus. No second reflection or involution is introduced.

**Theorem 1.3 (The formal polynomial symmetries hold).**

$$\operatorname{Monic}(\operatorname{toyQuartic}) \land (\forall \rho \in \operatorname{toySpectrum},\ \operatorname{eval}(\operatorname{toyQuartic}, \rho) = 0) \land (\forall s \in \mathbb{C},\ \operatorname{eval}(\operatorname{toyQuartic}, 1 - s) = \operatorname{eval}(\operatorname{toyQuartic}, s)) \land (\forall s \in \mathbb{C},\ \operatorname{eval}(\operatorname{toyQuartic}, \overline{s}) = \overline{\operatorname{eval}(\operatorname{toyQuartic}, s)})$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/ToySpectrum/OffLineToySpectrum.toy_spectrum_satisfies_formal_polynomial_symmetries` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The monic quartic is the product of X minus each of the four displayed points. Every point in the spectrum is a root, and its evaluation obeys F(1 - s) = F(s) and F(conjugate(s)) = conjugate(F(s)) for every complex s.

This is an honest partial formalization of the source's five-property toy-spectrum certificate. The repository provides no D5 definitions for antiunitary covariance or information complementarity, so those two clauses are not encoded or claimed here.

**Theorem 1.4 (The thirty-first Li coefficient is negative).**

$$\Re(\sum_{\rho \in \operatorname{toySpectrum}} (1 - (1 - \frac{1}{\rho})^{31})) < 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/ToySpectrum/OffLineToySpectrum.li_positivity_distinguishes_the_off_line_toy_spectrum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the explicit four-point spectrum, the real part of the finite sum of 1 - (1 - 1/rho)^31 is strictly negative. Lean checks the fixed exponent and all four rational complex terms exactly.

The theorem states only this concrete n = 31 computation. It does not assert a general Li criterion, positivity equivalence, or a claim about every small index.

## References

- Truth anchor: `D5/S3/Zeros/ToySpectrum/OffLineToySpectrum.explicit_off_line_j_invariant_four_point_counterexample`
- Truth anchor: `D5/S3/Zeros/ToySpectrum/OffLineToySpectrum.li_positivity_distinguishes_the_off_line_toy_spectrum`
- Truth anchor: `D5/S3/Zeros/ToySpectrum/OffLineToySpectrum.toy_spectrum_cardinality`
- Truth anchor: `D5/S3/Zeros/ToySpectrum/OffLineToySpectrum.toy_spectrum_satisfies_formal_polynomial_symmetries`
- Dependency: [D5/S3/Zeros/ZeroGeometry](../ZeroGeometry.md)
