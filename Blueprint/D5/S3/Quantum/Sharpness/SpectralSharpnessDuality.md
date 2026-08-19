# Spectral Sharpness as a Bounded-Pairing Maximum

## Abstract

Spectral sharpness is the attained maximum of bounded spectral pairings.

**Theorem 1.1 (Spectral sharpness is the greatest bounded spectral pairing).**

$$\operatorname{IsGreatest}(\left\{C_a(r) \mid \forall i, \lvert a_i \rvert \le 1\right\},\ \operatorname{sharp}(r)).$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Sharpness/SpectralSharpnessDuality.spectral_sharpness_isGreatest_bounded_pairing` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any finite real spectrum r, consider every real observable a whose coordinates have absolute value at most one. The spectral sharpness sharp(r) is a value attained by the spectral pairing capacity C_a(r), and every such bounded pairing is at most sharp(r). Thus sharp(r) is the greatest member of the set of attained bounded-pairing values.

Reindexing the reversed half of the pairing expresses C_a(r) as one half the sum of (r_i - r_{rev i}) a_i. The coordinatewise sign of r_i - r_{rev i} is a plus-or-minus-one witness and turns every term into its absolute value, proving attainment. For an arbitrary bounded a, the triangle inequality and |a_i| <= 1 give the matching upper bound.

This statement closes only the variational-duality and sign-witness subclaim of the source clause. It does not claim the qubit reduction, the zero-sharpness characterization, the saturation criterion, or data-processing monotonicity.

## References

- Truth anchor: `D5/S3/Quantum/Sharpness/SpectralSharpnessDuality.spectral_sharpness_isGreatest_bounded_pairing`
