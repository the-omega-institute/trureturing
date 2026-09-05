# Prime-Power Diffraction Atom

## Abstract

The explicit-formula summand at a positive prime power has its exact logarithmic location and midline weight.

**Theorem 1.1 (A prime-power summand has the canonical location and weight).**

$$\forall g, p, m \in \mathbb{N}, \operatorname{Prime}(p) \land m \neq 0 \Rightarrow\\\operatorname{log}(p^{m}) = m \cdot \operatorname{log}(p) \land\\\Lambda(p^{m}) \cdot {p^{m}}^{-1/2} = \operatorname{log}(p) \cdot p^{-m/2} \land\\\operatorname{primeSummand}\left(g, p^{m}\right) = \operatorname{log}(p) \cdot p^{-m/2} \cdot (g(m \cdot \operatorname{log}(p)) + g(-(m \cdot \operatorname{log}(p)))).$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/PrimeAddress/PrimePowerDiffractionAtom.prime_power_diffraction_atom` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a prime p and a nonzero natural exponent m, the sampled address log(p^m) is m log p. The von Mangoldt coefficient and real-power factor jointly reduce to log p times p^(-m/2).

Substituting both identities into the repository's primeSummand gives the full normalized explicit-formula atom, including its two symmetric test-function evaluations.

Pinned Mathlib supplies vonMangoldt_apply_pow, vonMangoldt_apply_prime, log_pow, rpow_mul, and rpow_natCast. The theorem does not assert an RH equivalence or a quasicrystal interpretation, for which the source provides no formal carrier.

## References

- Truth anchor: `D5/S3/Weil/PrimeAddress/PrimePowerDiffractionAtom.prime_power_diffraction_atom`
