# Gronwall Envelopes

## Abstract

Powers of primorials attain the sharp lower Gronwall envelope.

**Theorem 1.1 (Arbitrarily Large Near-Maximal Divisor Sums).**

Lean statement: `D5/S3/Weil/GronwallLowerEnvelope.gronwall_lower_envelope`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/GronwallLowerEnvelope.gronwall_lower_envelope` (`✓ std3`). ∎

*Citation.* T. H. Gronwall (1913). *Some asymptotic expressions in the theory of numbers*. DOI: [10.1090/s0002-9947-1913-1500940-6](https://doi.org/10.1090/s0002-9947-1913-1500940-6).

*Commentary.*

For every positive epsilon and every natural threshold, a power of a primorial reaches the normalized level one minus epsilon above that threshold. A geometric factor controls the reciprocal prime-power error uniformly. The denominator uses the Chebyshev upper bound, and the leading constant comes from Mertens' third theorem.

**Theorem 1.2 (The Two Sharp Envelopes).**

Lean statement: `D5/S3/Weil/GronwallLowerEnvelope.gronwall_envelopes`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/GronwallLowerEnvelope.gronwall_envelopes` (`✓ std3`). ∎

*Citation.* T. H. Gronwall (1913). *Some asymptotic expressions in the theory of numbers*. DOI: [10.1090/s0002-9947-1913-1500940-6](https://doi.org/10.1090/s0002-9947-1913-1500940-6).

*Commentary.*

The existing eventual upper envelope and the arbitrarily large lower witnesses are packaged with the same positive epsilon. These are the two epsilon conditions for the normalized Gronwall limsup to equal one.

## References

- Truth anchor: `D5/S3/Weil/GronwallLowerEnvelope.gronwall_envelopes`
- Truth anchor: `D5/S3/Weil/GronwallLowerEnvelope.gronwall_lower_envelope`
