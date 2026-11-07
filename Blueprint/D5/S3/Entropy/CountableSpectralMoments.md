# Countable spectral moments

## Abstract

Countable probability moments and the exact distinguished-coordinate identity.

For a nonnegative summable real sequence p, write m for its sum, q for the sum of its squares, and r for the sum of its cubes. The elementary symmetric moment e3 is the sum of p_i p_j p_k over i < j < k. There is no additional factorial in this convention. On subprobabilities every required series converges absolutely: squares and cubes are dominated by p, and the nonnegative partial triple sums are bounded by 1/6.

**Theorem 1.1 (Absolute convergence of the unordered triple sum).**

Lean statement: `D5/S3/Entropy/CountableSpectralMoments.absolute_triple_sum`

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/CountableSpectralMoments.absolute_triple_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The indicator of i < j < k is dominated by the summable threefold product of p with itself. Nonnegative product summability and Fubini identify the unordered sum with the finite-layer definition of e3. This argument requires no finite-support restriction and no mass bound.

**Theorem 1.2 (Countable Newton identity).**

Lean statement: `D5/S3/Entropy/CountableSpectralMoments.countable_newton`

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/CountableSpectralMoments.countable_newton` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite increasing-triple recurrence gives 6 e3 = m^3 - 3 m q + 2 r. Taking limits of the summable series proves the same identity on the entire countable domain.

**Theorem 1.3 (Nonnegative elementary symmetric moment).**

Lean statement: `D5/S3/Entropy/CountableSpectralMoments.third_nonneg`

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/CountableSpectralMoments.third_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each increasing-triple summand is nonnegative. This observation supplies the remainder sign in the distinguished-coordinate exclusion.

**Theorem 1.4 (The lower-purity branch).**

Lean statement: `D5/S3/Entropy/CountableSpectralMoments.third_lower_of_purity_le_third`

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/CountableSpectralMoments.third_lower_of_purity_le_third` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For m = 1, summing p_i (p_i - q)^2 >= 0 gives r >= q^2. Newton's identity implies e3 >= (1 - 3q + 2q^2)/6. For 0 <= q <= 1/3 this expression is at least 1/27. The latter constant is not claimed to be the sharp bound at every smaller q.

**Theorem 1.5 (An arbitrary distinguished coordinate).**

Lean statement: `D5/S3/Entropy/CountableSpectralMoments.distinguished_identity`

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/CountableSpectralMoments.distinguished_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Erase the coordinate x by putting zero in its original slot. The tail has mass 1-x, squared mass q-x^2 and cubic mass r-x^3. Applying Newton's identity to both sequences gives exactly e3(p)-1/32 = (2x-1)(4x-1)^2/32 + (x/2)(3/8-q) + e3(tail). The identity requires neither maximality of x nor any purity or sign restriction beyond the probability hypotheses.

**Theorem 1.6 (Conditional exclusion).**

Lean statement: `D5/S3/Entropy/CountableSpectralMoments.third_lower_of_distinguished_ge_half`

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/CountableSpectralMoments.third_lower_of_distinguished_ge_half` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If x >= 1/2 and q <= 3/8, all three terms on the right of the exact identity are nonnegative, so e3 >= 1/32. Any distinguished coordinate meeting the hypothesis suffices; it need not be asserted maximal. This excludes a spectral region and gives no characterization of spectra realizable by a physical channel.

## References

- Truth anchor: `D5/S3/Entropy/CountableSpectralMoments.absolute_triple_sum`
- Truth anchor: `D5/S3/Entropy/CountableSpectralMoments.countable_newton`
- Truth anchor: `D5/S3/Entropy/CountableSpectralMoments.distinguished_identity`
- Truth anchor: `D5/S3/Entropy/CountableSpectralMoments.third_lower_of_distinguished_ge_half`
- Truth anchor: `D5/S3/Entropy/CountableSpectralMoments.third_lower_of_purity_le_third`
- Truth anchor: `D5/S3/Entropy/CountableSpectralMoments.third_nonneg`
