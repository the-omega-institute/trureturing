# Conditional Parry words and collisions

## Abstract

Conditional Parry word masses and overlapping collisions.

**Theorem 1.1 (Conditional word mass).**

Lean statement: `D5/S3/TotalVariation/ParryWordCollision.parry_word_mass`

*Proof.* Machine-checked in Lean as `D5/S3/TotalVariation/ParryWordCollision.parry_word_mass` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every k >= 2, put p = parryParameter k and h = suffixWeight k p. Starting at any signed suffix state, the mass of every supported path of n transitions is p^n times h at its endpoint divided by h at its start. The transition factors telescope. A relation bit and a signed state determine at most one supported next state, so any specified relation word has at most one supported state path. Consequently, for every m >= 1 its conditional mass is at most p^(m-1), including mass zero for inadmissible words. The estimate uses the actual Parry inequalities p <= h_j <= 1.

**Theorem 1.2 (Overlapping complete words).**

Lean statement: `D5/S3/TotalVariation/ParryWordCollision.parry_overlapping_collision`

*Proof.* Machine-checked in Lean as `D5/S3/TotalVariation/ParryWordCollision.parry_overlapping_collision` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For k >= 2 and m >= 1, take two starts a < b with b+m <= n in a complete n-transition prefix under the signed stationary Parry law. The probability that their length-m relation words agree is at most p^(m-1). After the prefix before b is fixed, equality determines every bit of the second word: a required bit either lies in that prefix or is an earlier already determined bit of the second word. This induction includes overlap. Summing the unused suffix uses the stochastic kernel row sums; averaging over the prefix uses the actual normalized Parry law. The two occurrences need not be independent.

## References

- Truth anchor: `D5/S3/TotalVariation/ParryWordCollision.parry_overlapping_collision`
- Truth anchor: `D5/S3/TotalVariation/ParryWordCollision.parry_word_mass`
- Dependency: [D5/S3/TotalVariation/ParryResetLaw](ParryResetLaw.md)
- Dependency: [D5/S3/TotalVariation/TwistedPrefixComparison](TwistedPrefixComparison.md)
