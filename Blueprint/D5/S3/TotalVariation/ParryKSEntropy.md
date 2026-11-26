# The Parry law attains the entropy bound

## Abstract

Metric entropy of the actual bilateral forbidden-run shift.

**Theorem 1.1 (Maximum Kolmogorov–Sinai entropy of the bilateral Parry shift).**

Lean statement: `D5/S3/TotalVariation/ParryKSEntropy.bilateral_parry_entropy`

*Proof.* Machine-checked in Lean as `D5/S3/TotalVariation/ParryKSEntropy.bilateral_parry_entropy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every k at least two, there exist a bilateral coding and a shift-invariant probability on the unsigned relation space with the stationary Parry suffix cylinders at every integer origin. Its full Kolmogorov–Sinai entropy is minus log p, with p the reciprocal Parry root. Every probability preserved by the same shift has Kolmogorov–Sinai entropy at most minus log p.

On each realized suffix word, the logarithm of its reference mass is the number of transitions times log p, plus terms from the first and last suffix. Those terms are uniformly bounded because the suffix alphabet is finite. Gibbs' inequality bounds any competitor's block entropy by its cross entropy against that reference. Taking the block length to infinity removes the endpoint terms. The reference law attains the bound by the corresponding lower estimate on its own block entropy.

Reading the suffix at successively earlier origins gives increasing forward-generated sigma algebras. Their supremum contains every Boolean coordinate because the next suffix is zero exactly at a false bit. Stationarity gives these shifted suffix partitions equal entropy rates, so their common rate is the full Kolmogorov–Sinai entropy.

## References

- Truth anchor: `D5/S3/TotalVariation/ParryKSEntropy.bilateral_parry_entropy`
- Dependency: [D5/S3/Divergence/GrandmotherTheorem](../Divergence/GrandmotherTheorem.md)
- Dependency: [D5/S3/Entropy/KolmogorovSinai/Generator](../Entropy/KolmogorovSinai/Generator.md)
- Dependency: [D5/S3/TotalVariation/ParryInducedEntropy](ParryInducedEntropy.md)
