# Splitting at the Final Value

## Abstract

A final value splits a 132-avoider into larger and smaller letters and gives an appended-letter criterion.

**Theorem 1.1 (The cut determined by the final value).**

Lean statement: `D5/S3/Combinatorics/FundamentalBijection/ThetaIterateScan.final_value_cut`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/FundamentalBijection/ThetaIterateScan.final_value_cut` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kassie Archer, Robert P. Laudone (2024). *Pattern avoidance and the fundamental bijection*. DOI: [10.48550/arXiv.2407.06338](https://doi.org/10.48550/arXiv.2407.06338). URL: <https://arxiv.org/abs/2407.06338v1>.

*Commentary.*

A 132-avoiding permutation of size n ending with v greater than one has a cut at n minus v: all entries before the cut exceed v, all entries from the cut up to but excluding the final position are below v, the prefix permutes v plus one through n, and the intervening suffix permutes one through v minus one.

**Theorem 1.2 (Avoidance after appending a letter).**

Lean statement: `D5/S3/Combinatorics/FundamentalBijection/ThetaIterateScan.avoids132_append_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/FundamentalBijection/ThetaIterateScan.avoids132_append_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kassie Archer, Robert P. Laudone (2024). *Pattern avoidance and the fundamental bijection*. DOI: [10.48550/arXiv.2407.06338](https://doi.org/10.48550/arXiv.2407.06338). URL: <https://arxiv.org/abs/2407.06338v1>.

*Commentary.*

A word followed by v avoids 132 exactly when the word avoids 132 and no increasing positional pair in the word has its first value below v and its second value above v.

**Theorem 1.3 (Avoidance with an initial maximum).**

Lean statement: `D5/S3/Combinatorics/FundamentalBijection/ThetaIterateScan.avoids132_cons_max_append_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/FundamentalBijection/ThetaIterateScan.avoids132_cons_max_append_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kassie Archer, Robert P. Laudone (2024). *Pattern avoidance and the fundamental bijection*. DOI: [10.48550/arXiv.2407.06338](https://doi.org/10.48550/arXiv.2407.06338). URL: <https://arxiv.org/abs/2407.06338v1>.

*Commentary.*

If top exceeds every entry of a word followed by v, placing top before that word does not alter the criterion: avoidance of 132 is equivalent to avoidance in the word and the absence of an increasing positional pair whose values straddle v.

## References

- Truth anchor: `D5/S3/Combinatorics/FundamentalBijection/ThetaIterateScan.avoids132_append_iff`
- Truth anchor: `D5/S3/Combinatorics/FundamentalBijection/ThetaIterateScan.avoids132_cons_max_append_iff`
- Truth anchor: `D5/S3/Combinatorics/FundamentalBijection/ThetaIterateScan.final_value_cut`
- Dependency: [D5/S3/Combinatorics/FundamentalBijection/ThetaBasicInverseBlocks](ThetaBasicInverseBlocks.md)
- Dependency: [D5/S3/Combinatorics/FundamentalBijection/ThetaBasicInverseGeneral](ThetaBasicInverseGeneral.md)
- Dependency: [D5/S3/Combinatorics/FundamentalBijection/ThetaIteratePositionBlocks](ThetaIteratePositionBlocks.md)
