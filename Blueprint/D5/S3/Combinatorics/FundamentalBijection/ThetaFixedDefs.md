# The Fundamental Bijection and Fixed Avoiders

## Abstract

Standard cycle notation defines the fundamental bijection and its fixed-pattern generating functions.

**Definition 1.1 (A cycle read from a letter).**

Lean statement: `D5/S3/Combinatorics/FundamentalBijection/ThetaFixedDefs.cycleFrom`

*Formalization.* `D5/S3/Combinatorics/FundamentalBijection/ThetaFixedDefs.cycleFrom` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Kassie Archer, Robert P. Laudone (2024). *Pattern avoidance and the fundamental bijection*. DOI: [10.48550/arXiv.2407.06338](https://doi.org/10.48550/arXiv.2407.06338). URL: <https://arxiv.org/abs/2407.06338v1>.

*Commentary.*

Read the cycle of m in the permutation p by starting with m and following the permutation until the first return to m, using at most the length of p further steps.

**Definition 1.2 (The largest letter of a cycle).**

Lean statement: `D5/S3/Combinatorics/FundamentalBijection/ThetaFixedDefs.IsLeader`

*Formalization.* `D5/S3/Combinatorics/FundamentalBijection/ThetaFixedDefs.IsLeader` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Kassie Archer, Robert P. Laudone (2024). *Pattern avoidance and the fundamental bijection*. DOI: [10.48550/arXiv.2407.06338](https://doi.org/10.48550/arXiv.2407.06338). URL: <https://arxiv.org/abs/2407.06338v1>.

*Commentary.*

A letter is a cycle leader when every letter in the cycle read from it is at most that letter.

**Definition 1.3 (Decidability of cycle maxima).**

Lean statement: `D5/S3/Combinatorics/FundamentalBijection/ThetaFixedDefs.instDecidableIsLeader`

*Formalization.* `D5/S3/Combinatorics/FundamentalBijection/ThetaFixedDefs.instDecidableIsLeader` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Kassie Archer, Robert P. Laudone (2024). *Pattern avoidance and the fundamental bijection*. DOI: [10.48550/arXiv.2407.06338](https://doi.org/10.48550/arXiv.2407.06338). URL: <https://arxiv.org/abs/2407.06338v1>.

*Commentary.*

For every finite word and letter, whether that letter is the largest in its cycle is decidable.

**Definition 1.4 (The fundamental bijection).**

Lean statement: `D5/S3/Combinatorics/FundamentalBijection/ThetaFixedDefs.theta`

*Formalization.* `D5/S3/Combinatorics/FundamentalBijection/ThetaFixedDefs.theta` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Kassie Archer, Robert P. Laudone (2024). *Pattern avoidance and the fundamental bijection*. DOI: [10.48550/arXiv.2407.06338](https://doi.org/10.48550/arXiv.2407.06338). URL: <https://arxiv.org/abs/2407.06338v1>.

*Commentary.*

Write each cycle beginning with its largest letter, order the cycles by increasing largest letter, and concatenate their letters.

**Definition 1.5 (Avoiders fixed by an iterate).**

Lean statement: `D5/S3/Combinatorics/FundamentalBijection/ThetaFixedDefs.fixedAvoiders`

*Formalization.* `D5/S3/Combinatorics/FundamentalBijection/ThetaFixedDefs.fixedAvoiders` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Kassie Archer, Robert P. Laudone (2024). *Pattern avoidance and the fundamental bijection*. DOI: [10.48550/arXiv.2407.06338](https://doi.org/10.48550/arXiv.2407.06338). URL: <https://arxiv.org/abs/2407.06338v1>.

*Commentary.*

For a size n, an iteration number k, and a pattern sigma, the fixed avoiders are the permutations of one through n that avoid sigma and are fixed by the k-th iterate of the fundamental bijection.

**Definition 1.6 (The fixed-avoider generating function).**

Lean statement: `D5/S3/Combinatorics/FundamentalBijection/ThetaFixedDefs.gf`

*Formalization.* `D5/S3/Combinatorics/FundamentalBijection/ThetaFixedDefs.gf` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Kassie Archer, Robert P. Laudone (2024). *Pattern avoidance and the fundamental bijection*. DOI: [10.48550/arXiv.2407.06338](https://doi.org/10.48550/arXiv.2407.06338). URL: <https://arxiv.org/abs/2407.06338v1>.

*Commentary.*

The ordinary generating function has integer coefficient at degree n equal to the number of sigma-avoiding permutations of size n fixed by the k-th iterate.

**Definition 1.7 (The proposed third-iterate identity).**

Lean statement: `D5/S3/Combinatorics/FundamentalBijection/ThetaFixedDefs.cubeClaim`

*Formalization.* `D5/S3/Combinatorics/FundamentalBijection/ThetaFixedDefs.cubeClaim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Kassie Archer, Robert P. Laudone (2024). *Pattern avoidance and the fundamental bijection*. DOI: [10.48550/arXiv.2407.06338](https://doi.org/10.48550/arXiv.2407.06338). URL: <https://arxiv.org/abs/2407.06338v1>.

*Commentary.*

For each of the patterns 231 and 312, the generating function for third-iterate fixed avoiders multiplied by 1 - x - x squared - 2x cubed equals one.

**Definition 1.8 (The proposed fourth-iterate identity).**

Lean statement: `D5/S3/Combinatorics/FundamentalBijection/ThetaFixedDefs.fourthClaim`

*Formalization.* `D5/S3/Combinatorics/FundamentalBijection/ThetaFixedDefs.fourthClaim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Kassie Archer, Robert P. Laudone (2024). *Pattern avoidance and the fundamental bijection*. DOI: [10.48550/arXiv.2407.06338](https://doi.org/10.48550/arXiv.2407.06338). URL: <https://arxiv.org/abs/2407.06338v1>.

*Commentary.*

For each of the patterns 231 and 312, the generating function for fourth-iterate fixed avoiders multiplied by 1 - x - x squared - 2x to the fourth - x to the fifth - x to the sixth equals one.

**Definition 1.9 (The proposed fifth-iterate identity).**

Lean statement: `D5/S3/Combinatorics/FundamentalBijection/ThetaFixedDefs.fifthClaim`

*Formalization.* `D5/S3/Combinatorics/FundamentalBijection/ThetaFixedDefs.fifthClaim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Kassie Archer, Robert P. Laudone (2024). *Pattern avoidance and the fundamental bijection*. DOI: [10.48550/arXiv.2407.06338](https://doi.org/10.48550/arXiv.2407.06338). URL: <https://arxiv.org/abs/2407.06338v1>.

*Commentary.*

For each of the patterns 231 and 312, the generating function for fifth-iterate fixed avoiders multiplied by 1 - x - x squared equals one.

## References

- Truth anchor: `D5/S3/Combinatorics/FundamentalBijection/ThetaFixedDefs.IsLeader`
- Truth anchor: `D5/S3/Combinatorics/FundamentalBijection/ThetaFixedDefs.cubeClaim`
- Truth anchor: `D5/S3/Combinatorics/FundamentalBijection/ThetaFixedDefs.cycleFrom`
- Truth anchor: `D5/S3/Combinatorics/FundamentalBijection/ThetaFixedDefs.fifthClaim`
- Truth anchor: `D5/S3/Combinatorics/FundamentalBijection/ThetaFixedDefs.fixedAvoiders`
- Truth anchor: `D5/S3/Combinatorics/FundamentalBijection/ThetaFixedDefs.fourthClaim`
- Truth anchor: `D5/S3/Combinatorics/FundamentalBijection/ThetaFixedDefs.gf`
- Truth anchor: `D5/S3/Combinatorics/FundamentalBijection/ThetaFixedDefs.instDecidableIsLeader`
- Truth anchor: `D5/S3/Combinatorics/FundamentalBijection/ThetaFixedDefs.theta`
- Dependency: [D5/S3/Combinatorics/ArcherCyclicDefs](../ArcherCyclicDefs.md)
