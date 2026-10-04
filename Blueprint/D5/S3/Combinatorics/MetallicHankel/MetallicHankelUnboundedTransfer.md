# Dual-Number Transfer Along the Metallic Cycle

## Abstract

The metallic reversed-denominator recurrence over integer dual numbers has an explicit linear monodromy at each complete cycle.

**Definition 1.1 (The cyclic dual-number coefficients).**

Lean statement: `D5/S3/Combinatorics/MetallicHankel/MetallicHankelUnboundedTransfer.jetWord`

*Formalization.* `D5/S3/Combinatorics/MetallicHankel/MetallicHankelUnboundedTransfer.jetWord` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Guo-Niu Han, Emmanuel Pedon (2025). *Hankel continued fractions and Hankel determinants for q-deformed metallic numbers*. DOI: [10.48550/arXiv.2502.05993](https://doi.org/10.48550/arXiv.2502.05993). URL: <https://arxiv.org/abs/2502.05993v2>.

*Commentary.*

Work in the integer dual numbers, written a + b epsilon with epsilon squared equal to zero. For n equal to one, the coefficient word is [(1+epsilon,-1), (1+epsilon,1), (-1+epsilon,-1)]. For every other nonnegative integer n, take the metallic cycle in its given order. At each state with fraction data (k,v,D), the corresponding pair is ([q^{k+1}]D + [q^k]D epsilon, v). Thus the word retains the denominator coefficients at degrees k+1 and k together with the sign of each fraction term.

**Definition 1.2 (One reversed-denominator step).**

Lean statement: `D5/S3/Combinatorics/MetallicHankel/MetallicHankelUnboundedTransfer.jetStep`

*Formalization.* `D5/S3/Combinatorics/MetallicHankel/MetallicHankelUnboundedTransfer.jetStep` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Guo-Niu Han, Emmanuel Pedon (2025). *Hankel continued fractions and Hankel determinants for q-deformed metallic numbers*. DOI: [10.48550/arXiv.2502.05993](https://doi.org/10.48550/arXiv.2502.05993). URL: <https://arxiv.org/abs/2502.05993v2>.

*Commentary.*

For a state (z_1,z_2) of two integer dual numbers and a coefficient pair (a,v) consisting of a dual number and an integer, the next state is (a z_1 - v z_2, z_1). Integers act as dual numbers with zero epsilon coefficient.

**Theorem 1.3 (The state after complete cycles).**

Lean statement: `D5/S3/Combinatorics/MetallicHankel/MetallicHankelUnboundedTransfer.cycle_transfer`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/MetallicHankel/MetallicHankelUnboundedTransfer.cycle_transfer` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Guo-Niu Han, Emmanuel Pedon (2025). *Hankel continued fractions and Hankel determinants for q-deformed metallic numbers*. DOI: [10.48550/arXiv.2502.05993](https://doi.org/10.48550/arXiv.2502.05993). URL: <https://arxiv.org/abs/2502.05993v2>.

*Commentary.*

Let n be a positive integer, let W be its cyclic dual-number coefficient word, and let a sequence of states start at (1,0) and follow the step (z_1,z_2) to (a z_1 - v z_2,z_1), using the coefficient W at the current index modulo its length. Put lambda = 1 for n = 1 and lambda = 2n+1 otherwise. After k complete cycles, for every nonnegative integer k, the state is (1 - k lambda epsilon, 2k lambda epsilon). This includes the separate three-term golden word and the metallic words for every n at least two.

## References

- Truth anchor: `D5/S3/Combinatorics/MetallicHankel/MetallicHankelUnboundedTransfer.cycle_transfer`
- Truth anchor: `D5/S3/Combinatorics/MetallicHankel/MetallicHankelUnboundedTransfer.jetStep`
- Truth anchor: `D5/S3/Combinatorics/MetallicHankel/MetallicHankelUnboundedTransfer.jetWord`
- Dependency: [D5/S3/Combinatorics/MetallicHankel/MetallicHankelData](MetallicHankelData.md)
