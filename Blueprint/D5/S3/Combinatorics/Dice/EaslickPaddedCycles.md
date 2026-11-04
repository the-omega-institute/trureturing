# EaslickPaddedCycles

## Abstract

Uniform padding supplies simple cycles beyond every face count above six.

**Theorem 1.1 (Every edge of a closed seed).**

$$\forall r \in \mathit{Nat}, k \in \mathit{Nat}, c \in \operatorname{List}\left(\operatorname{List}\left(\mathit{Nat}\right)\right),\; \left(\left(\operatorname{length}\left(c\right) = k \land \operatorname{IsChain}\left(\operatorname{Edge}\left(r\right), \operatorname{append}\left(c, \operatorname{singleton}\left(\operatorname{head}\left(c\right)\right)\right)\right)\right) \land 0 < k\right) \Rightarrow \left(\forall i \in \operatorname{Fin}\left(k\right),\; \operatorname{Edge}\left(r, \operatorname{at}\left(c, i\right), \operatorname{at}\left(c, \left(i + 1\right) \bmod k\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Dice/EaslickPaddedCycles.cycle_edge_at` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Terry Easlick (2026). *Computer-assisted results for n-sided non-transitive dice taking face values in [n]*. URL: <https://arxiv.org/abs/2610.40321v1>.

*Commentary.*

For every r,k and list c of length k, if c followed by its first entry is an Edge(r) chain and k is positive, then every position i below k has an edge to position (i+1) modulo k. The last position therefore returns to the first one.

Every position i in Fin(k) is read through its natural value when indexing a list or forming (i+1) modulo k. The notation head denotes head!, and the closed-chain expression includes the final edge. All lengths, clone indices, products, remainders and inequalities are over natural numbers.

**Theorem 1.2 (Uniform nested padding).**

$$\forall r \in \mathit{Nat}, k \in \mathit{Nat}, t \in \mathit{Nat},\; \left(\left(\left(\left(3 \le r \land 0 < k\right) \land k \bmod 2 = 0\right) \land r + 6 \le r + 2 \cdot t\right) \land \operatorname{HasCycle}\left(r, k\right)\right) \Rightarrow \operatorname{HasCycle}\left(r + 2 \cdot t, k \cdot \left(t + 1\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Dice/EaslickPaddedCycles.padded_cycle` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Terry Easlick (2026). *Computer-assisted results for n-sided non-transitive dice taking face values in [n]*. URL: <https://arxiv.org/abs/2610.40321v1>.

*Commentary.*

For every r at least three, every positive even k, and every t with r+6 at most r+2t, a simple k-cycle for r-face dice gives a simple k(t+1)-cycle for (r+2t)-face dice. Enumerate the clone blocks by j from zero through t and, inside each block, enumerate the seed positions. Adjacent positions have opposite parity, including block transitions and the final closing edge because k is even. The central faces recover the seed position, and the multiplicity of the first low label recovers j, proving that all k(t+1) vertices are distinct.

Every position i in Fin(k) is read through its natural value when indexing a list or forming (i+1) modulo k. The notation head denotes head!, and the closed-chain expression includes the final edge. All lengths, clone indices, products, remainders and inequalities are over natural numbers.

**Theorem 1.3 (All parameters above six).**

$$\forall n \in \mathit{Nat},\; 7 \le n \Rightarrow \left(\exists k \in \mathit{Nat},\; n < k \land \operatorname{HasCycle}\left(n, k\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Dice/EaslickPaddedCycles.longer_cycle` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Terry Easlick (2026). *Computer-assisted results for n-sided non-transitive dice taking face values in [n]*. URL: <https://arxiv.org/abs/2610.40321v1>.

*Commentary.*

For every natural n at least seven, some k greater than n satisfies HasCycle(n,k). The finite cycles cover seven through eleven. For even n at least twelve use the six-face six-cycle and t=(n-6)/2; for odd n at least thirteen use the seven-face fourteen-cycle and t=(n-7)/2. The resulting lengths are 6(t+1) and 14(t+1), respectively, and both strictly exceed n. All vertices are explicit valid dice in the same graph and every edge uses the actual attained unconditional minimum.

Every position i in Fin(k) is read through its natural value when indexing a list or forming (i+1) modulo k. The notation head denotes head!, and the closed-chain expression includes the final edge. All lengths, clone indices, products, remainders and inequalities are over natural numbers.

**Theorem 1.4 (Failure of an exact n bound above six).**

$$\forall n \in \mathit{Nat},\; 7 \le n \Rightarrow \left(\neg \operatorname{S}\left(n\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Dice/EaslickPaddedCycles.not_S_above_six` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Terry Easlick (2026). *Computer-assisted results for n-sided non-transitive dice taking face values in [n]*. URL: <https://arxiv.org/abs/2610.40321v1>.

*Commentary.*

For every natural n at least seven, S(n) is false: the simple longer cycle contradicts its universal upper-bound clause. No assumed existence premise is added to the target.

Every position i in Fin(k) is read through its natural value when indexing a list or forming (i+1) modulo k. The notation head denotes head!, and the closed-chain expression includes the final edge. All lengths, clone indices, products, remainders and inequalities are over natural numbers.

## References

- Truth anchor: `D5/S3/Combinatorics/Dice/EaslickPaddedCycles.cycle_edge_at`
- Truth anchor: `D5/S3/Combinatorics/Dice/EaslickPaddedCycles.longer_cycle`
- Truth anchor: `D5/S3/Combinatorics/Dice/EaslickPaddedCycles.not_S_above_six`
- Truth anchor: `D5/S3/Combinatorics/Dice/EaslickPaddedCycles.padded_cycle`
- Dependency: [D5/S3/Combinatorics/Dice/EaslickCycleSeeds](EaslickCycleSeeds.md)
