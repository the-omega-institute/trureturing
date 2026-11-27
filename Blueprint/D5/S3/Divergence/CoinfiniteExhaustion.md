# Exhaustion dependence for bit erasure

## Abstract

Compatible nested finite restrictions of one faithful diagonal bit-erasure model have different entropy-loss limits.

The physical first coordinate is k = i + 1 for i a natural number. Its two fixed laws have masses p(k) = 1/(k(k+1)) and q(k) = 2⁻ᵏ. Both use the same independent fair bit. A cutoff m keeps the first m singletons and merges the remaining coordinates into an atom with respective masses 1/(m+1) and 2⁻ᵐ.

**Theorem 1.1 (Fixed faithful countable laws).**

Lean statement: `D5/S3/Divergence/CoinfiniteExhaustion.fixed_source_states`

*Proof.* Machine-checked in Lean as `D5/S3/Divergence/CoinfiniteExhaustion.fixed_source_states` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Tai-Hsuan Yang (2026). *Quantum data processing equality*. DOI: [10.48550/arXiv.2609.33815](https://doi.org/10.48550/arXiv.2609.33815). URL: <https://arxiv.org/abs/2609.33815v2>.

*Commentary.*

Both source laws on the product with the bit are strictly positive and sum to one.

**Theorem 1.2 (Restriction of the fixed laws).**

Lean statement: `D5/S3/Divergence/CoinfiniteExhaustion.fine_states_are_restrictions`

*Proof.* Machine-checked in Lean as `D5/S3/Divergence/CoinfiniteExhaustion.fine_states_are_restrictions` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Tai-Hsuan Yang (2026). *Quantum data processing equality*. DOI: [10.48550/arXiv.2609.33815](https://doi.org/10.48550/arXiv.2609.33815). URL: <https://arxiv.org/abs/2609.33815v2>.

*Commentary.*

Summing each source law over the fiber of the finite cutoff, with the bit retained, gives its corresponding fine input mass.

**Theorem 1.3 (Faithful finite laws).**

Lean statement: `D5/S3/Divergence/CoinfiniteExhaustion.finite_states`

*Proof.* Machine-checked in Lean as `D5/S3/Divergence/CoinfiniteExhaustion.finite_states` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Tai-Hsuan Yang (2026). *Quantum data processing equality*. DOI: [10.48550/arXiv.2609.33815](https://doi.org/10.48550/arXiv.2609.33815). URL: <https://arxiv.org/abs/2609.33815v2>.

*Commentary.*

At each cutoff the two marginal laws and their two fair-bit lifts are strictly positive and have sum one.

**Theorem 1.4 (Compatibility of the cutoffs).**

Lean statement: `D5/S3/Divergence/CoinfiniteExhaustion.partitionMap_cutIndex`

*Proof.* Machine-checked in Lean as `D5/S3/Divergence/CoinfiniteExhaustion.partitionMap_cutIndex` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Tai-Hsuan Yang (2026). *Quantum data processing equality*. DOI: [10.48550/arXiv.2609.33815](https://doi.org/10.48550/arXiv.2609.33815). URL: <https://arxiv.org/abs/2609.33815v2>.

*Commentary.*

For n ≤ a the coarse atom of a physical coordinate equals the coarse image of its fine atom.

**Theorem 1.5 (Nested clipping).**

Lean statement: `D5/S3/Divergence/CoinfiniteExhaustion.partitionMap_comp`

*Proof.* Machine-checked in Lean as `D5/S3/Divergence/CoinfiniteExhaustion.partitionMap_comp` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Tai-Hsuan Yang (2026). *Quantum data processing equality*. DOI: [10.48550/arXiv.2609.33815](https://doi.org/10.48550/arXiv.2609.33815). URL: <https://arxiv.org/abs/2609.33815v2>.

*Commentary.*

If n ≤ m, clipping a fine atom first at m and then at n gives its direct image at n.

**Theorem 1.6 (Eventual resolution of each physical atom).**

Lean statement: `D5/S3/Divergence/CoinfiniteExhaustion.eventually_resolves_atom`

*Proof.* Machine-checked in Lean as `D5/S3/Divergence/CoinfiniteExhaustion.eventually_resolves_atom` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Tai-Hsuan Yang (2026). *Quantum data processing equality*. DOI: [10.48550/arXiv.2609.33815](https://doi.org/10.48550/arXiv.2609.33815). URL: <https://arxiv.org/abs/2609.33815v2>.

*Commentary.*

For every compatible sequence a with n ≤ a(n), every fixed first coordinate eventually lies in a singleton atom.

**Theorem 1.7 (The finite bit-erasure channel).**

Lean statement: `D5/S3/Divergence/CoinfiniteExhaustion.partitionChannel_stochastic`

*Proof.* Machine-checked in Lean as `D5/S3/Divergence/CoinfiniteExhaustion.partitionChannel_stochastic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Tai-Hsuan Yang (2026). *Quantum data processing equality*. DOI: [10.48550/arXiv.2609.33815](https://doi.org/10.48550/arXiv.2609.33815). URL: <https://arxiv.org/abs/2609.33815v2>.

*Commentary.*

The finite stochastic matrix sends each fine atom and bit pair to its coarse atom with probability one. All entries are nonnegative and each input row sums to one.

**Theorem 1.8 (The two actual channel outputs).**

Lean statement: `D5/S3/Divergence/CoinfiniteExhaustion.partitionChannel_outputs`

*Proof.* Machine-checked in Lean as `D5/S3/Divergence/CoinfiniteExhaustion.partitionChannel_outputs` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Tai-Hsuan Yang (2026). *Quantum data processing equality*. DOI: [10.48550/arXiv.2609.33815](https://doi.org/10.48550/arXiv.2609.33815). URL: <https://arxiv.org/abs/2609.33815v2>.

*Commentary.*

For n ≤ a the actual outputs of the fine restrictions are the respective coarse cutoff laws.

**Theorem 1.9 (Exact finite KL loss).**

$$\forall a \in \mathbb{N},\; \forall n \in \mathbb{N},\; n \le a \Rightarrow \operatorname{loss}\left(a, n\right) = \operatorname{log}\left(2\right) \cdot \left(\operatorname{harmonic}\left(a\right) - \operatorname{harmonic}\left(n\right)\right) - \left(\operatorname{shannonEntropy}\left(\operatorname{pCut}\left(a\right)\right) - \operatorname{shannonEntropy}\left(\operatorname{pCut}\left(n\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Divergence/CoinfiniteExhaustion.loss_exact` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Tai-Hsuan Yang (2026). *Quantum data processing equality*. DOI: [10.48550/arXiv.2609.33815](https://doi.org/10.48550/arXiv.2609.33815). URL: <https://arxiv.org/abs/2609.33815v2>.

*Commentary.*

The common fair bit cancels by product additivity. The finite cross entropy is log(2) times the harmonic number because the expected truncated first coordinate grows by the preceding tail mass. Subtracting the fine and coarse KL values yields the displayed identity.

**Theorem 1.10 (Finite limit of cutoff Shannon entropy).**

Lean statement: `D5/S3/Divergence/CoinfiniteExhaustion.tendsto_cut_shannon`

*Proof.* Machine-checked in Lean as `D5/S3/Divergence/CoinfiniteExhaustion.tendsto_cut_shannon` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Tai-Hsuan Yang (2026). *Quantum data processing equality*. DOI: [10.48550/arXiv.2609.33815](https://doi.org/10.48550/arXiv.2609.33815). URL: <https://arxiv.org/abs/2609.33815v2>.

*Commentary.*

The cutoff entropies converge to the Shannon series of the countable first law. The singleton series has a summable power bound with exponent 3/2, and the entropy of the merged tail tends to zero.

**Theorem 1.11 (Asymptotic loss along any compatible sequence).**

Lean statement: `D5/S3/Divergence/CoinfiniteExhaustion.tendsto_loss_sub_log_ratio`

*Proof.* Machine-checked in Lean as `D5/S3/Divergence/CoinfiniteExhaustion.tendsto_loss_sub_log_ratio` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Tai-Hsuan Yang (2026). *Quantum data processing equality*. DOI: [10.48550/arXiv.2609.33815](https://doi.org/10.48550/arXiv.2609.33815). URL: <https://arxiv.org/abs/2609.33815v2>.

*Commentary.*

For every natural cutoff sequence a with n ≤ a(n), the loss at cutoffs a(n) and n minus log(2) log(a(n)/n) tends to zero at infinity. No monotonicity of a is required for this estimate.

**Theorem 1.12 (Limit when the cutoff ratio converges).**

Lean statement: `D5/S3/Divergence/CoinfiniteExhaustion.tendsto_loss_of_ratio`

*Proof.* Machine-checked in Lean as `D5/S3/Divergence/CoinfiniteExhaustion.tendsto_loss_of_ratio` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Tai-Hsuan Yang (2026). *Quantum data processing equality*. DOI: [10.48550/arXiv.2609.33815](https://doi.org/10.48550/arXiv.2609.33815). URL: <https://arxiv.org/abs/2609.33815v2>.

*Commentary.*

For every compatible natural cutoff sequence a and real R, if a(n)/n converges to R, the actual losses converge to log(2) log(R). Compatibility implies R ≥ 1 and permits continuity of the natural logarithm.

**Theorem 1.13 (Different limits for two compatible exhaustions).**

$$\operatorname{Tendsto}\left((n \mapsto \operatorname{loss}\left(n, n\right)), atTop, \operatorname{nhds}\left(0\right)\right) \land \left(\operatorname{Tendsto}\left((n \mapsto \operatorname{loss}\left(2 \cdot n, n\right)), atTop, \operatorname{nhds}\left(\operatorname{log}\left(2\right) \cdot \operatorname{log}\left(2\right)\right)\right) \land 0 < \operatorname{log}\left(2\right) \cdot \operatorname{log}\left(2\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Divergence/CoinfiniteExhaustion.nonunique_exhaustion_loss` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Tai-Hsuan Yang (2026). *Quantum data processing equality*. DOI: [10.48550/arXiv.2609.33815](https://doi.org/10.48550/arXiv.2609.33815). URL: <https://arxiv.org/abs/2609.33815v2>.

*Commentary.*

Taking the fine cutoff to be n or 2n produces different limits of the true finite loss for the same two source laws and bit-erasure map. The diagonal loss vanishes at each cutoff. The doubled cutoff has ratio two for all positive indices.

**Theorem 1.14 (No common limit over nested exhaustions).**

Lean statement: `D5/S3/Divergence/CoinfiniteExhaustion.no_common_exhaustion_limit`

*Proof.* Machine-checked in Lean as `D5/S3/Divergence/CoinfiniteExhaustion.no_common_exhaustion_limit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Tai-Hsuan Yang (2026). *Quantum data processing equality*. DOI: [10.48550/arXiv.2609.33815](https://doi.org/10.48550/arXiv.2609.33815). URL: <https://arxiv.org/abs/2609.33815v2>.

*Commentary.*

There is no real limit shared by all monotone cutoff sequences a with n ≤ a(n), coherent nested clipping, and stochastic channels. The identity and doubled sequences are both monotone and compatible, so uniqueness of limits would equate zero with the positive square of log(2). Yang's section V.3 provides the von Neumann algebra setting for this diagonal counterexample.

## References

- Truth anchor: `D5/S3/Divergence/CoinfiniteExhaustion.eventually_resolves_atom`
- Truth anchor: `D5/S3/Divergence/CoinfiniteExhaustion.fine_states_are_restrictions`
- Truth anchor: `D5/S3/Divergence/CoinfiniteExhaustion.finite_states`
- Truth anchor: `D5/S3/Divergence/CoinfiniteExhaustion.fixed_source_states`
- Truth anchor: `D5/S3/Divergence/CoinfiniteExhaustion.loss_exact`
- Truth anchor: `D5/S3/Divergence/CoinfiniteExhaustion.no_common_exhaustion_limit`
- Truth anchor: `D5/S3/Divergence/CoinfiniteExhaustion.nonunique_exhaustion_loss`
- Truth anchor: `D5/S3/Divergence/CoinfiniteExhaustion.partitionChannel_outputs`
- Truth anchor: `D5/S3/Divergence/CoinfiniteExhaustion.partitionChannel_stochastic`
- Truth anchor: `D5/S3/Divergence/CoinfiniteExhaustion.partitionMap_comp`
- Truth anchor: `D5/S3/Divergence/CoinfiniteExhaustion.partitionMap_cutIndex`
- Truth anchor: `D5/S3/Divergence/CoinfiniteExhaustion.tendsto_cut_shannon`
- Truth anchor: `D5/S3/Divergence/CoinfiniteExhaustion.tendsto_loss_of_ratio`
- Truth anchor: `D5/S3/Divergence/CoinfiniteExhaustion.tendsto_loss_sub_log_ratio`
- Dependency: [D5/S3/Divergence/ProductAdditivity](ProductAdditivity.md)
- Dependency: [D5/S3/Entropy/Forgetting/CapacityMonotone](../Entropy/Forgetting/CapacityMonotone.md)
