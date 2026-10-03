# Actual Endpoint History Kernel

## Abstract

Finite endpoint histories of actual avoiders have exact probability products and literal fixed-coordinate cylinders.

Every carrier is a subtype of the actual 2413/3142-avoiding permutations of Fin(n). State none is the whole class U. State some(s) is J(s), with no proper cut of sign s. For lengths at least two this is the opposite proper-cut class; zero and singleton lengths retain their actual conventions. False denotes direct sums and true skew sums.

An EndpointHistory stops in an actual carrier, emits a specified left shape from J(s) and resets to U, or removes a specified right shape from U and conditions its child to J(s). At each continued step both lengths are positive, and the source is U or J(not s). Assemble reconstructs an actual permutation by frozen blockSum. Event is the actual-permutation range of this reconstruction; Trace certifies every actual minimum cut. These descriptions do not replace the actual carrier by a sampler.

**Theorem 1.1 (Actual history counts and conditional remaining shapes).**

$$\forall h, \operatorname{card}\left(\operatorname{Event}\left(h\right)\right)=\operatorname{card}\left(\operatorname{Leaf}\left(h\right)\right) \land \frac{\operatorname{P}\left(\operatorname{Event}\left(h\right)\right)}{\operatorname{P}\left(\operatorname{Allowed}\left(h\right)\right)}=\operatorname{weight}\left(h\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Patterns/Separable/EndpointHistoryKernel.endpoint_history_count_kernel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite typed history, all terminal actual samples reconstruct in its source class and satisfy all minimum-cut certificates. Reconstruction is injective. The full actual history event has the cardinality of its terminal actual carrier. Its real probability conditional on the initial actual carrier is weight(h), the product of child-cardinality/parent-cardinality ratios at all steps. Every carrier has an identity or reversal witness, so the source denominators are nonzero. For every terminal predicate A, its reconstructed actual event has cardinality card(A); conditional on the history event its probability is card(A)/card(Leaf). Thus the remaining shape is genuinely uniform in its actual conditioned class. The theorem also proves emitted+remaining <= n, removed+remaining = n, and removed <= steps*K for every endpoint-length cap K. For a blocked opposite-sign source and n >= 2 it explicitly supplies the indicated proper-cut sign.

**Theorem 1.2 (Literal finite-alphabet cylinder transport).**

$$\forall h,B,v,x, B<\operatorname{remaining}\left(h\right) \Rightarrow \operatorname{take}\left(\operatorname{emitted}\left(h\right), \operatorname{literal}\left(\operatorname{assemble}\left(h, x\right), B, v\right)\right)=\operatorname{word}\left(h, B, v\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Patterns/Separable/EndpointHistoryKernel.endpoint_history_literal_cylinder` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every history, finite alphabet size B, low-label offset v, and terminal actual sample x, if B is smaller than the terminal length, the first emitted positions of the literal reconstructed permutation equal word(h,B,v). Values 0 through B-1 are represented as some(Fin B), and every other value by none, the star. The word emits literal low values at direct left steps and stars at skew left steps. It advances v by a left length exactly at direct emissions, and by a right length exactly at skew removals. Right suffixes stay pending after the remaining active interval. For every number of positions at most emitted and every predicate on the finite-alphabet prefix, its full actual probability intersected with the history event is either the whole history probability or zero, according to its value on the computed literal word. The transport also holds for every source length n > H*K+B when steps <= H and every encountered endpoint length is <= K. Finally, for every m smaller than the terminal length and at most the emitted count, the actual absolute event pi(i) != i for every position i < m selects either the entire history or none. Its decision is the literal word test record[i] != some(i) in alphabet Fin(m), not a standardized fixedpoint flag.

The kernel constructs exact finite histories and surviving conditional laws. It does not establish an exhaustive Good-history partition or truncation errors, actual count asymptotics, the infinite coupled law, limiting cylinders, occupation, hitting, or the all-positive-length derangement-ratio limit. No KPI settlement, freeze, or coverage is asserted.

## References

- Truth anchor: `D5/S1/Words/Patterns/Separable/EndpointHistoryKernel.endpoint_history_count_kernel`
- Truth anchor: `D5/S1/Words/Patterns/Separable/EndpointHistoryKernel.endpoint_history_literal_cylinder`
- Dependency: [D5/S1/Words/Patterns/Separable/MinimumCutKernel](MinimumCutKernel.md)
