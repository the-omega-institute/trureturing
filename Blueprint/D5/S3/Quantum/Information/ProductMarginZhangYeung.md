# ProductMarginZhangYeung

## Abstract

The spectral gap on the actual product-margin state

**Theorem 1.1 (The actual spectral entropy identity).**

$$\forall c,d:LocalPair,\ \forall k:\operatorname{Coupling}(c, d),\ \operatorname{zhangYeungGap}(k)=\operatorname{log}(2)-\operatorname{h}(\operatorname{re}(\operatorname{trace}(\operatorname{K}(k))))+\operatorname{qubitHolevo}(\operatorname{x}(c), \operatorname{z}(c))+\operatorname{qubitHolevo}(\operatorname{x}(d), \operatorname{z}(d))-3\cdot \operatorname{quantumMutualInformation}(\operatorname{productMixture}(c, d))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/ProductMarginZhangYeung.actual_gap_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Codex CLI (2026). *A harmonic-mean certificate for the unequal-local-pair product-margin quantum Zhang–Yeung family*. URL: <https://github.com/the-omega-institute/trureturing>.

*Commentary.*

The two LocalPair parameters contain four independent nonnegative real coordinates xC, zC, xD, zD, each pair in the closed unit disk. Coupling contains an arbitrary complex positive semidefinite K bounded by P and Q, where P is the product of the positive local members and Q is the product of the negative members. The actual density on two classical bits and two qubits has blocks (P-K)/2, K/2, K/2, (Q-K)/2. Its entries, positivity and trace normalization are retained even when a block vanishes.

Delta is the original Zhang--Yeung combination of natural-log von Neumann entropies of actual partial traces. Its conditional information terms are 2 I(C:D|A), I(C:D|B), I(A:C|D) and I(A:D|C), with I(A:B)-I(C:D). The two row and column marginals are uniform pointer records of P and Q. Pointer orthogonality gives the cq entropy formula without imposing orthogonality on the prepared qubits or normalizing a zero-weight block. The AB entropy is log(2)+h(Re Tr K), including both endpoints.

The right side uses the actual symmetric local Holevo entropies and the mutual information of M=(P+Q)/2. Establishing nonnegativity requires the information estimates for the actual prepared states in addition to this identity.

**Theorem 1.2 (The four-parameter product-margin inequality).**

$$\forall c,d:LocalPair,\ \forall k:\operatorname{Coupling}(c, d),\ 0\le \operatorname{zhangYeungGap}(k)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/ProductMarginZhangYeung.actual_zhang_yeung_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Codex CLI (2026). *A harmonic-mean certificate for the unequal-local-pair product-margin quantum Zhang–Yeung family*. URL: <https://github.com/the-omega-institute/trureturing>.

*Commentary.*

For every two independent closed-disk LocalPair parameters and every complex positive common lower matrix K, the original spectral Zhang--Yeung gap of the actual density is nonnegative. No information estimate, commutation or strict positivity is an input hypothesis.

When both x coordinates are less than one, the actual marginal reference states are faithful even if the joint density is singular. The canonical product-recovery identity identifies their mutual information with support-aware relative entropy. Local preparation channels map both each intermediate cq density and its product reference to the physical output. Their DPI bounds combine with qubit Holevo contraction, the common-trace bound and the closed-interval scalar entropy certificate. If an x coordinate equals one, the corresponding z is zero and the CD state is directly a product. Zero reliabilities, zero weights and pure prepared states remain included.

The conclusion concerns this four-parameter classical-bit product-margin construction. It makes no assertion for arbitrary four-party quantum states or for a coordinate-free extension.

## References

- Truth anchor: `D5/S3/Quantum/Information/ProductMarginZhangYeung.actual_gap_identity`
- Truth anchor: `D5/S3/Quantum/Information/ProductMarginZhangYeung.actual_zhang_yeung_nonneg`
- Dependency: [D5/S3/Quantum/Divergence/CanonicalChannelDPI](../Divergence/CanonicalChannelDPI.md)
- Dependency: [D5/S3/Quantum/Divergence/CanonicalProductRecovery](../Divergence/CanonicalProductRecovery.md)
- Dependency: [D5/S3/Quantum/Foundation/FinitePreparationChannel](../Foundation/FinitePreparationChannel.md)
- Dependency: [D5/S3/Quantum/Information/OrthogonalRecordEntropy](OrthogonalRecordEntropy.md)
- Dependency: [D5/S3/Quantum/Information/ProductMarginEntropyCertificate](ProductMarginEntropyCertificate.md)
- Dependency: [D5/S3/Quantum/Information/ProductMarginQubitOrder](ProductMarginQubitOrder.md)
- Dependency: [D5/S3/Quantum/Information/QubitEntropyContraction](QubitEntropyContraction.md)
