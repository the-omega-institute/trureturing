# Weight injectivity for an sl₂ triple

## Abstract

Lowering powers are injective at natural weights under local raising nilpotence.

**Theorem 1.1 (Zero kernel of a lowering power).**

$$\forall K \in \operatorname{Type},\; [\operatorname{Field}\left(K\right)] [\operatorname{CharZero}\left(K\right)] \forall V \in \operatorname{Type},\; [\operatorname{AddCommGroup}\left(V\right)] [\operatorname{Module}\left(K, V\right)] \forall h \in \operatorname{Module.End}\left(K, V\right),\; \forall e \in \operatorname{Module.End}\left(K, V\right),\; \forall f \in \operatorname{Module.End}\left(K, V\right),\; [\operatorname{IsSl2Triple}\left(h, e, f\right)] \forall n \in \mathbb{N},\; \forall v \in V,\; \forall q \in \mathbb{N},\; \forall k \in \mathbb{N},\; h\left(v\right) = (q : K) \cdot v \Rightarrow \left(k \le q \Rightarrow \left((e^{n})\left(v\right) = 0 \Rightarrow \left((f^{k})\left(v\right) = 0 \Rightarrow v = 0\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/SpinChains/Sl2WeightInjectivity.lowering_kernel_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This standard fact about sl₂ triples generalizes the rational lemma used by HypereclecticNonShortening. The operators h, e and f are respectively the weight, raising and lowering operators. If v has natural weight q, a raising power annihilates v, and k is at most q, then f to the kth power can annihilate v only when v is zero. Induction on the raising exponent reduces to a primitive vector, whose lowering chain is nonzero through its highest weight. The field has characteristic zero; neither finite dimensionality nor global nilpotence is assumed. Powers of endomorphisms use composition, and the dot denotes scalar multiplication.

## References

- Truth anchor: `D5/S3/Quantum/SpinChains/Sl2WeightInjectivity.lowering_kernel_zero`
