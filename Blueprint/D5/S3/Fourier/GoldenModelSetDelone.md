# An Explicit Golden Delone Set

## Abstract

The complete golden model set has explicit separation and global covering witnesses.

**Theorem 1.1 (Internal displacement bounds force physical separation).**

$$u,v\in \operatorname{GoldenInt}\left(\right), u\neq v, B\in \mathbb{R}, \operatorname{abs}\left(\operatorname{internal}\left(u\right)-\operatorname{internal}\left(v\right)\right)\le B \Rightarrow 1\le \operatorname{abs}\left(\operatorname{emb}\left(u\right)-\operatorname{emb}\left(v\right)\right)\times B$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/GoldenModelSetDelone.norm_separation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Internal(u) is embedding(conj(u)), and emb is the distinguished real embedding. The real bound B is arbitrary; no positivity hypothesis is needed. The nonzero integer norm of u-v has absolute value at least one.

**Theorem 1.2 (Packing radius one half and covering radius three).**

$$\exists D\in \operatorname{DeloneSet}\left(R\right), \operatorname{carrier}\left(D\right)=\operatorname{modelSet}\left(W\right) \land \operatorname{packingRadius}\left(D\right)=\frac{1}{2} \land \operatorname{coveringRadius}\left(D\right)=3$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/GoldenModelSetDelone.exists_golden_modelSet_delone` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

There are no hypotheses. Here R is the real line, W is the existing closed goldenWindow [-phi^(-2), phi^(-1)], and modelSet is D5.S1.Scale.modelSet: all physical embeddings of golden integers whose conjugate embedding belongs to W. The radii are nonnegative reals.

Distinct selected points are at least one apart by the norm bound. For every real x, put q=2*phi-1, b=floor(x/q), and a=floor(phi-1-b*(1-phi)). The golden integer (a,b) has conjugate coordinate in W and physical distance at most three from x. The scheme adapter transports these witnesses into Certificate, whose existing toDeloneSet conversion produces the asserted bundle.

The carrier is bi-infinite. This result makes no relative-density claim about the natural-number-indexed betaGolden image.

## References

- Truth anchor: `D5/S3/Fourier/GoldenModelSetDelone.exists_golden_modelSet_delone`
- Truth anchor: `D5/S3/Fourier/GoldenModelSetDelone.norm_separation`
- Dependency: [D5/S1/Deficit/ModelSet/GoldenModelSetSelfSimilar](../../S1/Deficit/ModelSet/GoldenModelSetSelfSimilar.md)
- Dependency: [D5/S3/Fourier/DeloneModelSetCertificate](DeloneModelSetCertificate.md)
- Dependency: [D5/S3/Fourier/GoldenCutProjectSchemeAdapter](GoldenCutProjectSchemeAdapter.md)
