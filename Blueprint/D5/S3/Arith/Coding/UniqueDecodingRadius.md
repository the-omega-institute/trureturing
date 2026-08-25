# Unique Decoding Radius

## Abstract

A minimum-distance code has a unique nearby codeword below half the minimum distance, including the canonical integral correction radius.

**Theorem 1.1 (Minimum distance gives the unique decoding radius).**

$$\operatorname{MinDistanceAtLeast}\left(C, d\right) \Rightarrow\\{}(\forall c, r, e, (c \in C \land \operatorname{hammingDist}\left(r, c\right) \leq e \land 2 \times e < d) \Rightarrow \exists x, x \in C \land \operatorname{hammingDist}\left(r, x\right) \leq e \land\\{}(\forall y, (y \in C \land \operatorname{hammingDist}\left(r, y\right) \leq e) \Rightarrow y = x)) \land\\{}(\forall c, r, (c \in C \land \operatorname{hammingDist}\left(r, c\right) \leq \left\lfloor\frac{d - 1}{2}\right\rfloor) \Rightarrow \exists x, x \in C \land \operatorname{hammingDist}\left(r, x\right) \leq \left\lfloor\frac{d - 1}{2}\right\rfloor \land\\{}(\forall y, (y \in C \land \operatorname{hammingDist}\left(r, y\right) \leq \left\lfloor\frac{d - 1}{2}\right\rfloor) \Rightarrow y = x)).$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Coding/UniqueDecodingRadius.unique_decoding_radius` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If the received word and a competing codeword are each within e coordinates of the true word, the Hamming triangle inequality puts the two codewords at distance at most 2e. The strict minimum-distance bound therefore forces them to coincide.

Natural-number division makes twice floor((d - 1) / 2) strictly less than every positive d. At d = 0, radius zero still has a unique candidate because zero Hamming distance is equality.

## References

- Truth anchor: `D5/S3/Arith/Coding/UniqueDecodingRadius.unique_decoding_radius`
- Dependency: [D5/S3/Arith/Coding/ResidueCodeErrorDetection](ResidueCodeErrorDetection.md)
