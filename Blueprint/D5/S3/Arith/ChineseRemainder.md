# Chinese Remainder Bijectivity

## Abstract

The natural map modulo coprime factors is bijective.

<a id="describe-the-natural-map-modulo-coprime-factors-is-bijective"></a>

**Theorem 1.1 (The natural map modulo coprime factors is bijective).**

$$\gcd(m,n)=1 \Rightarrow \left(\mathbb{Z}/mn\mathbb{Z} \to \mathbb{Z}/m\mathbb{Z}\times\mathbb{Z}/n\mathbb{Z},\ x\mapsto(x\operatorname{mod}m,x\operatorname{mod}n)\right)\text{ is bijective}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/ChineseRemainder.chinese_remainder_bijective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For coprime natural numbers m and n, the theorem fixes the natural map from integers modulo m times n to the product of the residue rings modulo m and modulo n. Its two readings are the canonical casts to the factor moduli. The conclusion states that this displayed map is bijective, rather than merely asserting that some bijection between the two finite carriers exists.

The atom's proof skeleton establishes injectivity from coprimality and then obtains surjectivity by counting the two finite carriers. The formal proof uses Mathlib's ZMod.chineseRemainder ring equivalence, whose forward function is definitionally the same ZMod.castHom natural map displayed in the statement, and assembles the result through the equivalence's bijectivity. This is a faithful library-level assembly of the atomic skeleton under precedent 6.1, and it asserts no numerical certificate.

## References

- Truth anchor: `D5/S3/Arith/ChineseRemainder.chinese_remainder_bijective`
