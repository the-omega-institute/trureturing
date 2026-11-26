# The four ten-point equality patterns

## Abstract

Exactly four integer patterns, up to translation, attain the ten-point plastic-template bound and its corresponding real-power sumset size.

Let E be any finite subset of the integers with exactly ten elements. Write C(E) for the total number of translates contained in E of {0,2,3,4}, {0,3,5,6}, {0,5,7}, and {0,5,8,9}. These copies can equivalently be counted by their unique right endpoints. All intervals below contain integers. Define S₀=[0,9], S₁={0}∪[2,10], S₂={0,1}∪[3,10], and S₃={0,3}∪[5,12]. The notation translate(a,S) means {a+z : z ∈ S}, with a an arbitrary integer. For a real r, let A(r,E)={rᶻ : z ∈ E}; its sumset is an actual finite subset of the reals. Negative exponents, negative translations, and arbitrarily large initial gaps are allowed. The statement concerns ten points only.

**Theorem 1.1 (Complete ten-point classification).**

$$\forall (E : \operatorname{Finset}\left(\mathbb{Z}\right)), (\lvert E\rvert  = 10) \Rightarrow (((\operatorname{C}\left(E\right) = 14) \Leftrightarrow (\exists (a : \mathbb{Z}), (E = \operatorname{translate}\left(a, S_{0}\right)) \lor ((E = \operatorname{translate}\left(a, S_{1}\right)) \lor ((E = \operatorname{translate}\left(a, S_{2}\right)) \lor (E = \operatorname{translate}\left(a, S_{3}\right)))))) \land (\forall (r : \mathbb{R}), (1 < r) \Rightarrow ((r^{3} = r + 1) \Rightarrow ((\lvert \operatorname{A}\left(r, E\right) + \operatorname{A}\left(r, E\right)\rvert  = 41) \Leftrightarrow (\exists (a : \mathbb{Z}), (E = \operatorname{translate}\left(a, S_{0}\right)) \lor ((E = \operatorname{translate}\left(a, S_{1}\right)) \lor ((E = \operatorname{translate}\left(a, S_{2}\right)) \lor (E = \operatorname{translate}\left(a, S_{3}\right)))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Additive/PlasticTenPointEquality.whole_ten_point_equality` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Attila Bérczes (2010). *On the sumset of geometric progressions*. DOI: [10.5486/PMD.2010.4683](https://doi.org/10.5486/PMD.2010.4683). URL: <https://doi.org/10.5486/PMD.2010.4683>.

*Commentary.*

The finite-memory upper bound assigns a potential to every actual prefix. If a ten-point set has fourteen copies, its last potential is fourteen. At each removal of the maximum, the actual increment identity and the transition upper bound force the preceding prefix and its transition to be tight. The tight-predecessor constraints reduce the possibilities to prefixes of the four displayed models. For each model separately, the extension calculation identifies the entire new prefix, rather than only its memory state. Thus distinct histories sharing a state are not identified. This yields an induction on the actual finite set and its maximum, not a check of four examples alone. Every allowed clipped gap is at most three, so it equals the original gap; clipping therefore introduces no restriction on the input set. This argument uses upper-bound potentials and tightness, without requiring that every table entry be reachable or be an exact optimum. Conversely, each of the four complete models has total count fourteen, and translation preserves the count. For r>1 with r³=r+1, the collision identity gives |A(r,E)+A(r,E)|+C(E)=55. Consequently the real sumset has cardinality forty-one exactly for those same four translated patterns.

## References

- Truth anchor: `D5/S3/Arith/Additive/PlasticTenPointEquality.whole_ten_point_equality`
- Dependency: [D5/S3/Arith/Additive/PlasticExtremal](PlasticExtremal.md)
