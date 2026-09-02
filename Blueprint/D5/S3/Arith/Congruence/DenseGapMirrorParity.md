# Dense Gap Mirror Parity

## Abstract

Dense admissible integer configurations have parity-controlled reflection.

**Theorem 1.1 (Point-count parity determines the reflected gap code).**

$$\forall gapCount \in \mathbb{N}, offset \in \operatorname{Fin}\left(gapCount + 1\right) \to \mathbb{Z},\; \left(\left(\forall i \in \operatorname{Fin}\left(gapCount\right),\; offset\left(\operatorname{succ}\left(i\right)\right) - offset\left(\operatorname{castSucc}\left(i\right)\right) = 2 \lor offset\left(\operatorname{succ}\left(i\right)\right) - offset\left(\operatorname{castSucc}\left(i\right)\right) = 4\right) \land \left(\neg \operatorname{Surjective}\left((i: \operatorname{Fin}\left(gapCount + 1\right) \mapsto \operatorname{cast}\left(offset\left(i\right), \operatorname{ZMod}\left(3\right)\right))\right)\right)\right) \Rightarrow \operatorname{let} gapCode: \operatorname{List}\left(\operatorname{Bool}\left(\right)\right) := \operatorname{ofFn}\left((i: \operatorname{Fin}\left(gapCount\right) \mapsto \operatorname{decide}\left(offset\left(\operatorname{succ}\left(i\right)\right) - offset\left(\operatorname{castSucc}\left(i\right)\right) = 4\right))\right), \left(\operatorname{Even}\left(gapCount + 1\right) \Rightarrow \operatorname{reverse}\left(gapCode\right) = gapCode\right) \land \left(\operatorname{Odd}\left(gapCount + 1\right) \Rightarrow \operatorname{reverse}\left(gapCode\right) = \operatorname{map}\left(not, gapCode\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Congruence/DenseGapMirrorParity.dense_gap_mirror_parity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The configuration has gapCount plus one ordered integer offsets. Every adjacent gap is two or four, and the offsets do not cover every residue modulo three.

The Boolean gap code is constructed by recording four-gaps as true. Mod-three admissibility forces alternation; reflection fixes the code at even point count and complements it at odd count.

## References

- Truth anchor: `D5/S3/Arith/Congruence/DenseGapMirrorParity.dense_gap_mirror_parity`
