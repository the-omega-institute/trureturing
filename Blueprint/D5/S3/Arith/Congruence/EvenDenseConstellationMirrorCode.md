# Even Dense Constellation Mirror Code

## Abstract

An even two-four-gap constellation that omits a residue modulo three has a reversal-fixed gap code.

**Theorem 1.1 (The gap code of an even admissible dense constellation is self-reversing).**

$$\begin{gathered}\forall H \in \operatorname{List}\left(\mathbb{Z}\right),\\{}((\forall i \in \mathbb{N}, i + 1 < \operatorname{length}\left(H\right) \Rightarrow (H_{i + 1} - H_{i} = 2 \lor H_{i + 1} - H_{i} = 4)) \land\\{}(\exists r \in \operatorname{ZMod}\left(3\right), \forall i \in \mathbb{N}, i < \operatorname{length}\left(H\right) \Rightarrow \operatorname{residue}\left(3, H_{i}\right) \neq r) \land\\{}\operatorname{Even}\left(\operatorname{length}\left(H\right)\right)) \Rightarrow\\{}\operatorname{reverse}\left(\operatorname{zipWith}\left((u, v \mapsto \operatorname{decide}\left(v - u = 4\right)), H, \operatorname{tail}\left(H\right)\right)\right) = \operatorname{zipWith}\left((u, v \mapsto \operatorname{decide}\left(v - u = 4\right)), H, \operatorname{tail}\left(H\right)\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Congruence/EvenDenseConstellationMirrorCode.even_dense_constellation_gap_code_self` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let points be an integer constellation whose consecutive gaps are all two or four. If one residue modulo three is omitted, two consecutive gaps cannot agree: three points separated by equal gaps would visit every residue.

The constructed Boolean gap code therefore alternates. An even number of points gives the code odd length, so reversing it preserves every symbol.

## References

- Truth anchor: `D5/S3/Arith/Congruence/EvenDenseConstellationMirrorCode.even_dense_constellation_gap_code_self`
