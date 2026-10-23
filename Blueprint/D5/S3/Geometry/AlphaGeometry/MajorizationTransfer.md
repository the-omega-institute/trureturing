# MajorizationTransfer

## Abstract

Hardy--Littlewood--Polya transfer step for finite vectors.

**Definition 1.1 (prefixSum).**

$$\forall (n : \mathbb{N}), \forall (k : \mathbb{N}), \forall (x : (\operatorname{Fin}\left(n\right)) \to (\mathbb{R})), \operatorname{prefixSum}\left(k, x\right) = (\sum_{i \in \operatorname{Finset}. \operatorname{univ}. \operatorname{filter}\left((\operatorname{fun} i : \operatorname{Fin}\left(n\right)\mapsto (((i) : (\mathbb{N})) < k))\right)} (x\left(i\right)))$$

*Formalization.* `D5/S3/Geometry/AlphaGeometry/MajorizationTransfer.prefixSum` (`✓ std3`).

*Citation.* Jon Crall; GPT-5.6 Thinking; Claude Fable 5; Claude Opus 5 (2026). *LeanPool finite-vector Hardy–Littlewood–Pólya transfer construction*. URL: <https://github.com/LeanPool/lean-pool/blob/7498a16d2393e1f02245cb265d67ec4fb2587814/LeanPool/DavisKahan/ForTauCeti/Analysis/Convex/Majorization.lean>.

*Commentary.*

The finite-vector initial sum contains precisely the coordinates whose natural indices are below k.

**Theorem 1.2 (prefixSum_eq_full_sum_of_le).**

$$\forall (n : \mathbb{N}), \forall (x : (\operatorname{Fin}\left(n\right)) \to (\mathbb{R})), \forall (k : \mathbb{N}), (n \le k) \Rightarrow (\operatorname{prefixSum}\left(k, x\right) = \sum_{i} (x\left(i\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/AlphaGeometry/MajorizationTransfer.prefixSum_eq_full_sum_of_le` (`✓ std3`). ∎

*Citation.* Jon Crall; GPT-5.6 Thinking; Claude Fable 5; Claude Opus 5 (2026). *LeanPool finite-vector Hardy–Littlewood–Pólya transfer construction*. URL: <https://github.com/LeanPool/lean-pool/blob/7498a16d2393e1f02245cb265d67ec4fb2587814/LeanPool/DavisKahan/ForTauCeti/Analysis/Convex/Majorization.lean>.

*Commentary.*

An initial sum is the full sum once its cutoff reaches the vector length.

**Definition 1.3 (IsTTransform).**

$$\forall (n : \mathbb{N}), \forall (y : (\operatorname{Fin}\left(n\right)) \to (\mathbb{R})), \forall (q : (\operatorname{Fin}\left(n\right)) \to (\mathbb{R})), \operatorname{IsTTransform}\left(y, q\right) \iff (\exists (j l : \operatorname{Fin}\left(n\right)) (c : \mathbb{R}) , (0 \le c \land \left(c \le 1 \land q = ((1 - c)) \cdot (y) + (c) \cdot (((y) \circ (\operatorname{Equiv}. \operatorname{swap}\left(j, l\right))))\right)))$$

*Formalization.* `D5/S3/Geometry/AlphaGeometry/MajorizationTransfer.IsTTransform` (`✓ std3`).

*Citation.* Jon Crall; GPT-5.6 Thinking; Claude Fable 5; Claude Opus 5 (2026). *LeanPool finite-vector Hardy–Littlewood–Pólya transfer construction*. URL: <https://github.com/LeanPool/lean-pool/blob/7498a16d2393e1f02245cb265d67ec4fb2587814/LeanPool/DavisKahan/ForTauCeti/Analysis/Convex/Majorization.lean>.

*Commentary.*

This definition records the displayed construction. All sums and products range over the displayed finite index type; ℝ operations use real arithmetic.

**Theorem 1.4 (exists_isTTransform_of_not_forall_le).**

$$\forall (n : \mathbb{N}), \forall (z : (\operatorname{Fin}\left(n\right)) \to (\mathbb{R})), \forall (q : (\operatorname{Fin}\left(n\right)) \to (\mathbb{R})), (\operatorname{Antitone}\left(z\right)) \Rightarrow ((\forall i , (0 \le z\left(i\right))) \Rightarrow ((\forall i , (0 \le q\left(i\right))) \Rightarrow ((\forall k , (\operatorname{prefixSum}\left(k, z\right) \le \operatorname{prefixSum}\left(k, q\right))) \Rightarrow ((\neg (\forall i , (z\left(i\right) \le q\left(i\right)))) \Rightarrow (\exists q' , (\operatorname{IsTTransform}\left(q, q'\right) \land \left((\forall i , (0 \le q'\left(i\right))) \land \left((\forall k , (\operatorname{prefixSum}\left(k, z\right) \le \operatorname{prefixSum}\left(k, q'\right))) \land ((\operatorname{Finset}. \operatorname{univ}. \operatorname{filter}\left(\operatorname{fun} i \mapsto (z\left(i\right) \ne q'\left(i\right))\right))). \operatorname{card} < ((\operatorname{Finset}. \operatorname{univ}. \operatorname{filter}\left(\operatorname{fun} i \mapsto (z\left(i\right) \ne q\left(i\right))\right))). \operatorname{card}\right)\right)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/AlphaGeometry/MajorizationTransfer.exists_isTTransform_of_not_forall_le` (`✓ std3`). ∎

*Citation.* Jon Crall; GPT-5.6 Thinking; Claude Fable 5; Claude Opus 5 (2026). *LeanPool finite-vector Hardy–Littlewood–Pólya transfer construction*. URL: <https://github.com/LeanPool/lean-pool/blob/7498a16d2393e1f02245cb265d67ec4fb2587814/LeanPool/DavisKahan/ForTauCeti/Analysis/Convex/Majorization.lean>.

*Commentary.*

LeanPool’s Hardy–Littlewood–Pólya transfer construction is transplanted without re-proof. Source: https://github.com/LeanPool/lean-pool/blob/7498a16d2393e1f02245cb265d67ec4fb2587814/LeanPool/DavisKahan/ForTauCeti/Analysis/Convex/Majorization.lean. Apache-2.0; the full LICENSE and NOTICE chain remain in docs/reports/brooks-suppliers/daviskahan-LICENSE.txt and daviskahan-NOTICE.txt. The logarithmic-simplex application is the p=∞ clause of Gibilisco and Isola, Conjecture 4.1 (DOI 10.1063/1.1834693; https://arxiv.org/abs/math-ph/0407007v2).

## References

- Truth anchor: `D5/S3/Geometry/AlphaGeometry/MajorizationTransfer.IsTTransform`
- Truth anchor: `D5/S3/Geometry/AlphaGeometry/MajorizationTransfer.exists_isTTransform_of_not_forall_le`
- Truth anchor: `D5/S3/Geometry/AlphaGeometry/MajorizationTransfer.prefixSum`
- Truth anchor: `D5/S3/Geometry/AlphaGeometry/MajorizationTransfer.prefixSum_eq_full_sum_of_le`
