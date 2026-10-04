# Reconstructing endomorphisms of actual zigzags

## Abstract

A terminal endomorphism preserving the right filtration of a right-streamlined zigzag has exactly one natural lift.

**Theorem 1.1 (Unique reconstruction from the terminal right filtration).**

$$\forall K \in Type, D \in \operatorname{ActualZigzag}\left(K\right), n \in \operatorname{Nat}\left(\right), a \in \operatorname{TerminalLinearEndomorphism}\left(D, n\right),\; \left(\operatorname{Field}\left(K\right) \land \left(\operatorname{RightStreamlined}\left(D, n\right) \land \operatorname{PreservesEveryRightFiltrationLayer}\left(D, n, a\right)\right)\right) \Rightarrow \operatorname{ExistsUniqueNaturalEndomorphismWithTerminalComponent}\left(D, n, a\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/Persistence/ZigzagNaturalLift.exists_unique_natural_endomorphism` (`✓ std3`). ∎

*Citation.* Gunnar Carlsson and Vin de Silva (2008). *Zigzag Persistence*. URL: <https://arxiv.org/abs/0812.0197v1>.

*Commentary.*

K is any field. A prefix with vertices 0 through n contains one actual linear arrow of either orientation at each adjacent pair. Every forward arrow is injective and every backward arrow is surjective. The right filtration starts with zero and the first whole space. A forward step maps each old layer and appends the new whole space; a backward step prepends zero and takes inverse images of all old layers.

For every linear endomorphism a of the terminal space preserving every right-filtration layer, there exists exactly one natural endomorphism of the actual finite oriented path-category diagram whose terminal component is a. No compatible family, lift or naturality is assumed. The diagram evaluates each path by composing its actual arrows.

Backward induction restricts through an injective forward arrow and descends through the kernel quotient of a surjective backward arrow. Layer preservation proves that these predecessor maps preserve the predecessor filtration. The same injection or surjection forces each predecessor component. Path induction proves all naturality squares.

The endomorphism remark after Lemma 3.18 in Carlsson and de Silva, PDF pages 16 and 17, is the source. Zero vertices and arbitrary characteristic are included; finite dimensionality is unnecessary for this reconstruction. The prefix has n+1 vertices, so n=0 means a single vertex. A chain with no vertices has no terminal component. General interval classification and intrinsic occurrence uniqueness are separate conclusions.

## References

- Truth anchor: `D5/S3/HomologicalAlgebra/Persistence/ZigzagNaturalLift.exists_unique_natural_endomorphism`
