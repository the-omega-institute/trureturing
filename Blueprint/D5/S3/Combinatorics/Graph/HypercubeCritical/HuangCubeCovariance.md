# Signed covariance of the actual Huang operator

## Abstract

Every actual cube equivalence intertwining coordinate flips admits a sign gauge whose pushforward commutes with Huang's fixed adjacency matrix.

Q(n) is the actual Boolean cube Fin n to Bool. The symbols flip and huangMatrix denote BalancedCriticalSpectrum.flip and the existing matrix from HypercubeSubQuorum, opened without changing its source. TRUE selects Huang's first recursive block; its directional signs therefore count earlier FALSE coordinates. The equivalences g and p act on vertices and coordinates respectively. Their sole geometric condition is g(flip(x,i)) = flip(g(x),p(i)); there is no assumed gauge, switching normal form, balance condition or positive dimension.

**Theorem 1.1 (A constructed gauge and full operator intertwining).**

$$\forall n \in \operatorname{Nat}\left(\right),\; \forall g \in \operatorname{Equiv}\left(\operatorname{Q}\left(n\right), \operatorname{Q}\left(n\right)\right),\; \forall p \in \operatorname{Equiv}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right)\right),\; (\forall x \in \operatorname{Q}\left(n\right),\; \forall i \in \operatorname{Fin}\left(n\right),\; g\left(\operatorname{flip}\left(x, i\right)\right) = \operatorname{flip}\left(g\left(x\right), p\left(i\right)\right)) \Rightarrow (\exists s \in \operatorname{Q}\left(n\right) \to \operatorname{Real}\left(\right),\; (\forall x \in \operatorname{Q}\left(n\right),\; (s\left(x\right) = 1) \lor (s\left(x\right) = -1)) \land ((\forall x \in \operatorname{Q}\left(n\right),\; \forall i \in \operatorname{Fin}\left(n\right),\; \operatorname{huangMatrix}\left(n, g\left(x\right), g\left(\operatorname{flip}\left(x, i\right)\right)\right) = s\left(x\right) \cdot \operatorname{huangMatrix}\left(n, x, \operatorname{flip}\left(x, i\right)\right) \cdot s\left(\operatorname{flip}\left(x, i\right)\right)) \land (\forall z \in \operatorname{Q}\left(n\right) \to \operatorname{Real}\left(\right),\; \operatorname{mulVec}\left(\operatorname{huangMatrix}\left(n\right), (y \mapsto s\left(\operatorname{symm}\left(g, y\right)\right) \cdot z\left(\operatorname{symm}\left(g, y\right)\right))\right) = (y \mapsto s\left(\operatorname{symm}\left(g, y\right)\right) \cdot \operatorname{mulVec}\left(\operatorname{huangMatrix}\left(n\right), z\right)\left(\operatorname{symm}\left(g, y\right)\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/HuangCubeCovariance.exists_signed_covariance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural dimension n, every equivalence g of Q(n), and every coordinate equivalence p satisfying the displayed flip law, one sign function s works simultaneously on all actual edges and all real vectors. The signed pushforward at y is s(g inverse(y)) times z(g inverse(y)); thus the gauge is evaluated in old coordinates. The coefficient law is H(g(x),g(flip(x,i))) = s(x) H(x,flip(x,i)) s(flip(x,i)). The last equality is equality of full functions, and uses the existing full matrix mulVec, including every vertex.

The proof multiplies the original edge signing by its geometric pullback. Edge-unit squares and reciprocity follow from matrix_sq_of_adj, matrix symmetry and flip involution. Evaluating gamma_anticommute on the constant-one function and applying gamma_apply gives negative square curvature for both signings, so their product is flat. A private dimension induction integrates that ratio: integrate the TRUE layer first and multiply by the head-edge ratio on the FALSE layer. Head-tail flatness supplies every remaining edge. At n=0 the constant-one function suffices. The actual matrix row is then restricted to its cube neighbors and bijectively indexed by coordinate flips. Reindexing those coordinates through p and cancelling s squared proves the operator equation. The construction is on its live proof path.

This algebraic bridge supports reconstruction after thin-slice cube geometry has supplied an actual vertex/coordinate equivalence. The genuine generalized Gray incidence support is the separate GrayGridComponent construction. Covariance alone does not identify an arbitrary support with that construction. The external research anchor is Hong, Wu and Xia, Graph Sensitivity of Cartesian Products with Matched Bridges, arXiv:2610.09483v1, Section 7 Problem 2, https://arxiv.org/html/2610.09483v1#Thmproblem2 . The original f2(Q9)=3-or-4 question, E15, the 258-vertex obstruction and universal component classification remain unresolved. No literature novelty or priority claim is made.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/HuangCubeCovariance.exists_signed_covariance`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/BalancedCubeGirth](BalancedCubeGirth.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/SupportedEigenSaturation](SupportedEigenSaturation.md)
