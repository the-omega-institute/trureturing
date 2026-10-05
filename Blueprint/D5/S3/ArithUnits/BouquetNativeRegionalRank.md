# Native Regional Rank on a Bouquet

## Abstract

Every native four-leg region has rank equal to its hit-loop count plus its padded central rank.

Let k and p be natural numbers with 2 <= k < p and p prime. Write K = GaloisField(p,2), I = Fin(k), L = Fin(4), and S = Fin(2). D is an arbitrary matrix from I times (I times S) to K. The selected region R is an arbitrary finite subset of I times L. Every rank below is the K-dimension of the image of the displayed linear map. The central and loop coordinates lambda and z both belong to I -> K.

**Definition 1.1 (Central forms).**

$$centralForm_{D,j,s}(\lambda)=\sum _{i\in \operatorname{Fin}\left(k\right)}\operatorname{D}\left(i, (j,s)\right)\cdot\lambda_{i}\quad a_{j}=\operatorname{centralForm}\left(D, j, 0\right),\quad b_{j}=\operatorname{centralForm}\left(D, j, 1\right)$$

*Formalization.* `D5/S3/ArithUnits/BouquetNativeRegionalRank.centralForm` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each loop has two central linear forms, using the two columns indexed by (j,0) and (j,1).

**Definition 1.2 (Selected loops).**

$$R_{j}=\{\ell\in \operatorname{Fin}\left(4\right)\mid (j,\ell)\in R\},\quad \operatorname{hitLoops}\left(R\right)=J=\{j\in \operatorname{Fin}\left(k\right)\mid R_{j}\neq \emptyset\},\quad H_{R}=|J|$$

*Formalization.* `D5/S3/ArithUnits/BouquetNativeRegionalRank.hitLoops` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A loop is hit exactly when at least one of its four actual rows belongs to R.

**Definition 1.3 (Actual selected map).**

$$F_{R}=\operatorname{actualMap}\left(D, R\right):K^{I}\times K^{I}\to K^{R},\quad F_{R}(\lambda,z)=(a_{j}(\lambda)+z_{j},a_{j}(\lambda)-z_{j},b_{j}(\lambda)+z_{j},b_{j}(\lambda)-z_{j})_{j\in I}|_{R}$$

*Formalization.* `D5/S3/ArithUnits/BouquetNativeRegionalRank.actualMap` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The four entries in each loop are indexed by 0,1,2,3 in that order. The map keeps exactly the coordinates in R; its domain contains both central and loop variables.

**Definition 1.4 (Padded central map).**

$$V_{R}=\operatorname{virtualMap}\left(D, R\right):K^{I}\to K^{I\times S},\quad V_{R}(\lambda)_{j}=\begin{cases}(0,0)&|R_{j}|\le 1\\(a_{j}(\lambda),0)&R_{j}=\{0,1\}\\(b_{j}(\lambda),0)&R_{j}=\{2,3\}\\(a_{j}(\lambda)-b_{j}(\lambda),0)&R_{j}\in \{\{0,2\},\{1,3\}\}\\(a_{j}(\lambda)+b_{j}(\lambda),0)&R_{j}\in \{\{0,3\},\{1,2\}\}\\(a_{j}(\lambda),b_{j}(\lambda))&|R_{j}|\ge 3\end{cases}$$

*Formalization.* `D5/S3/ArithUnits/BouquetNativeRegionalRank.virtualMap` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Here a and b in the table denote a_j(lambda) and b_j(lambda). Each block has two slots indexed by S, including the displayed zero padding. The six two-leg masks are handled individually and yield the four central constraints shown in the table.

**Theorem 1.5 (Native regional rank identity).**

$$\forall k,p\in \mathbb{N}, 2\le k<p\land \operatorname{Prime}\left(p\right)\implies \forall D:\operatorname{Matrix}\left(\operatorname{Fin}\left(k\right), \operatorname{Fin}\left(k\right)\times \operatorname{Fin}\left(2\right), \operatorname{GaloisField}\left(p, 2\right)\right),\forall R:\operatorname{Finset}\left(\operatorname{Fin}\left(k\right)\times \operatorname{Fin}\left(4\right)\right),\quad \operatorname{finrank}\left(\operatorname{GaloisField}\left(p, 2\right), \operatorname{range}\left(\operatorname{actualMap}\left(D, R\right)\right)\right)=\operatorname{card}\left(\operatorname{hitLoops}\left(R\right)\right)+\operatorname{finrank}\left(\operatorname{GaloisField}\left(p, 2\right), \operatorname{range}\left(\operatorname{virtualMap}\left(D, R\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ArithUnits/BouquetNativeRegionalRank.native_regional_rank` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An anchor is chosen from each hit loop using only R. Multiplying a row by its sign gives a central signed value plus z_j. Subtracting the anchor central value defines W_R. The kernel of F_R is linearly equivalent to the kernel of W_R times the functions on unhit loops: the forward map keeps lambda and the free loop coordinates, and the inverse sets each hit z_j to minus its signed anchor value. The table gives exactly the same central kernel as W_R, because 2 is nonzero in K. Rank-nullity on K^I times K^I proves the identity.

The assertion includes zero and dependent D, empty and full R, single rows, and k=2,p=3. It uses no injectivity, prescribed rank, or kernel equality assumption. Support, entropy, virtual-rank saturation, RT equivalence, and converse statements require separate assertions.

## References

- Truth anchor: `D5/S3/ArithUnits/BouquetNativeRegionalRank.actualMap`
- Truth anchor: `D5/S3/ArithUnits/BouquetNativeRegionalRank.centralForm`
- Truth anchor: `D5/S3/ArithUnits/BouquetNativeRegionalRank.hitLoops`
- Truth anchor: `D5/S3/ArithUnits/BouquetNativeRegionalRank.native_regional_rank`
- Truth anchor: `D5/S3/ArithUnits/BouquetNativeRegionalRank.virtualMap`
