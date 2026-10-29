# The attained mobile general position number of the integer lattice

## Abstract

Every positive dimensional integer lattice has attained mobile general position number two to the power two to the power dimension minus one.

For a natural dimension k, the vertices are all functions Fin k -> Int. The graph IntegerLatticeMotion.lattice k joins two vertices exactly when one coordinate changes by +1 or -1 and every other coordinate agrees. It is connected, and its graph distance is the sum of the absolute coordinate differences. CylinderSevenTen.IsGeneralPosition excludes every ordered triple of pairwise distinct occupied vertices whose middle vertex lies on a shortest path between the endpoints.

CylinderSevenTen.LegalMove G A B means that there are u in A and v outside A with G.Adj u v, B = insert v (A.erase u), and B in general position. Thus one occupied vertex moves along one actual edge into a vacant vertex and all other occupied vertices stay fixed. The occupied sets are finite, while the graph and the time index are unbounded.

**Definition 1.1 (One common covering trajectory).**

$$\forall (k : \mathrm{Nat}), \forall (S : \operatorname{Finset}\left((\operatorname{Fin}\left(k\right) \to \mathrm{Int})\right)), \operatorname{IsMobile}\left(S\right) = (\operatorname{CylinderSevenTen.IsGeneralPosition}\left(\operatorname{IntegerLatticeMotion.lattice}\left(k\right), S\right) \land \exists (c : \mathrm{Nat} \to \operatorname{Finset}\left((\operatorname{Fin}\left(k\right) \to \mathrm{Int})\right)), c\left(0\right) = S \land \left((\forall (t : \mathrm{Nat}), \operatorname{CylinderSevenTen.LegalMove}\left(\operatorname{IntegerLatticeMotion.lattice}\left(k\right), c\left(t\right), c\left(t + 1\right)\right)) \land \left((\forall (t : \mathrm{Nat}), \operatorname{CylinderSevenTen.IsGeneralPosition}\left(\operatorname{IntegerLatticeMotion.lattice}\left(k\right), c\left(t\right)\right)) \land (\forall (x : \operatorname{Fin}\left(k\right) \to \mathrm{Int}), \exists (t : \mathrm{Nat}), x \in c\left(t\right))\right)\right))$$

*Formalization.* `D5/S3/Combinatorics/Graph/GeneralPosition/IntegerLatticeMobile.IsMobile` (`✓ std3`).

*Citation.* Sandi Klavžar; Aditi Krishnakumar; Dorota Kuziak; Ethan Shallcross; James Tuite; Ismael G. Yero (2026). *Moving through Cartesian products, coronas and joins in general position*. DOI: [10.1016/j.dam.2025.10.041](https://doi.org/10.1016/j.dam.2025.10.041). URL: <https://arxiv.org/abs/2505.00535>.

*Commentary.*

Section 1.1 defines a mobile general position set by a sequence of legal moves starting at the set and visiting every graph vertex. Here the infinite lattice uses one sequence c indexed by all natural times. The same c starts at S, makes a legal move at every time, remains in general position at every time, and contains each lattice vertex at some finite time. Initial general position is explicit. No constant-cardinality premise is added.

**Theorem 1.2 (The exact bound is attained in every positive dimension).**

$$\forall (k : \mathrm{Nat}), 1 \le k \Rightarrow \left((\forall (S : \operatorname{Finset}\left((\operatorname{Fin}\left(k\right) \to \mathrm{Int})\right)), \operatorname{IsMobile}\left(S\right) \Rightarrow \operatorname{Finset.card}\left(S\right) \le 2^{2^{k - 1}}) \land (\exists (S : \operatorname{Finset}\left((\operatorname{Fin}\left(k\right) \to \mathrm{Int})\right)), \operatorname{IsMobile}\left(S\right) \land \operatorname{Finset.card}\left(S\right) = 2^{2^{k - 1}})\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/GeneralPosition/IntegerLatticeMobile.result` (`✓ std3`). ∎

*Resolves.* `Problems/klavzar-et-al-2025-mobile-general-position-integer-lattices` (proved) by `D5/S3/Combinatorics/Graph/GeneralPosition/IntegerLatticeMobile.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"klavzar-et-al-2025-mobile-general-position-integer-lattices","declaration_gid":"D5/S3/Combinatorics/Graph/GeneralPosition/IntegerLatticeMobile.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Sandi Klavžar; Aditi Krishnakumar; Dorota Kuziak; Ethan Shallcross; James Tuite; Ismael G. Yero (2026). *Moving through Cartesian products, coronas and joins in general position*. DOI: [10.1016/j.dam.2025.10.041](https://doi.org/10.1016/j.dam.2025.10.041). URL: <https://arxiv.org/abs/2505.00535>.

*Commentary.*

Section 5, second bullet, asks whether the known static value 2^(2^(k-1)) is also the mobile value in higher dimensional infinite grids. The theorem gives both the upper bound for every finite mobile S and an actual finite mobile set attaining it, for every natural k at least one, including all k at least three. The upper bound uses only initial general position: graph geodesic betweenness equals coordinate betweenness, so IntegerLatticeStatic.card_le applies, including to the empty set. IntegerLatticeStatic.exists_attaining supplies a nonempty coordinate general-position set S of the exact size. IntegerLatticeFiniteMotion.scaled_finset_mobile supplies one common covering trajectory from the fourfold image of S and proves that this image has the same cardinality. Its additional derived cardinality invariant is discarded when proving IsMobile. The initial attaining set is the fourfold image; no motion from the unscaled S to that image is asserted. There is no restriction to a finite box or to a bounded traversal duration, and no assumed optimum or independent trajectory for each target vertex.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/GeneralPosition/IntegerLatticeMobile.IsMobile`
- Truth anchor: `D5/S3/Combinatorics/Graph/GeneralPosition/IntegerLatticeMobile.result`
- Dependency: [D5/S3/Combinatorics/Graph/GeneralPosition/IntegerLatticeFiniteMotion](IntegerLatticeFiniteMotion.md)
- Dependency: [D5/S3/Combinatorics/Graph/GeneralPosition/IntegerLatticeStatic](IntegerLatticeStatic.md)
