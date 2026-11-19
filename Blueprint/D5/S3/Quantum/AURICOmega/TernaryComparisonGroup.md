# Ternary comparison structures and their groups

## Abstract

Origin-free ternary comparison structures become groups at every base point.

**Definition 1.1 (Ternary comparison structures).**

Lean statement: `D5/S3/Quantum/AURICOmega/TernaryComparisonGroup.TernaryComparison`

*Formalization.* `D5/S3/Quantum/AURICOmega/TernaryComparisonGroup.TernaryComparison` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jeremiah Certaine (1943). *The ternary operation (abc) = ab^{-1}c of a group*. DOI: [10.1090/S0002-9904-1943-08042-1](https://doi.org/10.1090/S0002-9904-1943-08042-1).

*Commentary.*

A ternary comparison structure on a type M consists of a transfer tri : M -> M -> M -> M and a real reading kappa : M -> M -> R. The transfer satisfies tri x x z = z, tri x z z = x and tri (tri x y z) u v = tri x y (tri z u v) for all x, y, z, u, v. The reading satisfies kappa x y = kappa y x, kappa x y = 1 exactly when x = y, 0 <= kappa x y, kappa (tri x u v) (tri y u v) = kappa x y and kappa (tri u v x) (tri u v y) = kappa x y. For every natural number n, every family x : Fin n -> M and every c : Fin n -> R, the Gram form sum over i and j of c i * c j * kappa (x i) (x j) is nonnegative. No base point, binary product or topology is part of the data. The three transfer identities are the heap identities; the reading is additional structure.

**Definition 1.2 (Order sensitivity of the transfer).**

$$\forall M \in \operatorname{Type}*,\; \forall C \in \operatorname{TernaryComparison}\left(M\right),\; \operatorname{Noncommutative}\left(C\right) \Leftrightarrow \left(\exists x \in M, y \in M, z \in M,\; \operatorname{tri}\left(C, x, y, z\right) \ne \operatorname{tri}\left(C, z, y, x\right)\right)$$

*Formalization.* `D5/S3/Quantum/AURICOmega/TernaryComparisonGroup.Noncommutative` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The transfer is order sensitive when exchanging its two outer arguments changes its value for some triple.

**Definition 1.3 (Readings arbitrarily close to zero).**

$$\forall M \in \operatorname{Type}*,\; \forall C \in \operatorname{TernaryComparison}\left(M\right),\; \operatorname{TouchesZero}\left(C\right) \Leftrightarrow \left(\forall e \in \mathbb{R},\; 0 < e \Rightarrow \left(\exists x \in M, y \in M,\; \operatorname{kappa}\left(C, x, y\right) < e\right)\right)$$

*Formalization.* `D5/S3/Quantum/AURICOmega/TernaryComparisonGroup.TouchesZero` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every positive real e some pair of points has reading below e.

**Definition 1.4 (Chain connectivity of the reading).**

$$\forall M \in \operatorname{Type}*,\; \forall C \in \operatorname{TernaryComparison}\left(M\right),\; \operatorname{ChainConnected}\left(C\right) \Leftrightarrow \left(\forall e \in \mathbb{R},\; 0 < e \Rightarrow \left(\forall x \in M, y \in M,\; \operatorname{ReflTransGen}\left(\lambda a b. 1 - e < \operatorname{kappa}\left(C, a, b\right), x, y\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/AURICOmega/TernaryComparisonGroup.ChainConnected` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every positive real e, any two points are related by the reflexive transitive closure of the relation a, b with 1 - e < kappa a b; that is, they are joined by a finite chain whose consecutive readings exceed 1 - e.

**Definition 1.5 (Gram rank bounded by r).**

$$\forall M \in \operatorname{Type}*,\; \forall C \in \operatorname{TernaryComparison}\left(M\right),\; \forall r \in \mathbb{N},\; \operatorname{GramRankLE}\left(C, r\right) \Leftrightarrow \left(\forall n \in \mathbb{N},\; \forall x \in \operatorname{Fin}\left(n\right) \to M,\; \operatorname{rank}\left((\operatorname{kappa}\left(C, x\left(i\right), x\left(j\right)\right))_{i,j \in \operatorname{Fin}\left(n\right)}\right) \le r\right)$$

*Formalization.* `D5/S3/Quantum/AURICOmega/TernaryComparisonGroup.GramRankLE` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every finite Gram matrix of the reading, indexed by Fin n with entries kappa (x i) (x j), has rank at most r.

**Definition 1.6 (Feature maps into Euclidean r-space).**

$$\forall M \in \operatorname{Type}*,\; \forall C \in \operatorname{TernaryComparison}\left(M\right),\; \forall r \in \mathbb{N},\; \operatorname{HasFeatureRank}\left(C, r\right) \Leftrightarrow \left(\exists f \in M \to \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(r\right)\right),\; \forall x \in M, y \in M,\; \operatorname{kappa}\left(C, x, y\right) = \langle f\left(x\right), f\left(y\right) \rangle_{\mathbb{R}}\right)$$

*Formalization.* `D5/S3/Quantum/AURICOmega/TernaryComparisonGroup.HasFeatureRank` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The reading is the real inner product of the images of a single map f from M into the Euclidean space of dimension r.

**Definition 1.7 (The group at a base point).**

Lean statement: `D5/S3/Quantum/AURICOmega/TernaryComparisonGroup.groupAt`

*Formalization.* `D5/S3/Quantum/AURICOmega/TernaryComparisonGroup.groupAt` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jeremiah Certaine (1943). *The ternary operation (abc) = ab^{-1}c of a group*. DOI: [10.1090/S0002-9904-1943-08042-1](https://doi.org/10.1090/S0002-9904-1943-08042-1).

*Commentary.*

For a base point o, groupAt C o is the group structure on M with product x * y = tri x o y, identity o and inverse x^-1 = tri o x o. Associativity is the transfer associativity with the two middle arguments equal to o. The left and right identity laws are tri o o y = y and tri x o o = x. The inverse law tri (tri o x o) o x = o follows from associativity and the two cancellation identities.

**Theorem 1.8 (The transfer recovered at any base point).**

$$\forall M \in \operatorname{Type}*,\; \forall C \in \operatorname{TernaryComparison}\left(M\right),\; \forall o \in M, x \in M, y \in M, z \in M,\; \operatorname{tri}\left(C, x, y, z\right) = \operatorname{mul}\left(\operatorname{groupAt}\left(C, o\right), \operatorname{mul}\left(\operatorname{groupAt}\left(C, o\right), x, \operatorname{inv}\left(\operatorname{groupAt}\left(C, o\right), y\right)\right), z\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/TernaryComparisonGroup.tri_eq_mul_inv_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jeremiah Certaine (1943). *The ternary operation (abc) = ab^{-1}c of a group*. DOI: [10.1090/S0002-9904-1943-08042-1](https://doi.org/10.1090/S0002-9904-1943-08042-1).

*Commentary.*

In the group at o, x * y^-1 * z unfolds to tri (tri x o (tri o y o)) o z. Two applications of associativity and tri o o w = w reduce it to tri x o (tri o y z), and one reverse associativity step followed by tri x o o = x gives tri x y z. The base point o is arbitrary: the transfer is the same expression x * y^-1 * z in every one of these groups.

**Theorem 1.9 (Base change is a bijection).**

$$\forall M \in \operatorname{Type}*,\; \forall C \in \operatorname{TernaryComparison}\left(M\right),\; \forall o \in M, p \in M,\; \operatorname{Bijective}\left(x \mapsto \operatorname{tri}\left(C, x, o, p\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/TernaryComparisonGroup.baseChange_bijective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jeremiah Certaine (1943). *The ternary operation (abc) = ab^{-1}c of a group*. DOI: [10.1090/S0002-9904-1943-08042-1](https://doi.org/10.1090/S0002-9904-1943-08042-1).

*Commentary.*

For base points o and p, the map x -> tri x o p has the two-sided inverse x -> tri x p o: by associativity and the cancellation identities, tri (tri x o p) p o = x and tri (tri x p o) o p = x.

**Theorem 1.10 (Order sensitivity and noncommutativity).**

$$\forall M \in \operatorname{Type}*,\; \forall C \in \operatorname{TernaryComparison}\left(M\right),\; \forall o \in M,\; \operatorname{Noncommutative}\left(C\right) \Leftrightarrow \left(\exists x \in M, y \in M,\; \operatorname{tri}\left(C, x, o, y\right) \ne \operatorname{tri}\left(C, y, o, x\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/TernaryComparisonGroup.noncommutative_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jeremiah Certaine (1943). *The ternary operation (abc) = ab^{-1}c of a group*. DOI: [10.1090/S0002-9904-1943-08042-1](https://doi.org/10.1090/S0002-9904-1943-08042-1).

*Commentary.*

If the group at o were commutative, the recovery formula would give tri x y z = x * y^-1 * z = z * y^-1 * x = tri z y x for every triple, so an order-sensitive triple forces two noncommuting elements. Conversely, two elements x and y with tri x o y different from tri y o x form the order-sensitive triple (x, o, y).

**Lemma 1.11 (The reading on the diagonal).**

$$\forall M \in \operatorname{Type}*,\; \forall C \in \operatorname{TernaryComparison}\left(M\right),\; \forall x \in M,\; \operatorname{kappa}\left(C, x, x\right) = 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/TernaryComparisonGroup.kappa_self` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This is the reverse direction of the axiom that the reading equals one exactly on the diagonal.

## References

- Truth anchor: `D5/S3/Quantum/AURICOmega/TernaryComparisonGroup.ChainConnected`
- Truth anchor: `D5/S3/Quantum/AURICOmega/TernaryComparisonGroup.GramRankLE`
- Truth anchor: `D5/S3/Quantum/AURICOmega/TernaryComparisonGroup.HasFeatureRank`
- Truth anchor: `D5/S3/Quantum/AURICOmega/TernaryComparisonGroup.Noncommutative`
- Truth anchor: `D5/S3/Quantum/AURICOmega/TernaryComparisonGroup.TernaryComparison`
- Truth anchor: `D5/S3/Quantum/AURICOmega/TernaryComparisonGroup.TouchesZero`
- Truth anchor: `D5/S3/Quantum/AURICOmega/TernaryComparisonGroup.baseChange_bijective`
- Truth anchor: `D5/S3/Quantum/AURICOmega/TernaryComparisonGroup.groupAt`
- Truth anchor: `D5/S3/Quantum/AURICOmega/TernaryComparisonGroup.kappa_self`
- Truth anchor: `D5/S3/Quantum/AURICOmega/TernaryComparisonGroup.noncommutative_iff`
- Truth anchor: `D5/S3/Quantum/AURICOmega/TernaryComparisonGroup.tri_eq_mul_inv_mul`
