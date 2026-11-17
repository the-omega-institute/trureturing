# The largest-order-prime commuting question

## Abstract

A dihedral product has fixed-element pi-commuting fraction one quarter despite a large prime in the element order.

**Definition 1.1 (Elements with prime support in pi).**

$$\forall G \in Type*,\; [Group\left(G\right)] [Finite\left(G\right)], \forall (\pi : Set\left(\mathbb{N}\right)), piElements\left(G, \pi\right) = \{x : G | \forall p \in \mathbb{N},\; \operatorname{Nat}.\operatorname{Prime}\left(p\right) \Rightarrow \left(p \mid orderOf\left(x\right) \Rightarrow p \in \pi\right)\}$$

*Formalization.* `D5/S3/FiniteGroups/Frobenius/MartinezLargestOrderPrimeCommutingRefutation.piElements` (`✓ std3`).

*Citation.* Juan Martínez (2024). *On the commuting probability of π-elements in finite groups*. DOI: [10.1002/mana.202300338](https://doi.org/10.1002/mana.202300338). URL: <https://arxiv.org/abs/2307.09868v3>.

*Commentary.*

Introduction, printed pages 1–2: “where G_π is the set of all π-elements in G.” An element belongs to this set when every prime divisor of its order belongs to pi. The identity is included because its order is one. Type* allows an arbitrary carrier universe.

**Definition 1.2 (Subgroups with prime support in pi).**

$$\forall G \in Type*,\; [Group\left(G\right)] [Finite\left(G\right)], \forall (\pi : Set\left(\mathbb{N}\right)), \forall N \in Subgroup\left(G\right),\; isPiSubgroup\left(\pi, N\right) = \left(\forall p \in \mathbb{N},\; \operatorname{Nat}.\operatorname{Prime}\left(p\right) \Rightarrow \left(p \mid \operatorname{Nat}.\operatorname{card}\left(N\right) \Rightarrow p \in \pi\right)\right)$$

*Formalization.* `D5/S3/FiniteGroups/Frobenius/MartinezLargestOrderPrimeCommutingRefutation.isPiSubgroup` (`✓ std3`).

*Citation.* Juan Martínez (2024). *On the commuting probability of π-elements in finite groups*. DOI: [10.1002/mana.202300338](https://doi.org/10.1002/mana.202300338). URL: <https://arxiv.org/abs/2307.09868v3>.

*Commentary.*

A pi-subgroup has no prime divisor of its cardinality outside pi. This is the standard finite-group meaning of the pi-subgroups used in Oπ(G); the source does not separately define this term.

**Definition 1.3 (The normal pi-core).**

$$\forall G \in Type*,\; [Group\left(G\right)] [Finite\left(G\right)], \forall (\pi : Set\left(\mathbb{N}\right)), piCore\left(G, \pi\right) = sSup\left(\{N : Subgroup\left(G\right) | \operatorname{Subgroup}.\operatorname{Normal}\left(N\right) \land isPiSubgroup\left(\pi, N\right)\}\right)$$

*Formalization.* `D5/S3/FiniteGroups/Frobenius/MartinezLargestOrderPrimeCommutingRefutation.piCore` (`✓ std3`).

*Citation.* Juan Martínez (2024). *On the commuting probability of π-elements in finite groups*. DOI: [10.1002/mana.202300338](https://doi.org/10.1002/mana.202300338). URL: <https://arxiv.org/abs/2307.09868v3>.

*Commentary.*

The normal pi-core Oπ(G) is represented as the supremum, in the complete lattice of subgroups, of the normal pi-subgroups. The family includes the trivial subgroup. The source uses the standard normal pi-core in Theorem A on printed page 2.

**Definition 1.4 (The fixed-element fraction).**

$$\forall G \in Type*,\; [Group\left(G\right)] [Finite\left(G\right)], \forall (\pi : Set\left(\mathbb{N}\right)), \forall x \in G,\; commutingFraction\left(G, \pi, x\right) = \frac{(\operatorname{Nat}.\operatorname{card}\left(\{y : G // y \in piElements\left(G, \pi\right) \land y \in \operatorname{Subgroup}.\operatorname{centralizer}\left((\{x\} : Set\left(G\right))\right)\}\right) : \mathbb{Q})}{(\operatorname{Nat}.\operatorname{card}\left(\{y : G // y \in piElements\left(G, \pi\right)\}\right) : \mathbb{Q})}$$

*Formalization.* `D5/S3/FiniteGroups/Frobenius/MartinezLargestOrderPrimeCommutingRefutation.commutingFraction` (`✓ std3`).

*Citation.* Juan Martínez (2024). *On the commuting probability of π-elements in finite groups*. DOI: [10.1002/mana.202300338](https://doi.org/10.1002/mana.202300338). URL: <https://arxiv.org/abs/2307.09868v3>.

*Commentary.*

Section 2, printed page 4: “It is important to remark that given x, a π-element of G, the proportion |C_G(x)_π|/|G_π| is exactly the fixed point ratio of x, where we consider the action of G on G_π by conjugation.” The numerator counts pi-elements in the singleton centralizer. Both finite cardinalities are cast to the rationals before division. The denominator includes the identity and is positive.

**Definition 1.5 (The source's largest-prime question).**

$$claim = (\forall G \in Type,\; [Group\left(G\right)] [Finite\left(G\right)], \forall (\pi : Set\left(\mathbb{N}\right)), \left(\forall p \in \mathbb{N},\; p \in \pi \Rightarrow \operatorname{Nat}.\operatorname{Prime}\left(p\right)\right) \Rightarrow \left(\operatorname{Set}.\operatorname{Nonempty}\left(\pi\right) \Rightarrow \left(\forall x \in G,\; x \in piElements\left(G, \pi\right) \Rightarrow \left(\neg (x \in piCore\left(G, \pi\right)) \Rightarrow \left(\exists q \in \mathbb{N},\; \operatorname{Nat}.\operatorname{Prime}\left(q\right) \land \left(q \mid orderOf\left(x\right) \land \left(\left(\forall p \in \mathbb{N},\; \operatorname{Nat}.\operatorname{Prime}\left(p\right) \Rightarrow \left(p \mid orderOf\left(x\right) \Rightarrow p \le q\right)\right) \land commutingFraction\left(G, \pi, x\right) \le \frac{1}{(q : \mathbb{Q})}\right)\right)\right)\right)\right)\right))$$

*Formalization.* `D5/S3/FiniteGroups/Frobenius/MartinezLargestOrderPrimeCommutingRefutation.claim` (`✓ std3`).

*Citation.* Juan Martínez (2024). *On the commuting probability of π-elements in finite groups*. DOI: [10.1002/mana.202300338](https://doi.org/10.1002/mana.202300338). URL: <https://arxiv.org/abs/2307.09868v3>.

*Commentary.*

Section 4, printed page 16, immediately after Theorem 4.7: “As we mentioned in the Introduction, it remains as an open question whether Theorem A holds with ≤ 1/q, where q is the largest prime dividing o(x).” Theorem A, printed page 2: “Let G be a finite group, let π be a set of primes and let p be the smallest prime in π. If x ∈ G_π∖O_π(G), then |C_G(x)_π|/|G_π| ≤ 1/p.” The proposition replaces that last bound by the reciprocal of the largest prime divisor of orderOf x. It quantifies over actual finite groups with carrier G : Type and arbitrary nonempty sets pi of primes. Existence of the largest prime divisor is included in the conclusion.

**Theorem 1.6 (Refutation by a dihedral product).**

$$\neg (\forall G \in Type,\; [Group\left(G\right)] [Finite\left(G\right)], \forall (\pi : Set\left(\mathbb{N}\right)), \left(\forall p \in \mathbb{N},\; p \in \pi \Rightarrow \operatorname{Nat}.\operatorname{Prime}\left(p\right)\right) \Rightarrow \left(\operatorname{Set}.\operatorname{Nonempty}\left(\pi\right) \Rightarrow \left(\forall x \in G,\; x \in piElements\left(G, \pi\right) \Rightarrow \left(\neg (x \in piCore\left(G, \pi\right)) \Rightarrow \left(\exists q \in \mathbb{N},\; \operatorname{Nat}.\operatorname{Prime}\left(q\right) \land \left(q \mid orderOf\left(x\right) \land \left(\left(\forall p \in \mathbb{N},\; \operatorname{Nat}.\operatorname{Prime}\left(p\right) \Rightarrow \left(p \mid orderOf\left(x\right) \Rightarrow p \le q\right)\right) \land commutingFraction\left(G, \pi, x\right) \le \frac{1}{(q : \mathbb{Q})}\right)\right)\right)\right)\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/Frobenius/MartinezLargestOrderPrimeCommutingRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/op-martinez2307` (refuted) by `D5/S3/FiniteGroups/Frobenius/MartinezLargestOrderPrimeCommutingRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"op-martinez2307","declaration_gid":"D5/S3/FiniteGroups/Frobenius/MartinezLargestOrderPrimeCommutingRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Juan Martínez (2024). *On the commuting probability of π-elements in finite groups*. DOI: [10.1002/mana.202300338](https://doi.org/10.1002/mana.202300338). URL: <https://arxiv.org/abs/2307.09868v3>.

*Commentary.*

Take G = DihedralGroup 3 × DihedralGroup 5, pi = {2,5}, and x = (DihedralGroup.sr 0, DihedralGroup.r 1). The element has order ten and lies outside the normal pi-core. There are forty pi-elements and ten centralizing pi-elements, so the fraction is one quarter, strictly greater than one fifth. The largest prime divisor of ten is five.

More generally, for every prime q ≥ 5, the same construction in DihedralGroup 3 × DihedralGroup q has pi-core 1 × DihedralGroup q, pi-element count 8q and centralizing pi-element count 2q. The first-coordinate reflection keeps x outside the pi-core while its second coordinate contributes q to its order. The fraction remains one quarter. The source's smallest-prime bound in Theorem A is not refuted; the separate smallest-prime-dividing-order question and the restricted Theorem B are not proved here.

## References

- Truth anchor: `D5/S3/FiniteGroups/Frobenius/MartinezLargestOrderPrimeCommutingRefutation.claim`
- Truth anchor: `D5/S3/FiniteGroups/Frobenius/MartinezLargestOrderPrimeCommutingRefutation.commutingFraction`
- Truth anchor: `D5/S3/FiniteGroups/Frobenius/MartinezLargestOrderPrimeCommutingRefutation.isPiSubgroup`
- Truth anchor: `D5/S3/FiniteGroups/Frobenius/MartinezLargestOrderPrimeCommutingRefutation.piCore`
- Truth anchor: `D5/S3/FiniteGroups/Frobenius/MartinezLargestOrderPrimeCommutingRefutation.piElements`
- Truth anchor: `D5/S3/FiniteGroups/Frobenius/MartinezLargestOrderPrimeCommutingRefutation.result`
