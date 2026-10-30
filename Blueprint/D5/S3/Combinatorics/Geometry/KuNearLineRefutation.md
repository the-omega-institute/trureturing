# Near-Line Avoidance on the Three-Dimensional Board

## Abstract

Ordinary integer-board line avoidance forces a strict upper bound on maximal saturated density.

**Definition 1.1 (Three coordinate values).**

$$\operatorname{C}\left(\right) = \operatorname{Fin}\left(3\right)$$

*Formalization.* `D5/S3/Combinatorics/Geometry/KuNearLineRefutation.C` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Kuo-Han Ku (2026). *Monochromatic k in a row*. URL: <https://arxiv.org/html/2606.12880v1>.

*Commentary.*

The coordinate labels are zero, one and two.

**Definition 1.2 (Twenty-seven points).**

$$\operatorname{P}\left(\right) = \left(\operatorname{Fin}\left(3\right) \to \operatorname{C}\left(\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Geometry/KuNearLineRefutation.P` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Kuo-Han Ku (2026). *Monochromatic k in a row*. URL: <https://arxiv.org/html/2606.12880v1>.

*Commentary.*

A point has three coordinates, each with three possible values.

**Definition 1.3 (Ordinary integer coordinates).**

$$\forall a \in \operatorname{P}\left(\right),\; \forall i \in \operatorname{Fin}\left(3\right),\; \operatorname{coord}\left(a, i\right) = (\operatorname{val}\left(\operatorname{apply}\left(a, i\right)\right): \mathbb{Z}) + 1$$

*Formalization.* `D5/S3/Combinatorics/Geometry/KuNearLineRefutation.coord` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Kuo-Han Ku (2026). *Monochromatic k in a row*. URL: <https://arxiv.org/html/2606.12880v1>.

*Commentary.*

Adding one identifies coordinate labels with the integers from one through three. Throughout, val is Fin.val, apply is function application, and (n : Z), displayed with the integer symbol, denotes the canonical natural-to-integer cast.

**Definition 1.4 (Full signed ordinary line).**

$$\forall s \in \operatorname{Fin}\left(3\right) \to \operatorname{Int}\left(\right),\; \forall v \in \operatorname{Fin}\left(3\right) \to \operatorname{Int}\left(\right),\; \operatorname{Valid}\left(s, v\right) \Leftrightarrow \left(\left(\exists i \in \operatorname{Fin}\left(3\right),\; \operatorname{apply}\left(v, i\right) \ne 0\right) \land \left(\left(\forall i \in \operatorname{Fin}\left(3\right),\; \operatorname{apply}\left(v, i\right) = -1 \lor \left(\operatorname{apply}\left(v, i\right) = 0 \lor \operatorname{apply}\left(v, i\right) = 1\right)\right) \land \left(\forall t \in \operatorname{Fin}\left(3\right),\; \forall i \in \operatorname{Fin}\left(3\right),\; 1 \le \operatorname{apply}\left(s, i\right) + (\operatorname{val}\left(t\right): \mathbb{Z}) \cdot \operatorname{apply}\left(v, i\right) \land \operatorname{apply}\left(s, i\right) + (\operatorname{val}\left(t\right): \mathbb{Z}) \cdot \operatorname{apply}\left(v, i\right) \le (3: \mathbb{Z})\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Geometry/KuNearLineRefutation.Valid` (`✓ std3`).

*Citation.* Kuo-Han Ku (2026). *Monochromatic k in a row*. URL: <https://arxiv.org/html/2606.12880v1>.

*Commentary.*

A direction is nonzero, each direction coordinate is minus one, zero or one, and all three parameter points stay inside the integer board.

**Definition 1.5 (Incidence).**

$$\forall a \in \operatorname{P}\left(\right),\; \forall s \in \operatorname{Fin}\left(3\right) \to \operatorname{Int}\left(\right),\; \forall v \in \operatorname{Fin}\left(3\right) \to \operatorname{Int}\left(\right),\; \operatorname{On}\left(a, s, v\right) \Leftrightarrow \left(\exists t \in \operatorname{Fin}\left(3\right),\; \forall i \in \operatorname{Fin}\left(3\right),\; \operatorname{coord}\left(a, i\right) = \operatorname{apply}\left(s, i\right) + (\operatorname{val}\left(t\right): \mathbb{Z}) \cdot \operatorname{apply}\left(v, i\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Geometry/KuNearLineRefutation.On` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Kuo-Han Ku (2026). *Monochromatic k in a row*. URL: <https://arxiv.org/html/2606.12880v1>.

*Commentary.*

Incidence uses ordinary integer addition and multiplication at a parameter in Fin 3.

**Definition 1.6 (A common full line).**

$$\forall a \in \operatorname{P}\left(\right),\; \forall b \in \operatorname{P}\left(\right),\; \operatorname{Common}\left(a, b\right) \Leftrightarrow \left(\exists s \in \operatorname{Fin}\left(3\right) \to \operatorname{Int}\left(\right),\; \exists v \in \operatorname{Fin}\left(3\right) \to \operatorname{Int}\left(\right),\; \operatorname{Valid}\left(s, v\right) \land \left(\operatorname{On}\left(a, s, v\right) \land \operatorname{On}\left(b, s, v\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Geometry/KuNearLineRefutation.Common` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Kuo-Han Ku (2026). *Monochromatic k in a row*. URL: <https://arxiv.org/html/2606.12880v1>.

*Commentary.*

Two points are related when a single admissible full line contains both.

**Definition 1.7 (Pairwise line avoidance).**

$$\forall S \in \operatorname{Finset}\left(\operatorname{P}\left(\right)\right),\; \operatorname{Config}\left(S\right) \Leftrightarrow \left(\forall a \in \operatorname{P}\left(\right),\; \forall b \in \operatorname{P}\left(\right),\; a \in S \Rightarrow \left(b \in S \Rightarrow \left(\operatorname{Common}\left(a, b\right) \Rightarrow a = b\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Geometry/KuNearLineRefutation.Config` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Kuo-Han Ku (2026). *Monochromatic k in a row*. URL: <https://arxiv.org/html/2606.12880v1>.

*Commentary.*

A configuration has at most one point on every full three-line.

**Theorem 1.8 (Axis-parallel line).**

$$\forall a \in \operatorname{P}\left(\right),\; \forall b \in \operatorname{P}\left(\right),\; \forall j \in \operatorname{Fin}\left(3\right),\; \left(\forall i \in \operatorname{Fin}\left(3\right),\; i \ne j \Rightarrow \operatorname{apply}\left(a, i\right) = \operatorname{apply}\left(b, i\right)\right) \Rightarrow \operatorname{Common}\left(a, b\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/KuNearLineRefutation.axis_common` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kuo-Han Ku (2026). *Monochromatic k in a row*. URL: <https://arxiv.org/html/2606.12880v1>.

*Commentary.*

Points that agree away from one coordinate lie on a full axis-parallel line.

**Theorem 1.9 (Face-diagonal line).**

$$\forall a \in \operatorname{P}\left(\right),\; \forall b \in \operatorname{P}\left(\right),\; \operatorname{apply}\left(a, 2\right) = \operatorname{apply}\left(b, 2\right) \Rightarrow \left(\left(\left(\operatorname{apply}\left(a, 0\right) = \operatorname{apply}\left(a, 1\right) \land \operatorname{apply}\left(b, 0\right) = \operatorname{apply}\left(b, 1\right)\right) \lor \left(\operatorname{val}\left(\operatorname{apply}\left(a, 0\right)\right) + \operatorname{val}\left(\operatorname{apply}\left(a, 1\right)\right) = 2 \land \operatorname{val}\left(\operatorname{apply}\left(b, 0\right)\right) + \operatorname{val}\left(\operatorname{apply}\left(b, 1\right)\right) = 2\right)\right) \Rightarrow \operatorname{Common}\left(a, b\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/KuNearLineRefutation.diag_common` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kuo-Han Ku (2026). *Monochromatic k in a row*. URL: <https://arxiv.org/html/2606.12880v1>.

*Commentary.*

Equal third coordinates and membership in the same main or opposite face diagonal give an ordinary full line.

**Definition 1.10 (Latin square predicate).**

$$\forall n \in \operatorname{Nat}\left(\right),\; \forall L \in \operatorname{Fin}\left(n\right) \to \left(\operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(n\right)\right),\; \operatorname{Latin}\left(n, L\right) \Leftrightarrow \operatorname{IsLatin}\left(n, L\right)$$

*Formalization.* `D5/S3/Combinatorics/Geometry/KuNearLineRefutation.Latin` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Kuo-Han Ku (2026). *Monochromatic k in a row*. URL: <https://arxiv.org/html/2606.12880v1>.

*Commentary.*

The Latin predicate is the existing row-and-column bijectivity predicate.

**Theorem 1.11 (Order-three diagonal collision).**

$$\forall L \in \operatorname{C}\left(\right) \to \left(\operatorname{C}\left(\right) \to \operatorname{C}\left(\right)\right),\; \operatorname{Latin}\left(3, L\right) \Rightarrow \left(\exists i \in \operatorname{C}\left(\right),\; \exists j \in \operatorname{C}\left(\right),\; i \ne j \land \left(\operatorname{apply}\left(L, i, i\right) = \operatorname{apply}\left(L, j, j\right) \lor \operatorname{apply}\left(L, i, 2 - i\right) = \operatorname{apply}\left(L, j, 2 - j\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/KuNearLineRefutation.latin_diagonal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kuo-Han Ku (2026). *Monochromatic k in a row*. URL: <https://arxiv.org/html/2606.12880v1>.

*Commentary.*

Every Latin square of order three repeats a symbol on at least one of its two diagonals. Subtraction here is in Fin 3; the opposite diagonal is also characterized by the sum of the natural coordinate values being two.

**Theorem 1.12 (Eight-point bound).**

$$\forall S \in \operatorname{Finset}\left(\operatorname{P}\left(\right)\right),\; \operatorname{Config}\left(S\right) \Rightarrow \operatorname{card}\left(S\right) \le 8$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/KuNearLineRefutation.config_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kuo-Han Ku (2026). *Monochromatic k in a row*. URL: <https://arxiv.org/html/2606.12880v1>.

*Commentary.*

Projection to the first two coordinates is injective. Equality at nine points would give a Latin square of order three; its diagonal collision contradicts line avoidance.

**Definition 1.13 (Near-three-line avoidance).**

$$\forall S \in \operatorname{Finset}\left(\operatorname{P}\left(\right)\right),\; \operatorname{SourceConfig}\left(S\right) \Leftrightarrow \left(\forall s \in \operatorname{Fin}\left(3\right) \to \operatorname{Int}\left(\right),\; \forall v \in \operatorname{Fin}\left(3\right) \to \operatorname{Int}\left(\right),\; \operatorname{Valid}\left(s, v\right) \Rightarrow \left(\forall N \in \operatorname{Finset}\left(\operatorname{P}\left(\right)\right),\; \operatorname{card}\left(N\right) = 2 \Rightarrow \left(\left(\forall a \in \operatorname{P}\left(\right),\; a \in N \Rightarrow \operatorname{On}\left(a, s, v\right)\right) \Rightarrow \neg (N \subseteq S)\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Geometry/KuNearLineRefutation.SourceConfig` (`✓ std3`).

*Citation.* Kuo-Han Ku (2026). *Monochromatic k in a row*. URL: <https://arxiv.org/html/2606.12880v1>.

*Commentary.*

No two-element subset of any admissible full three-line can be contained in the configuration.

**Theorem 1.14 (Pairwise and near-line descriptions).**

$$\forall S \in \operatorname{Finset}\left(\operatorname{P}\left(\right)\right),\; \operatorname{SourceConfig}\left(S\right) \Leftrightarrow \operatorname{Config}\left(S\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/KuNearLineRefutation.source_config_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kuo-Han Ku (2026). *Monochromatic k in a row*. URL: <https://arxiv.org/html/2606.12880v1>.

*Commentary.*

The source subset condition is equivalent to pairwise avoidance.

**Definition 1.15 (General ordinary board).**

$$\forall k \in \operatorname{Nat}\left(\right),\; \forall d \in \operatorname{Nat}\left(\right),\; \operatorname{Board}\left(k, d\right) = \left(\operatorname{Fin}\left(d\right) \to \operatorname{Fin}\left(k\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Geometry/KuNearLineRefutation.Board` (`✓ std3`).

*Citation.* Kuo-Han Ku (2026). *Monochromatic k in a row*. URL: <https://arxiv.org/html/2606.12880v1>.

*Commentary.*

The board has d coordinates, each labeled by Fin k and interpreted as integers by adding one. Its cardinality is k raised to d.

**Definition 1.16 (General full signed line).**

$$\forall k \in \operatorname{Nat}\left(\right),\; \forall d \in \operatorname{Nat}\left(\right),\; \forall s \in \operatorname{Fin}\left(d\right) \to \operatorname{Int}\left(\right),\; \forall v \in \operatorname{Fin}\left(d\right) \to \operatorname{Int}\left(\right),\; \operatorname{GValid}\left(k, d, s, v\right) \Leftrightarrow \left(\left(\exists i \in \operatorname{Fin}\left(d\right),\; \operatorname{apply}\left(v, i\right) \ne 0\right) \land \left(\left(\forall i \in \operatorname{Fin}\left(d\right),\; \operatorname{apply}\left(v, i\right) = -1 \lor \left(\operatorname{apply}\left(v, i\right) = 0 \lor \operatorname{apply}\left(v, i\right) = 1\right)\right) \land \left(\forall t \in \operatorname{Fin}\left(k\right),\; \forall i \in \operatorname{Fin}\left(d\right),\; 1 \le \operatorname{apply}\left(s, i\right) + (\operatorname{val}\left(t\right): \mathbb{Z}) \cdot \operatorname{apply}\left(v, i\right) \land \operatorname{apply}\left(s, i\right) + (\operatorname{val}\left(t\right): \mathbb{Z}) \cdot \operatorname{apply}\left(v, i\right) \le (k: \mathbb{Z})\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Geometry/KuNearLineRefutation.GValid` (`✓ std3`).

*Citation.* Kuo-Han Ku (2026). *Monochromatic k in a row*. URL: <https://arxiv.org/html/2606.12880v1>.

*Commentary.*

Every signed nonzero direction and every parameter from zero through k minus one are included.

**Definition 1.17 (General incidence).**

$$\forall k \in \operatorname{Nat}\left(\right),\; \forall d \in \operatorname{Nat}\left(\right),\; \forall a \in \operatorname{Board}\left(k, d\right),\; \forall s \in \operatorname{Fin}\left(d\right) \to \operatorname{Int}\left(\right),\; \forall v \in \operatorname{Fin}\left(d\right) \to \operatorname{Int}\left(\right),\; \operatorname{GOn}\left(a, s, v\right) \Leftrightarrow \left(\exists t \in \operatorname{Fin}\left(k\right),\; \forall i \in \operatorname{Fin}\left(d\right),\; (\operatorname{val}\left(\operatorname{apply}\left(a, i\right)\right): \mathbb{Z}) + 1 = \operatorname{apply}\left(s, i\right) + (\operatorname{val}\left(t\right): \mathbb{Z}) \cdot \operatorname{apply}\left(v, i\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Geometry/KuNearLineRefutation.GOn` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Kuo-Han Ku (2026). *Monochromatic k in a row*. URL: <https://arxiv.org/html/2606.12880v1>.

*Commentary.*

General incidence uses the same ordinary integer coordinate map.

**Definition 1.18 (Intersection cardinality condition).**

$$\forall k \in \operatorname{Nat}\left(\right),\; \forall d \in \operatorname{Nat}\left(\right),\; \forall S \in \operatorname{Finset}\left(\operatorname{Board}\left(k, d\right)\right),\; \operatorname{GConfig}\left(S\right) \Leftrightarrow \left(\forall s \in \operatorname{Fin}\left(d\right) \to \operatorname{Int}\left(\right),\; \forall v \in \operatorname{Fin}\left(d\right) \to \operatorname{Int}\left(\right),\; \operatorname{GValid}\left(k, d, s, v\right) \Rightarrow \operatorname{card}\left(\{a:\operatorname{Board}\left(k, d\right) | a \in S \land \operatorname{GOn}\left(a, s, v\right)\}\right) \le k - 2\right)$$

*Formalization.* `D5/S3/Combinatorics/Geometry/KuNearLineRefutation.GConfig` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Kuo-Han Ku (2026). *Monochromatic k in a row*. URL: <https://arxiv.org/html/2606.12880v1>.

*Commentary.*

Every line contains at most k minus two selected points.

**Definition 1.19 (Near-line subset condition).**

$$\forall k \in \operatorname{Nat}\left(\right),\; \forall d \in \operatorname{Nat}\left(\right),\; \forall S \in \operatorname{Finset}\left(\operatorname{Board}\left(k, d\right)\right),\; \operatorname{GSourceConfig}\left(S\right) \Leftrightarrow \left(\forall s \in \operatorname{Fin}\left(d\right) \to \operatorname{Int}\left(\right),\; \forall v \in \operatorname{Fin}\left(d\right) \to \operatorname{Int}\left(\right),\; \operatorname{GValid}\left(k, d, s, v\right) \Rightarrow \left(\forall N \in \operatorname{Finset}\left(\operatorname{Board}\left(k, d\right)\right),\; \operatorname{card}\left(N\right) = k - 1 \Rightarrow \left(\left(\forall a \in \operatorname{Board}\left(k, d\right),\; a \in N \Rightarrow \operatorname{GOn}\left(a, s, v\right)\right) \Rightarrow \neg (N \subseteq S)\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Geometry/KuNearLineRefutation.GSourceConfig` (`✓ std3`).

*Citation.* Kuo-Han Ku (2026). *Monochromatic k in a row*. URL: <https://arxiv.org/html/2606.12880v1>.

*Commentary.*

No subset of cardinality k minus one lying on a full line is selected in its entirety.

**Theorem 1.20 (General source equivalence).**

$$\forall k \in \operatorname{Nat}\left(\right),\; \forall d \in \operatorname{Nat}\left(\right),\; 2 \le k \Rightarrow \left(\forall S \in \operatorname{Finset}\left(\operatorname{Board}\left(k, d\right)\right),\; \operatorname{GSourceConfig}\left(S\right) \Leftrightarrow \operatorname{GConfig}\left(S\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/KuNearLineRefutation.gsource_config_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kuo-Han Ku (2026). *Monochromatic k in a row*. URL: <https://arxiv.org/html/2606.12880v1>.

*Commentary.*

For k at least two, the forbidden-subset and intersection-cardinality descriptions agree.

**Theorem 1.21 (Three-dimensional specialization).**

$$\forall S \in \operatorname{Finset}\left(\operatorname{P}\left(\right)\right),\; \operatorname{GConfig}\left(S\right) \Leftrightarrow \operatorname{Config}\left(S\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/KuNearLineRefutation.gconfig_33_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kuo-Han Ku (2026). *Monochromatic k in a row*. URL: <https://arxiv.org/html/2606.12880v1>.

*Commentary.*

At k equal to three and dimension three, the general configuration is exactly the pairwise geometric configuration.

**Definition 1.22 (Inclusion maximality).**

$$\forall k \in \operatorname{Nat}\left(\right),\; \forall d \in \operatorname{Nat}\left(\right),\; \forall S \in \operatorname{Finset}\left(\operatorname{Board}\left(k, d\right)\right),\; \operatorname{GSaturated}\left(S\right) \Leftrightarrow \left(\operatorname{GConfig}\left(S\right) \land \left(\forall T \in \operatorname{Finset}\left(\operatorname{Board}\left(k, d\right)\right),\; \operatorname{GConfig}\left(T\right) \Rightarrow \left(S \subseteq T \Rightarrow T = S\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Geometry/KuNearLineRefutation.GSaturated` (`✓ std3`).

*Citation.* Kuo-Han Ku (2026). *Monochromatic k in a row*. URL: <https://arxiv.org/html/2606.12880v1>.

*Commentary.*

A saturated configuration cannot be enlarged while retaining near-line avoidance.

**Theorem 1.23 (A cardinality maximizer exists).**

$$\forall k \in \operatorname{Nat}\left(\right),\; \forall d \in \operatorname{Nat}\left(\right),\; \exists S \in \operatorname{Finset}\left(\operatorname{Board}\left(k, d\right)\right),\; \operatorname{GConfig}\left(S\right) \land \left(\forall T \in \operatorname{Finset}\left(\operatorname{Board}\left(k, d\right)\right),\; \operatorname{GConfig}\left(T\right) \Rightarrow \operatorname{card}\left(T\right) \le \operatorname{card}\left(S\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/KuNearLineRefutation.gexists_opt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kuo-Han Ku (2026). *Monochromatic k in a row*. URL: <https://arxiv.org/html/2606.12880v1>.

*Commentary.*

The finite family of configurations is nonempty because it contains the empty set. A cardinality maximum therefore exists.

**Definition 1.24 (Chosen cardinality maximizer).**

$$\forall k \in \operatorname{Nat}\left(\right),\; \forall d \in \operatorname{Nat}\left(\right),\; \forall h \in \left(\exists S \in \operatorname{Finset}\left(\operatorname{Board}\left(k, d\right)\right),\; \operatorname{GConfig}\left(S\right) \land \left(\forall T \in \operatorname{Finset}\left(\operatorname{Board}\left(k, d\right)\right),\; \operatorname{GConfig}\left(T\right) \Rightarrow \operatorname{card}\left(T\right) \le \operatorname{card}\left(S\right)\right)\right),\; \operatorname{gopt}\left(k, d\right) = Classical.choose\left(h\right)$$

*Formalization.* `D5/S3/Combinatorics/Geometry/KuNearLineRefutation.gopt` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Kuo-Han Ku (2026). *Monochromatic k in a row*. URL: <https://arxiv.org/html/2606.12880v1>.

*Commentary.*

The proof h has exactly the existential type displayed. In the source it is gexists_opt k d; proof irrelevance identifies any proof h of that proposition with this source proof, so Classical.choose h is exactly the defining choice, not a choice applied to a proposition.

**Theorem 1.25 (Maximizer specification).**

$$\forall k \in \operatorname{Nat}\left(\right),\; \forall d \in \operatorname{Nat}\left(\right),\; \operatorname{GConfig}\left(\operatorname{gopt}\left(k, d\right)\right) \land \left(\forall T \in \operatorname{Finset}\left(\operatorname{Board}\left(k, d\right)\right),\; \operatorname{GConfig}\left(T\right) \Rightarrow \operatorname{card}\left(T\right) \le \operatorname{card}\left(\operatorname{gopt}\left(k, d\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/KuNearLineRefutation.gopt_spec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kuo-Han Ku (2026). *Monochromatic k in a row*. URL: <https://arxiv.org/html/2606.12880v1>.

*Commentary.*

The selected set is a configuration and its cardinality dominates every configuration.

**Theorem 1.26 (A maximum is saturated).**

$$\forall k \in \operatorname{Nat}\left(\right),\; \forall d \in \operatorname{Nat}\left(\right),\; \operatorname{GSaturated}\left(\operatorname{gopt}\left(k, d\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/KuNearLineRefutation.gopt_saturated` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kuo-Han Ku (2026). *Monochromatic k in a row*. URL: <https://arxiv.org/html/2606.12880v1>.

*Commentary.*

Any configuration containing the cardinality maximizer has equal cardinality and hence is the same set.

**Definition 1.27 (Maximum density).**

$$\forall k \in \operatorname{Nat}\left(\right),\; \forall d \in \operatorname{Nat}\left(\right),\; \forall h \in \left(\exists S \in \operatorname{Finset}\left(\operatorname{Board}\left(k, d\right)\right),\; \operatorname{GSaturated}\left(S\right) \land \left(\forall T \in \operatorname{Finset}\left(\operatorname{Board}\left(k, d\right)\right),\; \operatorname{GSaturated}\left(T\right) \Rightarrow \operatorname{card}\left(T\right) \le \operatorname{card}\left(S\right)\right)\right),\; \operatorname{density}\left(k, d\right) = \frac{(\operatorname{card}\left(Classical.choose\left(h\right)\right): \mathbb{R})}{(k: \mathbb{R})^{d}}$$

*Formalization.* `D5/S3/Combinatorics/Geometry/KuNearLineRefutation.density` (`✓ std3`).

*Citation.* Kuo-Han Ku (2026). *Monochromatic k in a row*. URL: <https://arxiv.org/html/2606.12880v1>.

*Commentary.*

The proof h has exactly the displayed saturated-maximum existential type; the source uses density_maximum_attained k d. Proof irrelevance makes Classical.choose h the same defining choice. Parenthesized type annotations with the real symbol denote canonical natural-to-real casts. Divide the selected cardinality by k raised to d; for k at least two the denominator is positive, giving exactly the maximum saturated density.

**Theorem 1.28 (Attained saturated maximum).**

$$\forall k \in \operatorname{Nat}\left(\right),\; \forall d \in \operatorname{Nat}\left(\right),\; \exists S \in \operatorname{Finset}\left(\operatorname{Board}\left(k, d\right)\right),\; \operatorname{GSaturated}\left(S\right) \land \left(\forall T \in \operatorname{Finset}\left(\operatorname{Board}\left(k, d\right)\right),\; \operatorname{GSaturated}\left(T\right) \Rightarrow \operatorname{card}\left(T\right) \le \operatorname{card}\left(S\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/KuNearLineRefutation.density_maximum_attained` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kuo-Han Ku (2026). *Monochromatic k in a row*. URL: <https://arxiv.org/html/2606.12880v1>.

*Commentary.*

A saturated configuration has cardinality at least that of every saturated configuration. Choosing from this nonempty finite maximizing family defines the density.

**Theorem 1.29 (Strict density bound).**

$$\operatorname{density}\left(3, 3\right) < \frac{1}{3}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/KuNearLineRefutation.exact_real_event` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kuo-Han Ku (2026). *Monochromatic k in a row*. URL: <https://arxiv.org/html/2606.12880v1>.

*Commentary.*

The saturated maximizer has at most eight points out of twenty-seven, strictly below one third. No exact maximum or prescribed size-eight attainer is asserted.

**Definition 1.30 (Conjecture 5.6).**

$$\operatorname{claim}\left(\right) \Leftrightarrow \left(\forall k \in \operatorname{Nat}\left(\right),\; 2 \le k \Rightarrow \left(\forall d \in \operatorname{Nat}\left(\right),\; \operatorname{density}\left(k, d\right) = 1 - \frac{2}{(k: \mathbb{R})}\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Geometry/KuNearLineRefutation.claim` (`✓ std3`).

*Citation.* Kuo-Han Ku (2026). *Monochromatic k in a row*. URL: <https://arxiv.org/html/2606.12880v1>.

*Commentary.*

The conjecture asserts the same density formula for every k at least two and every natural dimension. The real type annotation denotes the canonical natural-to-real cast. The parameter pair three, three belongs to either convention for natural dimensions.

**Theorem 1.31 (Refutation).**

$$\neg (\operatorname{claim}\left(\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/KuNearLineRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/ku-2026-monochromatic-k-in-a-row-conjecture-5-6` (refuted) by `D5/S3/Combinatorics/Geometry/KuNearLineRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"ku-2026-monochromatic-k-in-a-row-conjecture-5-6","declaration_gid":"D5/S3/Combinatorics/Geometry/KuNearLineRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Kuo-Han Ku (2026). *Monochromatic k in a row*. URL: <https://arxiv.org/html/2606.12880v1>.

*Commentary.*

At k equal to three and dimension three, the asserted equality contradicts the strict bound.

## References

- Truth anchor: `D5/S3/Combinatorics/Geometry/KuNearLineRefutation.Board`
- Truth anchor: `D5/S3/Combinatorics/Geometry/KuNearLineRefutation.C`
- Truth anchor: `D5/S3/Combinatorics/Geometry/KuNearLineRefutation.Common`
- Truth anchor: `D5/S3/Combinatorics/Geometry/KuNearLineRefutation.Config`
- Truth anchor: `D5/S3/Combinatorics/Geometry/KuNearLineRefutation.GConfig`
- Truth anchor: `D5/S3/Combinatorics/Geometry/KuNearLineRefutation.GOn`
- Truth anchor: `D5/S3/Combinatorics/Geometry/KuNearLineRefutation.GSaturated`
- Truth anchor: `D5/S3/Combinatorics/Geometry/KuNearLineRefutation.GSourceConfig`
- Truth anchor: `D5/S3/Combinatorics/Geometry/KuNearLineRefutation.GValid`
- Truth anchor: `D5/S3/Combinatorics/Geometry/KuNearLineRefutation.Latin`
- Truth anchor: `D5/S3/Combinatorics/Geometry/KuNearLineRefutation.On`
- Truth anchor: `D5/S3/Combinatorics/Geometry/KuNearLineRefutation.P`
- Truth anchor: `D5/S3/Combinatorics/Geometry/KuNearLineRefutation.SourceConfig`
- Truth anchor: `D5/S3/Combinatorics/Geometry/KuNearLineRefutation.Valid`
- Truth anchor: `D5/S3/Combinatorics/Geometry/KuNearLineRefutation.axis_common`
- Truth anchor: `D5/S3/Combinatorics/Geometry/KuNearLineRefutation.claim`
- Truth anchor: `D5/S3/Combinatorics/Geometry/KuNearLineRefutation.config_bound`
- Truth anchor: `D5/S3/Combinatorics/Geometry/KuNearLineRefutation.coord`
- Truth anchor: `D5/S3/Combinatorics/Geometry/KuNearLineRefutation.density`
- Truth anchor: `D5/S3/Combinatorics/Geometry/KuNearLineRefutation.density_maximum_attained`
- Truth anchor: `D5/S3/Combinatorics/Geometry/KuNearLineRefutation.diag_common`
- Truth anchor: `D5/S3/Combinatorics/Geometry/KuNearLineRefutation.exact_real_event`
- Truth anchor: `D5/S3/Combinatorics/Geometry/KuNearLineRefutation.gconfig_33_iff`
- Truth anchor: `D5/S3/Combinatorics/Geometry/KuNearLineRefutation.gexists_opt`
- Truth anchor: `D5/S3/Combinatorics/Geometry/KuNearLineRefutation.gopt`
- Truth anchor: `D5/S3/Combinatorics/Geometry/KuNearLineRefutation.gopt_saturated`
- Truth anchor: `D5/S3/Combinatorics/Geometry/KuNearLineRefutation.gopt_spec`
- Truth anchor: `D5/S3/Combinatorics/Geometry/KuNearLineRefutation.gsource_config_iff`
- Truth anchor: `D5/S3/Combinatorics/Geometry/KuNearLineRefutation.latin_diagonal`
- Truth anchor: `D5/S3/Combinatorics/Geometry/KuNearLineRefutation.result`
- Truth anchor: `D5/S3/Combinatorics/Geometry/KuNearLineRefutation.source_config_iff`
- Dependency: [D5/S3/Combinatorics/LatinEulerianDefs](../LatinEulerianDefs.md)
