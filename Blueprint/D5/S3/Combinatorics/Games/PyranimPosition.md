# Stable positions and legal options in Pyranim

## Abstract

Stable positions and legal options in Pyranim

**Definition 1.1 (Nonempty intervals).**

$$\forall n \in \mathbb{N},\; (\operatorname{Equiv}\left(\operatorname{Interval}\left(n\right), \{p:\mathbb{N}\times \mathbb{N}\mid (1 \le p.1) \land ((p.1 \le p.2) \land (p.2 \le n))\}\right)) \land (\forall c \in \operatorname{Interval}\left(n\right),\; \forall u \in \operatorname{Interval}\left(n\right),\; (c \le u) \Leftrightarrow ((u.left \le c.left) \land (c.right \le u.right)))$$

*Formalization.* `D5/S3/Combinatorics/Games/PyranimPosition.Interval` (`✓ std3`).

*Citation.* Yoav Binyamin, Evan Kniffen (2026). *Enumerating Pyranim Isomorphisms*. URL: <https://arxiv.org/abs/2611.16153v1>.

*Commentary.*

The nonempty chips of width n have endpoints l and r with 1 ≤ l ≤ r ≤ n. Their order is interval inclusion.

**Definition 1.2 (All stable positions).**

$$\forall n \in \mathbb{N},\; \operatorname{Stable}\left(n\right) = \{S:\operatorname{Set}\left(\operatorname{Interval}\left(n\right)\right)\mid \operatorname{IsLowerSet}\left(S\right)\}$$

*Formalization.* `D5/S3/Combinatorics/Games/PyranimPosition.Stable` (`✓ std3`).

*Citation.* Yoav Binyamin, Evan Kniffen (2026). *Enumerating Pyranim Isomorphisms*. URL: <https://arxiv.org/abs/2611.16153v1>.

*Commentary.*

A position contains every subinterval of each surviving chip. The board may have absent bottom chips, including the empty board.

**Definition 1.3 (Empty position).**

$$\forall n \in \mathbb{N},\; \operatorname{emptyStable}\left(n\right).val = \emptyset$$

*Formalization.* `D5/S3/Combinatorics/Games/PyranimPosition.emptyStable` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Yoav Binyamin, Evan Kniffen (2026). *Enumerating Pyranim Isomorphisms*. URL: <https://arxiv.org/abs/2611.16153v1>.

*Commentary.*

No chip survives in the empty stable position.

**Definition 1.4 (Stable positions and Dyck words).**

$$\forall n \in \mathbb{N},\; \operatorname{stableEquivDyck}\left(n\right):\operatorname{Equiv}\left(\operatorname{Stable}\left(n\right), \{w:DyckWord\mid w.semilength = n + 1\}\right)$$

*Formalization.* `D5/S3/Combinatorics/Games/PyranimPosition.stableEquivDyck` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Yoav Binyamin, Evan Kniffen (2026). *Enumerating Pyranim Isomorphisms*. URL: <https://arxiv.org/abs/2611.16153v1>.

*Commentary.*

The maximal omitted start in each column gives a bounded nondecreasing inversion sequence. The inverse keeps intervals whose start exceeds that threshold. The frozen inversion-sequence equivalence gives the Dyck word.

**Theorem 1.5 (Catalan count).**

$$\forall n \in \mathbb{N},\; \operatorname{Nat}.\operatorname{card}\left(\operatorname{Stable}\left(n\right)\right) = \operatorname{catalan}\left(n + 1\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Games/PyranimPosition.stableCard` (`✓ std3`). ∎

*Citation.* Yoav Binyamin, Evan Kniffen (2026). *Enumerating Pyranim Isomorphisms*. URL: <https://arxiv.org/abs/2611.16153v1>.

*Commentary.*

The Catalan count uses Dyck semilength n+1, including width zero.

**Definition 1.6 (Full bottom row).**

$$\forall n \in \mathbb{N},\; \operatorname{FullBottom}\left(n\right) = \{I:\operatorname{Stable}\left(n\right)\mid \forall c \in \operatorname{Interval}\left(n\right),\; (c.left = c.right) \Rightarrow (c \in I.val)\}$$

*Formalization.* `D5/S3/Combinatorics/Games/PyranimPosition.FullBottom` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Yoav Binyamin, Evan Kniffen (2026). *Enumerating Pyranim Isomorphisms*. URL: <https://arxiv.org/abs/2611.16153v1>.

*Commentary.*

Every singleton interval belongs to a full-bottom position.

**Definition 1.7 (Lengthening the right endpoint).**

$$\forall n \in \mathbb{N},\; \forall c \in \operatorname{Interval}\left(n\right),\; (\operatorname{raiseRight}\left(c\right).left = c.left) \land (\operatorname{raiseRight}\left(c\right).right = c.right + 1)$$

*Formalization.* `D5/S3/Combinatorics/Games/PyranimPosition.raiseRight` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Yoav Binyamin, Evan Kniffen (2026). *Enumerating Pyranim Isomorphisms*. URL: <https://arxiv.org/abs/2611.16153v1>.

*Commentary.*

The width and the right endpoint increase by one.

**Definition 1.8 (Shortening a nonsingleton).**

$$\forall n \in \mathbb{N},\; \forall c \in \operatorname{Interval}\left(n + 1\right),\; \forall (h:c.left < c.right), (\operatorname{lowerRight}\left(c, h\right).left = c.left) \land (\operatorname{lowerRight}\left(c, h\right).right = c.right - 1)$$

*Formalization.* `D5/S3/Combinatorics/Games/PyranimPosition.lowerRight` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Yoav Binyamin, Evan Kniffen (2026). *Enumerating Pyranim Isomorphisms*. URL: <https://arxiv.org/abs/2611.16153v1>.

*Commentary.*

The width and the right endpoint decrease by one. The strict endpoint inequality supplies the proof h that shortening leaves a nonempty interval.

**Lemma 1.9 (Recovering a nonsingleton).**

$$\forall n \in \mathbb{N},\; \forall c \in \operatorname{Interval}\left(n + 1\right),\; \forall (h:c.left < c.right), \operatorname{raiseRight}\left(\operatorname{lowerRight}\left(c, h\right)\right) = c$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Games/PyranimPosition.raiseRight_lowerRight` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Yoav Binyamin, Evan Kniffen (2026). *Enumerating Pyranim Isomorphisms*. URL: <https://arxiv.org/abs/2611.16153v1>.

*Commentary.*

Lengthening recovers the original nonsingleton.

**Definition 1.10 (Removing the full bottom row).**

$$\forall n \in \mathbb{N},\; \forall I \in \operatorname{FullBottom}\left(n + 1\right),\; \operatorname{removeBottom}\left(I\right).val = \{c:\operatorname{Interval}\left(n\right)\mid \operatorname{raiseRight}\left(c\right) \in I.val.val\}$$

*Formalization.* `D5/S3/Combinatorics/Games/PyranimPosition.removeBottom` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Yoav Binyamin, Evan Kniffen (2026). *Enumerating Pyranim Isomorphisms*. URL: <https://arxiv.org/abs/2611.16153v1>.

*Commentary.*

The surviving chips have right endpoints shifted down by one.

**Definition 1.11 (Full-bottom positions as smaller boards).**

$$\forall n \in \mathbb{N},\; \operatorname{fullBottomSuccEquiv}\left(n\right):\operatorname{Equiv}\left(\operatorname{FullBottom}\left(n + 1\right), \operatorname{Stable}\left(n\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Games/PyranimPosition.fullBottomSuccEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Yoav Binyamin, Evan Kniffen (2026). *Enumerating Pyranim Isomorphisms*. URL: <https://arxiv.org/abs/2611.16153v1>.

*Commentary.*

Deleting the bottom row and reinstating it give inverse maps.

**Definition 1.12 (Largest stable subposition).**

$$\forall n \in \mathbb{N},\; \forall S \in \operatorname{Set}\left(\operatorname{Interval}\left(n\right)\right),\; \operatorname{stabilize}\left(S\right).val = \{b:\operatorname{Interval}\left(n\right)\mid \forall a \in \operatorname{Interval}\left(n\right),\; (a \le b) \Rightarrow (a \in S)\}$$

*Formalization.* `D5/S3/Combinatorics/Games/PyranimPosition.stabilize` (`✓ std3`).

*Citation.* Yoav Binyamin, Evan Kniffen (2026). *Enumerating Pyranim Isomorphisms*. URL: <https://arxiv.org/abs/2611.16153v1>.

*Commentary.*

A surviving chip remains stable exactly when all its subintervals are in the supplied set.

**Definition 1.13 (Chip removal and cascade).**

$$\forall n \in \mathbb{N},\; \forall I \in \operatorname{Stable}\left(n\right),\; \forall c \in \operatorname{Interval}\left(n\right),\; \operatorname{removeChip}\left(I, c\right).val = \{b:\operatorname{Interval}\left(n\right)\mid (b \in I.val) \land (\neg (c \le b))\}$$

*Formalization.* `D5/S3/Combinatorics/Games/PyranimPosition.removeChip` (`✓ std3`).

*Citation.* Yoav Binyamin, Evan Kniffen (2026). *Enumerating Pyranim Isomorphisms*. URL: <https://arxiv.org/abs/2611.16153v1>.

*Commentary.*

Remove the selected chip and every surviving superinterval that it supports.

**Lemma 1.14 (Cascade agrees with stabilization).**

$$\forall n \in \mathbb{N},\; \forall I \in \operatorname{Stable}\left(n\right),\; \forall c \in \operatorname{Interval}\left(n\right),\; \operatorname{removeChip}\left(I, c\right) = \operatorname{stabilize}\left(I.val\setminus \{z:\operatorname{Interval}\left(n\right)\mid z = c\}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Games/PyranimPosition.removeChip_eq_stabilize` (`✓ std3`). ∎

*Citation.* Yoav Binyamin, Evan Kniffen (2026). *Enumerating Pyranim Isomorphisms*. URL: <https://arxiv.org/abs/2611.16153v1>.

*Commentary.*

The ideal obtained by removing all superintervals is the largest ideal after deleting the selected chip.

**Definition 1.15 (Immediate upper left chip).**

$$\forall n \in \mathbb{N},\; \forall c \in \operatorname{Interval}\left(n\right),\; \forall u \in \operatorname{Interval}\left(n\right),\; (\operatorname{LeftAbove}\left(c, u\right)) \Leftrightarrow ((u.left + 1 = c.left) \land (u.right = c.right))$$

*Formalization.* `D5/S3/Combinatorics/Games/PyranimPosition.LeftAbove` (`✓ std3`).

*Citation.* Yoav Binyamin, Evan Kniffen (2026). *Enumerating Pyranim Isomorphisms*. URL: <https://arxiv.org/abs/2611.16153v1>.

*Commentary.*

The immediate upper left chip extends the left endpoint by one.

**Definition 1.16 (Immediate upper right chip).**

$$\forall n \in \mathbb{N},\; \forall c \in \operatorname{Interval}\left(n\right),\; \forall u \in \operatorname{Interval}\left(n\right),\; (\operatorname{RightAbove}\left(c, u\right)) \Leftrightarrow ((u.left = c.left) \land (c.right + 1 = u.right))$$

*Formalization.* `D5/S3/Combinatorics/Games/PyranimPosition.RightAbove` (`✓ std3`).

*Citation.* Yoav Binyamin, Evan Kniffen (2026). *Enumerating Pyranim Isomorphisms*. URL: <https://arxiv.org/abs/2611.16153v1>.

*Commentary.*

The immediate upper right chip extends the right endpoint by one.

**Definition 1.17 (Immediate support step).**

$$\forall n \in \mathbb{N},\; \forall c \in \operatorname{Interval}\left(n\right),\; \forall u \in \operatorname{Interval}\left(n\right),\; (\operatorname{ImmediateAbove}\left(c, u\right)) \Leftrightarrow ((\operatorname{LeftAbove}\left(c, u\right)) \lor (\operatorname{RightAbove}\left(c, u\right)))$$

*Formalization.* `D5/S3/Combinatorics/Games/PyranimPosition.ImmediateAbove` (`✓ std3`).

*Citation.* Yoav Binyamin, Evan Kniffen (2026). *Enumerating Pyranim Isomorphisms*. URL: <https://arxiv.org/abs/2611.16153v1>.

*Commentary.*

A support step extends exactly one endpoint to its immediate neighbor.

**Lemma 1.18 (Cascade along support paths).**

$$\forall n \in \mathbb{N},\; \forall I \in \operatorname{Stable}\left(n\right),\; \forall c \in \operatorname{Interval}\left(n\right),\; \forall u \in \operatorname{Interval}\left(n\right),\; (u \in \operatorname{removeChip}\left(I, c\right).val) \Leftrightarrow ((u \in I.val) \land (\neg (\operatorname{ReflTransGen}\left(ImmediateAbove, c, u\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Games/PyranimPosition.cascade_iff` (`✓ std3`). ∎

*Citation.* Yoav Binyamin, Evan Kniffen (2026). *Enumerating Pyranim Isomorphisms*. URL: <https://arxiv.org/abs/2611.16153v1>.

*Commentary.*

A reflexive support path includes the selected chip itself. Transitive support is equivalent to interval containment.

**Definition 1.19 (Visible surviving chip).**

$$\forall n \in \mathbb{N},\; \forall I \in \operatorname{Stable}\left(n\right),\; \forall c \in \operatorname{Interval}\left(n\right),\; (\operatorname{Visible}\left(I, c\right)) \Leftrightarrow ((c \in I.val) \land (\neg ((\exists u \in \operatorname{Interval}\left(n\right),\; (u \in I.val) \land (\operatorname{LeftAbove}\left(c, u\right))) \land (\exists u \in \operatorname{Interval}\left(n\right),\; (u \in I.val) \land (\operatorname{RightAbove}\left(c, u\right))))))$$

*Formalization.* `D5/S3/Combinatorics/Games/PyranimPosition.Visible` (`✓ std3`).

*Citation.* Yoav Binyamin, Evan Kniffen (2026). *Enumerating Pyranim Isomorphisms*. URL: <https://arxiv.org/abs/2611.16153v1>.

*Commentary.*

A surviving chip is legal to select when its two immediate upper neighbors are not both present.

**Definition 1.20 (Cover within the surviving position).**

$$\forall n \in \mathbb{N},\; \forall I \in \operatorname{Stable}\left(n\right),\; \forall c \in \operatorname{Interval}\left(n\right),\; \forall u \in \operatorname{Interval}\left(n\right),\; (\operatorname{UpperCover}\left(I, c, u\right)) \Leftrightarrow ((u \in I.val) \land ((c < u) \land (\forall v \in \operatorname{Interval}\left(n\right),\; (v \in I.val) \Rightarrow ((c < v) \Rightarrow ((v < u) \Rightarrow (False))))))$$

*Formalization.* `D5/S3/Combinatorics/Games/PyranimPosition.UpperCover` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Yoav Binyamin, Evan Kniffen (2026). *Enumerating Pyranim Isomorphisms*. URL: <https://arxiv.org/abs/2611.16153v1>.

*Commentary.*

A cover is a surviving strict superinterval with no surviving chip strictly between the two.

**Lemma 1.21 (Visibility from order covers).**

$$\forall n \in \mathbb{N},\; \forall I \in \operatorname{Stable}\left(n\right),\; \forall c \in \operatorname{Interval}\left(n\right),\; (\operatorname{Visible}\left(I, c\right)) \Leftrightarrow ((c \in I.val) \land (\neg (\exists u \in \operatorname{Interval}\left(n\right),\; \exists v \in \operatorname{Interval}\left(n\right),\; (\operatorname{UpperCover}\left(I, c, u\right)) \land ((\operatorname{UpperCover}\left(I, c, v\right)) \land (u\neq v)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Games/PyranimPosition.visible_iff_covers` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Yoav Binyamin, Evan Kniffen (2026). *Enumerating Pyranim Isomorphisms*. URL: <https://arxiv.org/abs/2611.16153v1>.

*Commentary.*

The only possible covers extend one endpoint by one. Visibility is therefore preserved by a survivor-poset order isomorphism.

**Definition 1.22 (Legal successor position).**

$$\forall n \in \mathbb{N},\; \forall I \in \operatorname{Stable}\left(n\right),\; \forall J \in \operatorname{Stable}\left(n\right),\; (\operatorname{LegalOption}\left(I, J\right)) \Leftrightarrow (\exists c \in \operatorname{Interval}\left(n\right),\; (\operatorname{Visible}\left(I, c\right)) \land (J = \operatorname{removeChip}\left(I, c\right)))$$

*Formalization.* `D5/S3/Combinatorics/Games/PyranimPosition.LegalOption` (`✓ std3`).

*Citation.* Yoav Binyamin, Evan Kniffen (2026). *Enumerating Pyranim Isomorphisms*. URL: <https://arxiv.org/abs/2611.16153v1>.

*Commentary.*

The option set consists of resulting stable positions reached by selecting a visible chip and applying the cascade.

**Definition 1.23 (Subtype of actual legal options).**

$$\forall n \in \mathbb{N},\; \forall I \in \operatorname{Stable}\left(n\right),\; \operatorname{Options}\left(I\right) = \{J:\operatorname{Stable}\left(n\right)\mid \operatorname{LegalOption}\left(I, J\right)\}$$

*Formalization.* `D5/S3/Combinatorics/Games/PyranimPosition.Options` (`✓ std3`).

*Citation.* Yoav Binyamin, Evan Kniffen (2026). *Enumerating Pyranim Isomorphisms*. URL: <https://arxiv.org/abs/2611.16153v1>.

*Commentary.*

Each option is a stable position together with its legal-move property.

**Lemma 1.24 (A move strictly reduces the position).**

$$\forall n \in \mathbb{N},\; \forall I \in \operatorname{Stable}\left(n\right),\; \forall J \in \operatorname{Stable}\left(n\right),\; (\operatorname{LegalOption}\left(I, J\right)) \Rightarrow (J.val\subset I.val)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Games/PyranimPosition.legalOption_ssubset` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Yoav Binyamin, Evan Kniffen (2026). *Enumerating Pyranim Isomorphisms*. URL: <https://arxiv.org/abs/2611.16153v1>.

*Commentary.*

The chip selected by a legal move witnesses strict inclusion of the surviving set.

**Definition 1.25 (Surviving chips).**

$$\forall n \in \mathbb{N},\; \forall I \in \operatorname{Stable}\left(n\right),\; \operatorname{chipCount}\left(I\right) = \operatorname{Finset}.\operatorname{card}\left(\operatorname{toFinset}\left(I.val\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Games/PyranimPosition.chipCount` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Yoav Binyamin, Evan Kniffen (2026). *Enumerating Pyranim Isomorphisms*. URL: <https://arxiv.org/abs/2611.16153v1>.

*Commentary.*

The cardinality is finite because each chip has two bounded endpoints.

**Lemma 1.26 (Legal options lower chip count).**

$$\forall n \in \mathbb{N},\; \forall I \in \operatorname{Stable}\left(n\right),\; \forall J \in \operatorname{Stable}\left(n\right),\; (\operatorname{LegalOption}\left(I, J\right)) \Rightarrow (\operatorname{chipCount}\left(J\right) < \operatorname{chipCount}\left(I\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Games/PyranimPosition.chipCount_lt_of_option` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Yoav Binyamin, Evan Kniffen (2026). *Enumerating Pyranim Isomorphisms*. URL: <https://arxiv.org/abs/2611.16153v1>.

*Commentary.*

The strict inclusion of finite surviving sets gives the decrease.

**Lemma 1.27 (Well-founded legal descent).**

$$\forall n \in \mathbb{N},\; \operatorname{WellFounded}\left(\lambda (J:\operatorname{Stable}\left(n\right)) (I:\operatorname{Stable}\left(n\right))\mapsto\operatorname{LegalOption}\left(I, J\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Games/PyranimPosition.legalOption_wellFounded` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Yoav Binyamin, Evan Kniffen (2026). *Enumerating Pyranim Isomorphisms*. URL: <https://arxiv.org/abs/2611.16153v1>.

*Commentary.*

Chip count is a natural-number measure for legal descent.

**Definition 1.28 (Recursive game isomorphism).**

$$\forall n \in \mathbb{N},\; \forall m \in \mathbb{N},\; \forall I \in \operatorname{Stable}\left(n\right),\; \forall J \in \operatorname{Stable}\left(m\right),\; (\operatorname{GameIso}\left(I, J\right)) \Leftrightarrow (\exists e \in \operatorname{Equiv}\left(\operatorname{Options}\left(I\right), \operatorname{Options}\left(J\right)\right),\; \forall a \in \operatorname{Options}\left(I\right),\; \operatorname{GameIso}\left(a.val, e\left(a\right).val\right))$$

*Formalization.* `D5/S3/Combinatorics/Games/PyranimPosition.GameIso` (`✓ std3`).

*Citation.* Yoav Binyamin, Evan Kniffen (2026). *Enumerating Pyranim Isomorphisms*. URL: <https://arxiv.org/abs/2611.16153v1>.

*Commentary.*

At every pair of positions there must be a bijection of actual legal options whose matched positions are again game isomorphic. The first board’s chip count decreases in the recursion.

**Lemma 1.29 (Recursive equation for game isomorphism).**

$$\forall n \in \mathbb{N},\; \forall m \in \mathbb{N},\; \forall I \in \operatorname{Stable}\left(n\right),\; \forall J \in \operatorname{Stable}\left(m\right),\; (\operatorname{GameIso}\left(I, J\right)) \Leftrightarrow (\exists e \in \operatorname{Equiv}\left(\operatorname{Options}\left(I\right), \operatorname{Options}\left(J\right)\right),\; \forall a \in \operatorname{Options}\left(I\right),\; \operatorname{GameIso}\left(a.val, e\left(a\right).val\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Games/PyranimPosition.gameIso_iff` (`✓ std3`). ∎

*Citation.* Yoav Binyamin, Evan Kniffen (2026). *Enumerating Pyranim Isomorphisms*. URL: <https://arxiv.org/abs/2611.16153v1>.

*Commentary.*

Unfolding the recursion gives the option-bijection criterion at all widths.

**Lemma 1.30 (Reflexive game isomorphism).**

$$\forall n \in \mathbb{N},\; \forall I \in \operatorname{Stable}\left(n\right),\; \operatorname{GameIso}\left(I, I\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Games/PyranimPosition.gameIso_refl` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Yoav Binyamin, Evan Kniffen (2026). *Enumerating Pyranim Isomorphisms*. URL: <https://arxiv.org/abs/2611.16153v1>.

*Commentary.*

The identity bijection works at each pair of identical positions by well-founded induction.

**Lemma 1.31 (Symmetric game isomorphism).**

$$\forall n \in \mathbb{N},\; \forall m \in \mathbb{N},\; \forall I \in \operatorname{Stable}\left(n\right),\; \forall J \in \operatorname{Stable}\left(m\right),\; (\operatorname{GameIso}\left(I, J\right)) \Rightarrow (\operatorname{GameIso}\left(J, I\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Games/PyranimPosition.gameIso_symm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Yoav Binyamin, Evan Kniffen (2026). *Enumerating Pyranim Isomorphisms*. URL: <https://arxiv.org/abs/2611.16153v1>.

*Commentary.*

Invert the option bijection at each step of well-founded induction.

**Lemma 1.32 (Transitive game isomorphism).**

$$\forall n \in \mathbb{N},\; \forall m \in \mathbb{N},\; \forall I \in \operatorname{Stable}\left(n\right),\; \forall J \in \operatorname{Stable}\left(m\right),\; \forall l \in \mathbb{N},\; \forall K \in \operatorname{Stable}\left(l\right),\; (\operatorname{GameIso}\left(I, J\right)) \Rightarrow ((\operatorname{GameIso}\left(J, K\right)) \Rightarrow (\operatorname{GameIso}\left(I, K\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Games/PyranimPosition.gameIso_trans` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Yoav Binyamin, Evan Kniffen (2026). *Enumerating Pyranim Isomorphisms*. URL: <https://arxiv.org/abs/2611.16153v1>.

*Commentary.*

Compose the two option bijections and use well-founded induction on their matched options.

**Definition 1.33 (Dyck words of fixed semilength).**

$$\forall n \in \mathbb{N},\; \operatorname{DyckAt}\left(n\right) = \{w:DyckWord\mid w.semilength = n\}$$

*Formalization.* `D5/S3/Combinatorics/Games/PyranimPosition.DyckAt` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Yoav Binyamin, Evan Kniffen (2026). *Enumerating Pyranim Isomorphisms*. URL: <https://arxiv.org/abs/2611.16153v1>.

*Commentary.*

The subtype records the number of up-steps, equal to the number of down-steps.

**Definition 1.34 (Dyck block with a movable down-step).**

$$\forall L \in \mathbb{N},\; \forall i \in \operatorname{Fin}\left(L + 1\right),\; \operatorname{rankBlock}\left(L, i\right).toList = \operatorname{replicate}\left(i.val + 1, U\right)++[D]++\operatorname{replicate}\left(L - i.val, U\right)++\operatorname{replicate}\left(L, D\right)$$

*Formalization.* `D5/S3/Combinatorics/Games/PyranimPosition.rankBlock` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Yoav Binyamin, Evan Kniffen (2026). *Enumerating Pyranim Isomorphisms*. URL: <https://arxiv.org/abs/2611.16153v1>.

*Commentary.*

U and D are up-steps and down-steps. The index i places the first down-step after i+1 up-steps.

**Lemma 1.35 (Semilength of a rank block).**

$$\forall L \in \mathbb{N},\; \forall i \in \operatorname{Fin}\left(L + 1\right),\; \operatorname{rankBlock}\left(L, i\right).semilength = L + 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Games/PyranimPosition.rankBlock_semilength` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Yoav Binyamin, Evan Kniffen (2026). *Enumerating Pyranim Isomorphisms*. URL: <https://arxiv.org/abs/2611.16153v1>.

*Commentary.*

Every choice of the moving step leaves L+1 up-steps and L+1 down-steps.

**Lemma 1.36 (Length of a rank block).**

$$\forall L \in \mathbb{N},\; \forall i \in \operatorname{Fin}\left(L + 1\right),\; \operatorname{rankBlock}\left(L, i\right).toList.length = 2 \cdot (L + 1)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Games/PyranimPosition.rankBlock_length` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Yoav Binyamin, Evan Kniffen (2026). *Enumerating Pyranim Isomorphisms*. URL: <https://arxiv.org/abs/2611.16153v1>.

*Commentary.*

Every choice of i gives the same number of steps.

**Definition 1.37 (Replacing a balanced block).**

$$\forall n \in \mathbb{N},\; \forall w \in \operatorname{DyckAt}\left(n + 1\right),\; \forall pre \in \operatorname{List}\left(DyckStep\right),\; \forall post \in \operatorname{List}\left(DyckStep\right),\; \forall u \in DyckWord,\; \forall v \in DyckWord,\; \forall (h:w.val.toList = pre++u.toList++post), \forall (s:u.semilength = v.semilength), \operatorname{exchangeDyck}\left(w, pre, post, u, v, h, s\right).val.toList = pre++v.toList++post$$

*Formalization.* `D5/S3/Combinatorics/Games/PyranimPosition.exchangeDyck` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Yoav Binyamin, Evan Kniffen (2026). *Enumerating Pyranim Isomorphisms*. URL: <https://arxiv.org/abs/2611.16153v1>.

*Commentary.*

The original word is the prefix, the u block and the suffix. Equal lengths and matched up- and down-step counts make replacement by v preserve both the prefix inequalities and the ambient semilength.

**Theorem 1.38 (Strict increase in chip count under block replacement).**

$$\forall n \in \mathbb{N},\; \forall L \in \mathbb{N},\; \forall i \in \operatorname{Fin}\left(L + 1\right),\; \forall j \in \operatorname{Fin}\left(L + 1\right),\; (i < j) \Rightarrow (\forall p \in \operatorname{DyckAt}\left(n + 1\right),\; \forall q \in \operatorname{DyckAt}\left(n + 1\right),\; \forall pre \in \operatorname{List}\left(DyckStep\right),\; \forall post \in \operatorname{List}\left(DyckStep\right),\; (p.val.toList = pre++\operatorname{rankBlock}\left(L, i\right).toList++post) \Rightarrow ((q.val.toList = pre++\operatorname{rankBlock}\left(L, j\right).toList++post) \Rightarrow (\operatorname{chipCount}\left(\operatorname{stableEquivDyck}\left(n\right).symm\left(p\right)\right) < \operatorname{chipCount}\left(\operatorname{stableEquivDyck}\left(n\right).symm\left(q\right)\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Games/PyranimPosition.rankBlock_strict` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Yoav Binyamin, Evan Kniffen (2026). *Enumerating Pyranim Isomorphisms*. URL: <https://arxiv.org/abs/2611.16153v1>.

*Commentary.*

Increasing i weakly decreases every column’s omitted-start threshold and strictly enlarges the stable ideal. The other steps of the Dyck word are fixed.

## References

- Truth anchor: `D5/S3/Combinatorics/Games/PyranimPosition.DyckAt`
- Truth anchor: `D5/S3/Combinatorics/Games/PyranimPosition.FullBottom`
- Truth anchor: `D5/S3/Combinatorics/Games/PyranimPosition.GameIso`
- Truth anchor: `D5/S3/Combinatorics/Games/PyranimPosition.ImmediateAbove`
- Truth anchor: `D5/S3/Combinatorics/Games/PyranimPosition.Interval`
- Truth anchor: `D5/S3/Combinatorics/Games/PyranimPosition.LeftAbove`
- Truth anchor: `D5/S3/Combinatorics/Games/PyranimPosition.LegalOption`
- Truth anchor: `D5/S3/Combinatorics/Games/PyranimPosition.Options`
- Truth anchor: `D5/S3/Combinatorics/Games/PyranimPosition.RightAbove`
- Truth anchor: `D5/S3/Combinatorics/Games/PyranimPosition.Stable`
- Truth anchor: `D5/S3/Combinatorics/Games/PyranimPosition.UpperCover`
- Truth anchor: `D5/S3/Combinatorics/Games/PyranimPosition.Visible`
- Truth anchor: `D5/S3/Combinatorics/Games/PyranimPosition.cascade_iff`
- Truth anchor: `D5/S3/Combinatorics/Games/PyranimPosition.chipCount`
- Truth anchor: `D5/S3/Combinatorics/Games/PyranimPosition.chipCount_lt_of_option`
- Truth anchor: `D5/S3/Combinatorics/Games/PyranimPosition.emptyStable`
- Truth anchor: `D5/S3/Combinatorics/Games/PyranimPosition.exchangeDyck`
- Truth anchor: `D5/S3/Combinatorics/Games/PyranimPosition.fullBottomSuccEquiv`
- Truth anchor: `D5/S3/Combinatorics/Games/PyranimPosition.gameIso_iff`
- Truth anchor: `D5/S3/Combinatorics/Games/PyranimPosition.gameIso_refl`
- Truth anchor: `D5/S3/Combinatorics/Games/PyranimPosition.gameIso_symm`
- Truth anchor: `D5/S3/Combinatorics/Games/PyranimPosition.gameIso_trans`
- Truth anchor: `D5/S3/Combinatorics/Games/PyranimPosition.legalOption_ssubset`
- Truth anchor: `D5/S3/Combinatorics/Games/PyranimPosition.legalOption_wellFounded`
- Truth anchor: `D5/S3/Combinatorics/Games/PyranimPosition.lowerRight`
- Truth anchor: `D5/S3/Combinatorics/Games/PyranimPosition.raiseRight`
- Truth anchor: `D5/S3/Combinatorics/Games/PyranimPosition.raiseRight_lowerRight`
- Truth anchor: `D5/S3/Combinatorics/Games/PyranimPosition.rankBlock`
- Truth anchor: `D5/S3/Combinatorics/Games/PyranimPosition.rankBlock_length`
- Truth anchor: `D5/S3/Combinatorics/Games/PyranimPosition.rankBlock_semilength`
- Truth anchor: `D5/S3/Combinatorics/Games/PyranimPosition.rankBlock_strict`
- Truth anchor: `D5/S3/Combinatorics/Games/PyranimPosition.removeBottom`
- Truth anchor: `D5/S3/Combinatorics/Games/PyranimPosition.removeChip`
- Truth anchor: `D5/S3/Combinatorics/Games/PyranimPosition.removeChip_eq_stabilize`
- Truth anchor: `D5/S3/Combinatorics/Games/PyranimPosition.stabilize`
- Truth anchor: `D5/S3/Combinatorics/Games/PyranimPosition.stableCard`
- Truth anchor: `D5/S3/Combinatorics/Games/PyranimPosition.stableEquivDyck`
- Truth anchor: `D5/S3/Combinatorics/Games/PyranimPosition.visible_iff_covers`
- Dependency: [D5/S3/Combinatorics/InversionSeq/InversionSeq152Dyck](../InversionSeq/InversionSeq152Dyck.md)
