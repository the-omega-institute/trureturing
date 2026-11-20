# First touch in clipped honeycomb domains

## Abstract

Synchronous first-touch dynamics and strict horizons in clipped honeycomb domains.

A stored pair gives the tick and multiplicity of the first touch. A vertex with multiplicity one is born and sends on the next tick. The seed starts with the pair (0, 1). In the formulas, u is the universe of the vertex type. The witnesses e and dec are Lean's typeclass arguments for decidable equality and adjacency. A type after a colon gives the type of a variable or of the displayed value.

**Definition 1.1 (Sending neighbors).**

$$\forall V \in \operatorname{Type} u,\; \forall G \in \operatorname{SimpleGraph}\left(V\right), dec \in \operatorname{DecidableRel}\left(G.\operatorname{Adj}\right),\; \forall D \in \operatorname{Finset}\left(V\right), t \in \mathbb{N}, prior \in V \to \operatorname{Option}\left((\mathbb{N} \times \mathbb{N})\right), v \in V,\; (\operatorname{sendingNeighbors}\left(G, D, t, \operatorname{prior}, v\right): \operatorname{Finset}\left(V\right)) = \{w: V \mid (w \in D) \land \left((G.\operatorname{Adj}\left(v, w\right)) \land (\operatorname{prior}\left(w\right) = \operatorname{some}\left((t, 1)\right))\right)\}$$

*Formalization.* `D5/S3/StatisticalMechanics/CellularAutomata/HoneycombFirstTouch.sendingNeighbors` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each retained sender is counted once by the finite set filter.

**Definition 1.2 (Stored first-touch state).**

$$\forall V \in \operatorname{Type} u,\; \forall e \in \operatorname{DecidableEq}\left(V\right),\; \forall G \in \operatorname{SimpleGraph}\left(V\right), dec \in \operatorname{DecidableRel}\left(G.\operatorname{Adj}\right),\; \forall D \in \operatorname{Finset}\left(V\right), seed \in V,\; \operatorname{state}\left(G, D, seed\right): \mathbb{N} \to V \to \operatorname{Option}\left((\mathbb{N} \times \mathbb{N})\right),\quad(\forall v \in V,\; \operatorname{state}\left(G, D, seed, 0, v\right) = \operatorname{ite}\left((v \in D) \land (v = seed), \operatorname{some}\left((0, 1)\right), \operatorname{none}\right)) \land (\forall t \in \mathbb{N}, v \in V,\; \operatorname{state}\left(G, D, seed, t + 1, v\right) = \operatorname{ite}\left(\operatorname{state}\left(G, D, seed, t, v\right) \ne \operatorname{none}, \operatorname{state}\left(G, D, seed, t, v\right), \operatorname{ite}\left((v \in D) \land (\operatorname{card}\left(\operatorname{sendingNeighbors}\left(G, D, t, \operatorname{state}\left(G, D, seed, t\right), v\right)\right) \ne 0), \operatorname{some}\left((t + 1, \operatorname{card}\left(\operatorname{sendingNeighbors}\left(G, D, t, \operatorname{state}\left(G, D, seed, t\right), v\right)\right))\right), \operatorname{none}\right)\right))$$

*Formalization.* `D5/S3/StatisticalMechanics/CellularAutomata/HoneycombFirstTouch.state` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The successor update keeps any stored pair. For an untouched retained vertex, the new pair is stored only when the sender count is positive.

**Definition 1.3 (First touch).**

$$\forall V \in \operatorname{Type} u,\; \forall e \in \operatorname{DecidableEq}\left(V\right),\; \forall G \in \operatorname{SimpleGraph}\left(V\right), dec \in \operatorname{DecidableRel}\left(G.\operatorname{Adj}\right),\; \forall D \in \operatorname{Finset}\left(V\right), seed \in V, t \in \mathbb{N}, v \in V,\; \forall mult \in \mathbb{N},\; (\operatorname{Touch}\left(G, D, seed, t, v, mult\right): \operatorname{Prop}) \Leftrightarrow (\operatorname{state}\left(G, D, seed, t, v\right) = \operatorname{some}\left((t, mult)\right))$$

*Formalization.* `D5/S3/StatisticalMechanics/CellularAutomata/HoneycombFirstTouch.Touch` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The stored time must be the queried tick.

**Definition 1.4 (Birth).**

$$\forall V \in \operatorname{Type} u,\; \forall e \in \operatorname{DecidableEq}\left(V\right),\; \forall G \in \operatorname{SimpleGraph}\left(V\right), dec \in \operatorname{DecidableRel}\left(G.\operatorname{Adj}\right),\; \forall D \in \operatorname{Finset}\left(V\right), seed \in V, t \in \mathbb{N}, v \in V,\; (\operatorname{Born}\left(G, D, seed, t, v\right): \operatorname{Prop}) \Leftrightarrow (\operatorname{Touch}\left(G, D, seed, t, v, 1\right))$$

*Formalization.* `D5/S3/StatisticalMechanics/CellularAutomata/HoneycombFirstTouch.Born` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A first touch with exactly one sender activates the vertex.

**Definition 1.5 (Intact status).**

$$\forall V \in \operatorname{Type} u,\; \forall e \in \operatorname{DecidableEq}\left(V\right),\; \forall G \in \operatorname{SimpleGraph}\left(V\right), dec \in \operatorname{DecidableRel}\left(G.\operatorname{Adj}\right),\; \forall D \in \operatorname{Finset}\left(V\right), seed \in V, t \in \mathbb{N}, v \in V,\; (\operatorname{Intact}\left(G, D, seed, t, v\right): \operatorname{Prop}) \Leftrightarrow (\operatorname{state}\left(G, D, seed, t, v\right) = \operatorname{none})$$

*Formalization.* `D5/S3/StatisticalMechanics/CellularAutomata/HoneycombFirstTouch.Intact` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The predicate checks the stored option. To use it as the status of a retained vertex, supply membership separately.

**Definition 1.6 (Senders at a vertex).**

$$\forall V \in \operatorname{Type} u,\; \forall e \in \operatorname{DecidableEq}\left(V\right),\; \forall G \in \operatorname{SimpleGraph}\left(V\right), dec \in \operatorname{DecidableRel}\left(G.\operatorname{Adj}\right),\; \forall D \in \operatorname{Finset}\left(V\right), seed \in V, t \in \mathbb{N}, v \in V,\; (\operatorname{senders}\left(G, D, seed, t, v\right): \operatorname{Finset}\left(V\right)) = \operatorname{sendingNeighbors}\left(G, D, t, \operatorname{state}\left(G, D, seed, t\right), v\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/CellularAutomata/HoneycombFirstTouch.senders` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The prior state is the state at the same tick t as the births that send.

**Theorem 1.7 (Membership in the sender set).**

$$\forall V \in \operatorname{Type} u,\; \forall e \in \operatorname{DecidableEq}\left(V\right),\; \forall G \in \operatorname{SimpleGraph}\left(V\right), dec \in \operatorname{DecidableRel}\left(G.\operatorname{Adj}\right),\; \forall D \in \operatorname{Finset}\left(V\right), seed \in V, v \in V, t \in \mathbb{N}, w \in V,\; (w \in \operatorname{senders}\left(G, D, seed, t, v\right)) \Leftrightarrow ((w \in D) \land \left((G.\operatorname{Adj}\left(v, w\right)) \land (\operatorname{Born}\left(G, D, seed, t, w\right))\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/CellularAutomata/HoneycombFirstTouch.mem_senders` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Membership can be tested using the birth predicate at the source vertex w.

**Theorem 1.8 (First touch at tick zero).**

$$\forall V \in \operatorname{Type} u,\; \forall e \in \operatorname{DecidableEq}\left(V\right),\; \forall G \in \operatorname{SimpleGraph}\left(V\right), dec \in \operatorname{DecidableRel}\left(G.\operatorname{Adj}\right),\; \forall D \in \operatorname{Finset}\left(V\right), seed \in V, v \in V, mult \in \mathbb{N},\; (\operatorname{Touch}\left(G, D, seed, 0, v, mult\right)) \Leftrightarrow ((v \in D) \land \left((v = seed) \land (mult = 1)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/CellularAutomata/HoneycombFirstTouch.touch_zero_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Tick zero supplies the initial event for the induction on time.

**Theorem 1.9 (Retention and positive multiplicity).**

$$\forall V \in \operatorname{Type} u,\; \forall e \in \operatorname{DecidableEq}\left(V\right),\; \forall G \in \operatorname{SimpleGraph}\left(V\right), dec \in \operatorname{DecidableRel}\left(G.\operatorname{Adj}\right),\; \forall D \in \operatorname{Finset}\left(V\right), seed \in V, v \in V, t \in \mathbb{N}, mult \in \mathbb{N},\; (\operatorname{Touch}\left(G, D, seed, t, v, mult\right)) \Rightarrow ((v \in D) \land (0 < mult))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/CellularAutomata/HoneycombFirstTouch.touch_retained_and_positive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

These constraints hold for the stored pair at any first-touch event.

**Theorem 1.10 (Intact status through a tick).**

$$\forall V \in \operatorname{Type} u,\; \forall e \in \operatorname{DecidableEq}\left(V\right),\; \forall G \in \operatorname{SimpleGraph}\left(V\right), dec \in \operatorname{DecidableRel}\left(G.\operatorname{Adj}\right),\; \forall D \in \operatorname{Finset}\left(V\right), seed \in V, v \in V, t \in \mathbb{N},\; (\operatorname{Intact}\left(G, D, seed, t, v\right)) \Leftrightarrow (\forall s \in \mathbb{N},\; (s \le t) \Rightarrow (\forall mult \in \mathbb{N},\; \neg (\operatorname{Touch}\left(G, D, seed, s, v, mult\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/CellularAutomata/HoneycombFirstTouch.intact_iff_no_touch` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The quantifier over earlier ticks includes the current tick.

**Theorem 1.11 (Uniqueness of touch data).**

$$\forall V \in \operatorname{Type} u,\; \forall e \in \operatorname{DecidableEq}\left(V\right),\; \forall G \in \operatorname{SimpleGraph}\left(V\right), dec \in \operatorname{DecidableRel}\left(G.\operatorname{Adj}\right),\; \forall D \in \operatorname{Finset}\left(V\right), seed \in V, v \in V, t \in \mathbb{N}, s \in \mathbb{N}, mult \in \mathbb{N},\; (\operatorname{Touch}\left(G, D, seed, s, v, mult\right)) \Rightarrow (\forall other \in \mathbb{N},\; (\operatorname{Touch}\left(G, D, seed, t, v, other\right)) \Rightarrow ((s = t) \land (mult = other)))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/CellularAutomata/HoneycombFirstTouch.touch_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Persistence makes both the tick and the multiplicity unique.

**Theorem 1.12 (Strict horizon on a general graph).**

$$\forall V \in \operatorname{Type} u,\; \forall e \in \operatorname{DecidableEq}\left(V\right),\; \forall G \in \operatorname{SimpleGraph}\left(V\right), dec \in \operatorname{DecidableRel}\left(G.\operatorname{Adj}\right),\; \forall D \in \operatorname{Finset}\left(V\right), E \in \operatorname{Finset}\left(V\right), seed \in V, h \in V \to \mathbb{N},\; (D \subseteq E) \Rightarrow \left((seed \in D) \Rightarrow \left((\forall v \in V, w \in V,\; (G.\operatorname{Adj}\left(v, w\right)) \Rightarrow (h\left(v\right) \le h\left(w\right) + 1)) \Rightarrow \left((\forall v \in V,\; (v \in E) \Rightarrow \left((\neg (v \in D)) \Rightarrow \left((\exists w \in V,\; (w \in D) \land (G.\operatorname{Adj}\left(v, w\right))) \Rightarrow (\forall t \in \mathbb{N},\; (t < h\left(v\right)) \Rightarrow (\neg (\operatorname{Born}\left(G, E, seed, t, v\right))))\right)\right)) \Rightarrow (\forall t \in \mathbb{N},\; (\forall v \in V,\; (v \in D) \Rightarrow \left((t < h\left(v\right)) \Rightarrow (\forall mult \in \mathbb{N},\; (0 < mult) \Rightarrow ((\operatorname{Touch}\left(G, D, seed, t, v, mult\right)) \Leftrightarrow (\operatorname{Touch}\left(G, E, seed, t, v, mult\right))))\right)) \land (\forall v \in V,\; (v \in E) \Rightarrow \left((\neg (v \in D)) \Rightarrow \left((t < h\left(v\right)) \Rightarrow (\neg (\operatorname{Born}\left(G, E, seed, t, v\right)))\right)\right)))\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/CellularAutomata/HoneycombFirstTouch.strict_horizon` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The wall hypothesis applies to exterior vertices with an edge into D. The second conclusion ranges over every exterior vertex of E.

For honeycomb geometry, Vertex is Bool × ℤ × ℤ. Write v=(p,x,y) and use p(v), x(v), y(v) for its projections. The operation land is Nat.land, the bitwise AND of natural numbers. Subtraction in natural parameters is truncated.

**Definition 1.13 (A vertex).**

$$\forall x \in \mathbb{Z}, y \in \mathbb{Z},\; (\operatorname{A}\left(x, y\right): \operatorname{Vertex}) = (\operatorname{false}, (x, y))$$

*Formalization.* `D5/S3/StatisticalMechanics/CellularAutomata/HoneycombFirstTouch.A` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The first coordinate identifies the A part of the bipartition.

**Definition 1.14 (B vertex).**

$$\forall x \in \mathbb{Z}, y \in \mathbb{Z},\; (\operatorname{B}\left(x, y\right): \operatorname{Vertex}) = (\operatorname{true}, (x, y))$$

*Formalization.* `D5/S3/StatisticalMechanics/CellularAutomata/HoneycombFirstTouch.B` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The first coordinate identifies the B part of the bipartition.

**Definition 1.15 (Adjacency laws).**

$$\forall G \in \operatorname{SimpleGraph}\left(\operatorname{Vertex}\right),\; (\operatorname{NeighborLaws}\left(G\right): \operatorname{Prop}) \Leftrightarrow ((\forall v \in \operatorname{Vertex}, w \in \operatorname{Vertex},\; (G.\operatorname{Adj}\left(v, w\right)) \Rightarrow (\operatorname{p}\left(v\right) \ne \operatorname{p}\left(w\right))) \land (\forall x \in \mathbb{Z}, y \in \mathbb{Z}, a \in \mathbb{Z}, b \in \mathbb{Z},\; (G.\operatorname{Adj}\left(\operatorname{A}\left(x, y\right), \operatorname{B}\left(a, b\right)\right)) \Leftrightarrow (((x = a) \land (y = b)) \lor \left(((x = a + 1) \land (y = b)) \lor ((x = a) \land (y = b + 1))\right))))$$

*Formalization.* `D5/S3/StatisticalMechanics/CellularAutomata/HoneycombFirstTouch.NeighborLaws` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The two fields of the structure are opposite and fromA, in the order displayed.

**Theorem 1.16 (Neighbors of an A vertex).**

$$\forall G \in \operatorname{SimpleGraph}\left(\operatorname{Vertex}\right),\; (\operatorname{NeighborLaws}\left(G\right)) \Rightarrow (\forall x \in \mathbb{Z}, y \in \mathbb{Z}, w \in \operatorname{Vertex},\; (G.\operatorname{Adj}\left(\operatorname{A}\left(x, y\right), w\right)) \Leftrightarrow ((w = \operatorname{B}\left(x, y\right)) \lor \left((w = \operatorname{B}\left(x - 1, y\right)) \lor (w = \operatorname{B}\left(x, y - 1\right))\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/CellularAutomata/HoneycombFirstTouch.neighbors_A` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The two nonzero offsets from A to B each subtract one in a different coordinate.

**Theorem 1.17 (Neighbors of a B vertex).**

$$\forall G \in \operatorname{SimpleGraph}\left(\operatorname{Vertex}\right),\; (\operatorname{NeighborLaws}\left(G\right)) \Rightarrow (\forall x \in \mathbb{Z}, y \in \mathbb{Z}, w \in \operatorname{Vertex},\; (G.\operatorname{Adj}\left(\operatorname{B}\left(x, y\right), w\right)) \Leftrightarrow ((w = \operatorname{A}\left(x, y\right)) \lor \left((w = \operatorname{A}\left(x + 1, y\right)) \lor (w = \operatorname{A}\left(x, y + 1\right))\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/CellularAutomata/HoneycombFirstTouch.neighbors_B` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The reverse offsets from B to A each add one in a different coordinate.

**Definition 1.18 (Integer color).**

$$\forall v \in \operatorname{Vertex},\; (\operatorname{part}\left(v\right): \mathbb{Z}) = \operatorname{ite}\left(\operatorname{p}\left(v\right), 1, 0\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/CellularAutomata/HoneycombFirstTouch.part` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The Boolean color is read as an integer.

**Definition 1.19 (Coordinate sum).**

$$\forall v \in \operatorname{Vertex},\; (\operatorname{heightSum}\left(v\right): \mathbb{Z}) = \operatorname{x}\left(v\right) + \operatorname{y}\left(v\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/CellularAutomata/HoneycombFirstTouch.heightSum` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The diagonal height is independent of the color.

**Definition 1.20 (Cut coordinate).**

$$\forall v \in \operatorname{Vertex},\; (\operatorname{g}\left(v\right): \mathbb{Z}) = 2 \cdot \operatorname{x}\left(v\right) + \operatorname{y}\left(v\right) + \operatorname{part}\left(v\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/CellularAutomata/HoneycombFirstTouch.g` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The strict cut compares this integer coordinate with the cut threshold.

**Definition 1.21 (Earliest possible touch).**

$$\forall v \in \operatorname{Vertex},\; (\operatorname{earliest}\left(v\right): \mathbb{N}) = \operatorname{Int.toNat}\left(\operatorname{g}\left(v\right) + \operatorname{y}\left(v\right)\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/CellularAutomata/HoneycombFirstTouch.earliest` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The integer expression is converted to a natural only after adding the y-coordinate.

**Definition 1.22 (Displaced-wall horizon).**

$$\forall P \in \mathbb{N}, v \in \operatorname{Vertex},\; (\operatorname{horizon}\left(P, v\right): \mathbb{N}) = \operatorname{Int.toNat}\left(2 \cdot \operatorname{x}\left(v\right) + \operatorname{part}\left(v\right) + 2 \cdot (P: \mathbb{Z})\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/CellularAutomata/HoneycombFirstTouch.horizon` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The formula allows any natural width P.

**Definition 1.23 (Retained finite domain).**

$$\forall a \in \mathbb{N}, K \in \mathbb{N},\; (\operatorname{domain}\left(a, K\right): \operatorname{Finset}\left(\operatorname{Vertex}\right)) = \{v \in \operatorname{univ}\left(\operatorname{Bool}\right) \times (\operatorname{Ico}\left((0: \mathbb{Z}), (a: \mathbb{Z})\right) \times \operatorname{Ico}\left((0: \mathbb{Z}), (a: \mathbb{Z})\right)) \mid (\operatorname{heightSum}\left(v\right) < (a: \mathbb{Z})) \land (\operatorname{g}\left(v\right) < (K: \mathbb{Z}))\}$$

*Formalization.* `D5/S3/StatisticalMechanics/CellularAutomata/HoneycombFirstTouch.domain` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The braces denote a filter on the finite product with two half-open integer intervals.

**Theorem 1.24 (Retained vertex criterion).**

$$\forall a \in \mathbb{N}, K \in \mathbb{N}, v \in \operatorname{Vertex},\; (v \in \operatorname{domain}\left(a, K\right)) \Leftrightarrow ((0 \le \operatorname{x}\left(v\right)) \land \left((0 \le \operatorname{y}\left(v\right)) \land ((\operatorname{heightSum}\left(v\right) < (a: \mathbb{Z})) \land (\operatorname{g}\left(v\right) < (K: \mathbb{Z})))\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/CellularAutomata/HoneycombFirstTouch.mem_domain` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The nonnegative coordinates and the two strict bounds characterize the filtered domain.

**Theorem 1.25 (Monotonicity in height).**

$$\forall m \in \mathbb{N}, N \in \mathbb{N}, K \in \mathbb{N},\; (m \le N) \Rightarrow (\operatorname{domain}\left(m, K\right) \subseteq \operatorname{domain}\left(N, K\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/CellularAutomata/HoneycombFirstTouch.domain_mono` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The cut threshold K is held fixed.

**Theorem 1.26 (Seed retention).**

$$\forall a \in \mathbb{N}, K \in \mathbb{N},\; (0 < a) \Rightarrow \left((0 < K) \Rightarrow (\operatorname{A}\left(0, 0\right) \in \operatorname{domain}\left(a, K\right))\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/CellularAutomata/HoneycombFirstTouch.seed_mem` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The strict inequalities on height and threshold retain the zero origin.

**Theorem 1.27 (Lower bound on touch time).**

$$\forall G \in \operatorname{SimpleGraph}\left(\operatorname{Vertex}\right),\; \forall dec \in \operatorname{DecidableRel}\left(G.\operatorname{Adj}\right),\; (\operatorname{NeighborLaws}\left(G\right)) \Rightarrow (\forall D \in \operatorname{Finset}\left(\operatorname{Vertex}\right), t \in \mathbb{N}, mult \in \mathbb{N}, v \in \operatorname{Vertex},\; (\operatorname{Touch}\left(G, D, \operatorname{A}\left(0, 0\right), t, v, mult\right)) \Rightarrow (\operatorname{earliest}\left(v\right) \le t))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/CellularAutomata/HoneycombFirstTouch.earliest_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The bound applies to touches of arbitrary multiplicity in any finite retained set.

**Definition 1.28 (Sufficient parity condition).**

$$\forall G \in \operatorname{SimpleGraph}\left(\operatorname{Vertex}\right),\; \forall dec \in \operatorname{DecidableRel}\left(G.\operatorname{Adj}\right),\; \forall D \in \operatorname{Finset}\left(\operatorname{Vertex}\right),\; (\operatorname{EarliestBirths}\left(G, D\right): \operatorname{Prop}) \Leftrightarrow (\forall v \in \operatorname{Vertex},\; (v \in D) \Rightarrow \left((\operatorname{land}\left(\operatorname{Int.toNat}\left(\operatorname{x}\left(v\right)\right), \operatorname{Int.toNat}\left(\operatorname{y}\left(v\right)\right)\right) = 0) \Rightarrow (\operatorname{Born}\left(G, D, \operatorname{A}\left(0, 0\right), \operatorname{earliest}\left(v\right), v\right))\right))$$

*Formalization.* `D5/S3/StatisticalMechanics/CellularAutomata/HoneycombFirstTouch.EarliestBirths` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Only the sufficient direction of the bitwise criterion is assumed here.

At a dyadic width dividing the smaller height, a crossing edge can leave the smaller domain only at the diagonal A wall. Below the dyadic width, the two eligible parents send together. At or above that width, the earliest-touch bound suffices. Induction on time transports the full touch data and excludes earlier exterior births.

**Theorem 1.29 (Strict horizon across clipped honeycombs).**

$$\forall G \in \operatorname{SimpleGraph}\left(\operatorname{Vertex}\right),\; \forall dec \in \operatorname{DecidableRel}\left(G.\operatorname{Adj}\right),\; (\operatorname{NeighborLaws}\left(G\right)) \Rightarrow (\forall b \in \mathbb{N}, m \in \mathbb{N}, N \in \mathbb{N}, K \in \mathbb{N},\; (0 < m) \Rightarrow \left((m < N) \Rightarrow \left((1 \le K) \Rightarrow \left((K \le 2 \cdot m) \Rightarrow \left((2^{b} \mid m) \Rightarrow \left((\operatorname{EarliestBirths}\left(G, \operatorname{domain}\left(N, K\right)\right)) \Rightarrow (\forall t \in \mathbb{N},\; (\forall v \in \operatorname{Vertex},\; (v \in \operatorname{domain}\left(m, K\right)) \Rightarrow \left((t < \operatorname{horizon}\left(2^{b}, v\right)) \Rightarrow (\forall mult \in \mathbb{N},\; (0 < mult) \Rightarrow ((\operatorname{Touch}\left(G, \operatorname{domain}\left(m, K\right), \operatorname{A}\left(0, 0\right), t, v, mult\right)) \Leftrightarrow (\operatorname{Touch}\left(G, \operatorname{domain}\left(N, K\right), \operatorname{A}\left(0, 0\right), t, v, mult\right))))\right)) \land (\forall v \in \operatorname{Vertex},\; (v \in \operatorname{domain}\left(N, K\right)) \Rightarrow \left((\neg (v \in \operatorname{domain}\left(m, K\right))) \Rightarrow \left((t < \operatorname{horizon}\left(2^{b}, v\right)) \Rightarrow (\neg (\operatorname{Born}\left(G, \operatorname{domain}\left(N, K\right), \operatorname{A}\left(0, 0\right), t, v\right)))\right)\right)))\right)\right)\right)\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/CellularAutomata/HoneycombFirstTouch.clipped_first_touch` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The same cut K, seed and horizon are used in both runs. Both conclusions are strict in the queried tick.

**Definition 1.30 (Adjacent-cut domain).**

$$\forall a \in \mathbb{N}, d \in \mathbb{N},\; (\operatorname{omegaDomain}\left(a, d\right): \operatorname{Finset}\left(\operatorname{Vertex}\right)) = \operatorname{domain}\left(a, 2 \cdot a - d\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/CellularAutomata/HoneycombFirstTouch.omegaDomain` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Increasing d narrows the cut by lowering the threshold.

**Theorem 1.31 (Monotonicity in the cut threshold).**

$$\forall a \in \mathbb{N}, K \in \mathbb{N}, L \in \mathbb{N},\; (K \le L) \Rightarrow (\operatorname{domain}\left(a, K\right) \subseteq \operatorname{domain}\left(a, L\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/CellularAutomata/HoneycombFirstTouch.domain_cut_mono` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The height a is held fixed.

**Definition 1.32 (Earliest-birth parity law).**

$$\forall G \in \operatorname{SimpleGraph}\left(\operatorname{Vertex}\right),\; \forall dec \in \operatorname{DecidableRel}\left(G.\operatorname{Adj}\right),\; (\operatorname{EarliestBirthIff}\left(G\right): \operatorname{Prop}) \Leftrightarrow (\forall a \in \mathbb{N}, c \in \mathbb{N},\; (0 < a) \Rightarrow \left((c \le a) \Rightarrow (\forall v \in \operatorname{Vertex},\; (v \in \operatorname{omegaDomain}\left(a, c\right)) \Rightarrow ((\operatorname{Born}\left(G, \operatorname{omegaDomain}\left(a, c\right), \operatorname{A}\left(0, 0\right), \operatorname{earliest}\left(v\right), v\right)) \Leftrightarrow (\operatorname{land}\left(\operatorname{Int.toNat}\left(\operatorname{x}\left(v\right)\right), \operatorname{Int.toNat}\left(\operatorname{y}\left(v\right)\right)\right) = 0)))\right))$$

*Formalization.* `D5/S3/StatisticalMechanics/CellularAutomata/HoneycombFirstTouch.EarliestBirthIff` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The criterion is restricted to the positive-height range 0 ≤ c ≤ a and to vertices in the cut domain.

**Theorem 1.33 (Parity law from the adjacency laws).**

$$\forall G \in \operatorname{SimpleGraph}\left(\operatorname{Vertex}\right),\; \forall dec \in \operatorname{DecidableRel}\left(G.\operatorname{Adj}\right),\; (\operatorname{NeighborLaws}\left(G\right)) \Rightarrow (\operatorname{EarliestBirthIff}\left(G\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/CellularAutomata/HoneycombFirstTouch.earliestBirthIff_of_neighborLaws` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The graph-level adjacency laws suffice to derive the Pascal parity criterion for the cut domains.

**Definition 1.34 (Decidable repository adjacency).**

$$\operatorname{repositoryAdjacency}: \operatorname{DecidableRel}\left(\operatorname{honeycombGraph}.\operatorname{Adj}\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/CellularAutomata/HoneycombFirstTouch.repositoryAdjacency` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The decision procedure tests the color and the three allowed offsets of the repository graph.

**Theorem 1.35 (Adjacency laws on the repository graph).**

$$\operatorname{NeighborLaws}\left(\operatorname{honeycombGraph}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/CellularAutomata/HoneycombFirstTouch.repositoryNeighborLaws` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Here honeycombGraph is the existing graph in HoneycombCylinderCoordination.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/CellularAutomata/HoneycombFirstTouch.A`
- Truth anchor: `D5/S3/StatisticalMechanics/CellularAutomata/HoneycombFirstTouch.B`
- Truth anchor: `D5/S3/StatisticalMechanics/CellularAutomata/HoneycombFirstTouch.Born`
- Truth anchor: `D5/S3/StatisticalMechanics/CellularAutomata/HoneycombFirstTouch.EarliestBirthIff`
- Truth anchor: `D5/S3/StatisticalMechanics/CellularAutomata/HoneycombFirstTouch.EarliestBirths`
- Truth anchor: `D5/S3/StatisticalMechanics/CellularAutomata/HoneycombFirstTouch.Intact`
- Truth anchor: `D5/S3/StatisticalMechanics/CellularAutomata/HoneycombFirstTouch.NeighborLaws`
- Truth anchor: `D5/S3/StatisticalMechanics/CellularAutomata/HoneycombFirstTouch.Touch`
- Truth anchor: `D5/S3/StatisticalMechanics/CellularAutomata/HoneycombFirstTouch.clipped_first_touch`
- Truth anchor: `D5/S3/StatisticalMechanics/CellularAutomata/HoneycombFirstTouch.domain`
- Truth anchor: `D5/S3/StatisticalMechanics/CellularAutomata/HoneycombFirstTouch.domain_cut_mono`
- Truth anchor: `D5/S3/StatisticalMechanics/CellularAutomata/HoneycombFirstTouch.domain_mono`
- Truth anchor: `D5/S3/StatisticalMechanics/CellularAutomata/HoneycombFirstTouch.earliest`
- Truth anchor: `D5/S3/StatisticalMechanics/CellularAutomata/HoneycombFirstTouch.earliestBirthIff_of_neighborLaws`
- Truth anchor: `D5/S3/StatisticalMechanics/CellularAutomata/HoneycombFirstTouch.earliest_bound`
- Truth anchor: `D5/S3/StatisticalMechanics/CellularAutomata/HoneycombFirstTouch.g`
- Truth anchor: `D5/S3/StatisticalMechanics/CellularAutomata/HoneycombFirstTouch.heightSum`
- Truth anchor: `D5/S3/StatisticalMechanics/CellularAutomata/HoneycombFirstTouch.horizon`
- Truth anchor: `D5/S3/StatisticalMechanics/CellularAutomata/HoneycombFirstTouch.intact_iff_no_touch`
- Truth anchor: `D5/S3/StatisticalMechanics/CellularAutomata/HoneycombFirstTouch.mem_domain`
- Truth anchor: `D5/S3/StatisticalMechanics/CellularAutomata/HoneycombFirstTouch.mem_senders`
- Truth anchor: `D5/S3/StatisticalMechanics/CellularAutomata/HoneycombFirstTouch.neighbors_A`
- Truth anchor: `D5/S3/StatisticalMechanics/CellularAutomata/HoneycombFirstTouch.neighbors_B`
- Truth anchor: `D5/S3/StatisticalMechanics/CellularAutomata/HoneycombFirstTouch.omegaDomain`
- Truth anchor: `D5/S3/StatisticalMechanics/CellularAutomata/HoneycombFirstTouch.part`
- Truth anchor: `D5/S3/StatisticalMechanics/CellularAutomata/HoneycombFirstTouch.repositoryAdjacency`
- Truth anchor: `D5/S3/StatisticalMechanics/CellularAutomata/HoneycombFirstTouch.repositoryNeighborLaws`
- Truth anchor: `D5/S3/StatisticalMechanics/CellularAutomata/HoneycombFirstTouch.seed_mem`
- Truth anchor: `D5/S3/StatisticalMechanics/CellularAutomata/HoneycombFirstTouch.senders`
- Truth anchor: `D5/S3/StatisticalMechanics/CellularAutomata/HoneycombFirstTouch.sendingNeighbors`
- Truth anchor: `D5/S3/StatisticalMechanics/CellularAutomata/HoneycombFirstTouch.state`
- Truth anchor: `D5/S3/StatisticalMechanics/CellularAutomata/HoneycombFirstTouch.strict_horizon`
- Truth anchor: `D5/S3/StatisticalMechanics/CellularAutomata/HoneycombFirstTouch.touch_retained_and_positive`
- Truth anchor: `D5/S3/StatisticalMechanics/CellularAutomata/HoneycombFirstTouch.touch_unique`
- Truth anchor: `D5/S3/StatisticalMechanics/CellularAutomata/HoneycombFirstTouch.touch_zero_iff`
- Dependency: [D5/S3/StatisticalMechanics/HoneycombCylinderCoordination](../HoneycombCylinderCoordination.md)
