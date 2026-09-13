# Crossing- and Nesting-Free Labeled Graphs

## Abstract

Barker's recurrence counts labeled simple graphs whose edges neither cross nor nest.

Vertices are linearly ordered by Fin(n). An edge is an ordered pair whose first endpoint is smaller than its second endpoint. The count uses literal finite sets of such ordered pairs.

**Definition 1.1 (Crossing edges).**

$$\forall n \in \mathbb{N},\; \forall e \in Fin\left(n\right) \times Fin\left(n\right), f \in Fin\left(n\right) \times Fin\left(n\right),\; Crossing\left(e, f\right) \Leftrightarrow ((fst\left(e\right) < fst\left(f\right) \land \left(fst\left(f\right) < snd\left(e\right) \land snd\left(e\right) < snd\left(f\right)\right)) \lor (fst\left(f\right) < fst\left(e\right) \land \left(fst\left(e\right) < snd\left(f\right) \land snd\left(f\right) < snd\left(e\right)\right)))$$

*Formalization.* `D5/S1/Words/Patterns/NoncrossingNonnestingGraphRecurrence.Crossing` (`✓ std3`).

*Citation.* Colin Barker (2019). *OEIS A326244, Number of labeled n-vertex simple graphs without crossing or nesting edges*. URL: <https://oeis.org/A326244>.

*Commentary.*

Two ordered pairs cross exactly when their four endpoints occur in one of the two alternating orders stated in the OEIS entry.

**Definition 1.2 (Nesting edges).**

$$\forall n \in \mathbb{N},\; \forall e \in Fin\left(n\right) \times Fin\left(n\right), f \in Fin\left(n\right) \times Fin\left(n\right),\; Nesting\left(e, f\right) \Leftrightarrow ((fst\left(e\right) < fst\left(f\right) \land \left(fst\left(f\right) < snd\left(f\right) \land snd\left(f\right) < snd\left(e\right)\right)) \lor (fst\left(f\right) < fst\left(e\right) \land \left(fst\left(e\right) < snd\left(e\right) \land snd\left(e\right) < snd\left(f\right)\right)))$$

*Formalization.* `D5/S1/Words/Patterns/NoncrossingNonnestingGraphRecurrence.Nesting` (`✓ std3`).

*Citation.* Colin Barker (2019). *OEIS A326244, Number of labeled n-vertex simple graphs without crossing or nesting edges*. URL: <https://oeis.org/A326244>.

*Commentary.*

The endpoints of one edge lie strictly between the endpoints of the other, with both edges increasing.

**Definition 1.3 (Graphs avoiding both edge patterns).**

$$\forall n \in \mathbb{N},\; \forall E \in Finset\left((Fin\left(n\right) \times Fin\left(n\right))\right),\; IsAvoiding\left(E\right) \Leftrightarrow (\left(\forall e \in E,\; fst\left(e\right) < snd\left(e\right)\right) \land \left(\forall e \in E,\; \forall f \in E,\; \left(\neg Crossing\left(e, f\right)\right) \land \left(\neg Nesting\left(e, f\right)\right)\right))$$

*Formalization.* `D5/S1/Words/Patterns/NoncrossingNonnestingGraphRecurrence.IsAvoiding` (`✓ std3`).

*Citation.* Colin Barker (2019). *OEIS A326244, Number of labeled n-vertex simple graphs without crossing or nesting edges*. URL: <https://oeis.org/A326244>.

*Commentary.*

Every edge is increasing, and every ordered pair of edges avoids both crossing and nesting. Repeated choices of the same edge are included in the universal condition and satisfy it automatically.

**Definition 1.4 (The A326244 counting function).**

$$\forall n \in \mathbb{N},\; a\left(n\right) = card\left(filter\left((E \mapsto IsAvoiding\left(E\right)), univ\left(Finset\left((Fin\left(n\right) \times Fin\left(n\right))\right)\right)\right)\right)$$

*Formalization.* `D5/S1/Words/Patterns/NoncrossingNonnestingGraphRecurrence.a` (`✓ std3`).

*Citation.* Colin Barker (2019). *OEIS A326244, Number of labeled n-vertex simple graphs without crossing or nesting edges*. URL: <https://oeis.org/A326244>.

*Commentary.*

The value a(n) is the cardinality of the filter of avoiding edge sets inside the finite universe of all edge sets on Fin(n).

**Theorem 1.5 (Barker's third-order recurrence).**

$$\forall n \in \mathbb{N},\; 2 < n \Rightarrow Int\left(a\left(n\right)\right) = 6 \cdot Int\left(a\left(n - 1\right)\right) - 8 \cdot Int\left(a\left(n - 2\right)\right) + 4 \cdot Int\left(a\left(n - 3\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Patterns/NoncrossingNonnestingGraphRecurrence.barker_a326244` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a326244-noncrossing-nonnesting-graph-recurrence` (proved) by `D5/S1/Words/Patterns/NoncrossingNonnestingGraphRecurrence.barker_a326244`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a326244-noncrossing-nonnesting-graph-recurrence","declaration_gid":"D5/S1/Words/Patterns/NoncrossingNonnestingGraphRecurrence.barker_a326244","resolution_kind":"proved"} -->

*Citation.* Colin Barker (2019). *OEIS A326244, Number of labeled n-vertex simple graphs without crossing or nesting edges*. URL: <https://oeis.org/A326244>.

*Commentary.*

Removing the greatest vertex identifies every avoiding graph on n+1 vertices with an avoiding graph G on n vertices and a subset of its allowed vertices. The new allowed-set size is r+1, 2, or 1 according as the chosen subset is empty, a singleton, or has at least two members. Three weighted counts obey first-order identities; eliminating the two auxiliary moments gives the displayed recurrence for every n greater than two.

## References

- Truth anchor: `D5/S1/Words/Patterns/NoncrossingNonnestingGraphRecurrence.Crossing`
- Truth anchor: `D5/S1/Words/Patterns/NoncrossingNonnestingGraphRecurrence.IsAvoiding`
- Truth anchor: `D5/S1/Words/Patterns/NoncrossingNonnestingGraphRecurrence.Nesting`
- Truth anchor: `D5/S1/Words/Patterns/NoncrossingNonnestingGraphRecurrence.a`
- Truth anchor: `D5/S1/Words/Patterns/NoncrossingNonnestingGraphRecurrence.barker_a326244`
