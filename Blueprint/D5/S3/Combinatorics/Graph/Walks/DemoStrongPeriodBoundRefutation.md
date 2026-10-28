# The strong distance-two period bound fails at the singleton

## Abstract

The connected singleton refutes the unrestricted strong distance-two period bound.

The operator uses exact shortest distance two and keeps the same vertex type. Its iterates may be disconnected. Strong return means an isomorphism to the initial graph after a positive number of applications; it does not mean an eventual return or preservation of vertex labels. The three graph definitions are universe-polymorphic. The closed conjecture quantifies vertex types in Type, with a finite-type instance and connectedness as its only graph hypothesis.

**Definition 1.1 (Exact distance two on the same vertices).**

$$\forall V \in \operatorname{Type}^*,\; \forall G \in \operatorname{SimpleGraph}\left(V\right),\; \forall u \in V,\; \forall v \in V,\; (\operatorname{SimpleGraph}.\operatorname{Adj}\left(\operatorname{distanceTwo}\left(G\right), u, v\right)) \Leftrightarrow (\operatorname{SimpleGraph}.\operatorname{edist}\left(G, u, v\right) = 2)$$

*Formalization.* `D5/S3/Combinatorics/Graph/Walks/DemoStrongPeriodBoundRefutation.distanceTwo` (`✓ std3`).

*Citation.* Gregory Demo, David Lund, Oleksiy Al-saadi (2026). *On the Periodicity of k-distance Graphs*. URL: <https://arxiv.org/abs/2606.25493v1>.

*Commentary.*

For every vertex type V and simple graph G on V, distanceTwo G is a simple graph on V with exactly this adjacency relation. SimpleGraph.edist is the extended natural shortest-walk distance; an unreachable pair has distance infinity, so is not adjacent here. Symmetry follows from SimpleGraph.edist_comm, and SimpleGraph.edist_self excludes loops.

**Definition 1.2 (Positive isomorphism return).**

$$\forall V \in \operatorname{Type}^*,\; \forall G \in \operatorname{SimpleGraph}\left(V\right),\; \forall t \in \mathbb{N},\; (\operatorname{PositiveReturn}\left(G, t\right)) \Leftrightarrow ((0 < t) \land (\operatorname{Nonempty}\left(\operatorname{SimpleGraph}.\operatorname{Iso}\left(\operatorname{Function}.\operatorname{iterate}\left(\operatorname{distanceTwo}, t, G\right), G\right)\right)))$$

*Formalization.* `D5/S3/Combinatorics/Graph/Walks/DemoStrongPeriodBoundRefutation.PositiveReturn` (`✓ std3`).

*Citation.* Gregory Demo, David Lund, Oleksiy Al-saadi (2026). *On the Periodicity of k-distance Graphs*. URL: <https://arxiv.org/abs/2606.25493v1>.

*Commentary.*

PositiveReturn G t is a proposition. Function.iterate(distanceTwo,t,G) applies distanceTwo exactly t times, starting with G at t = 0. SimpleGraph.Iso is the graph-isomorphism type and Nonempty asserts that an isomorphism exists. In Definition 1 of the source the initial graph has index one, so its first return index is f = t + 1, with f > 1.

**Definition 1.3 (Least positive return, with zero for no return).**

$$\forall V \in \operatorname{Type}^*,\; \forall G \in \operatorname{SimpleGraph}\left(V\right),\; (\forall h \in (\exists t \in \mathbb{N},\; \operatorname{PositiveReturn}\left(G, t\right)),\; \operatorname{strongPeriod}\left(G\right) = \operatorname{Nat}.\operatorname{find}\left(h\right)) \land ((\neg (\exists t \in \mathbb{N},\; \operatorname{PositiveReturn}\left(G, t\right))) \Rightarrow (\operatorname{strongPeriod}\left(G\right) = 0))$$

*Formalization.* `D5/S3/Combinatorics/Graph/Walks/DemoStrongPeriodBoundRefutation.strongPeriod` (`✓ std3`).

*Citation.* Gregory Demo, David Lund, Oleksiy Al-saadi (2026). *On the Periodicity of k-distance Graphs*. URL: <https://arxiv.org/abs/2606.25493v1>.

*Commentary.*

strongPeriod G is a natural number. These two exhaustive cases display its defining conditional: for an existence proof h, Nat.find h is the least t satisfying precisely PositiveReturn G t; if there is no such t, the value is zero. Thus zero is never a permitted return step. No finiteness or connectedness is required to define the operator, its return predicate, or this period.

**Definition 1.4 (The complete universal bound of Conjecture 1).**

$$(\operatorname{claim}) \Leftrightarrow (\forall V \in \operatorname{Type},\; \forall inst \in \operatorname{Fintype}\left(V\right),\; \forall G \in \operatorname{SimpleGraph}\left(V\right),\; (\operatorname{SimpleGraph}.\operatorname{Connected}\left(G\right)) \Rightarrow (\operatorname{Int}.\operatorname{ofNat}\left(\operatorname{strongPeriod}\left(G\right)\right) \le \operatorname{Int}.\operatorname{ofNat}\left(\operatorname{Fintype}.\operatorname{card}\left(V, inst\right)\right) - 3))$$

*Formalization.* `D5/S3/Combinatorics/Graph/Walks/DemoStrongPeriodBoundRefutation.claim` (`✓ std3`).

*Citation.* Gregory Demo, David Lund, Oleksiy Al-saadi (2026). *On the Periodicity of k-distance Graphs*. URL: <https://arxiv.org/abs/2606.25493v1>.

*Commentary.*

claim has type Prop and no parameters. The binder inst is the finite-type instance; Fintype.card(V,inst) displays that normally implicit instance explicitly. Both natural numbers are embedded into the integers by Int.ofNat before subtraction. There is no lower bound on the number of vertices, no nontriviality requirement and no positive-edge requirement.

**Theorem 1.5 (Refutation of the full universal claim).**

$$\neg (\forall V \in \operatorname{Type},\; \forall inst \in \operatorname{Fintype}\left(V\right),\; \forall G \in \operatorname{SimpleGraph}\left(V\right),\; (\operatorname{SimpleGraph}.\operatorname{Connected}\left(G\right)) \Rightarrow (\operatorname{Int}.\operatorname{ofNat}\left(\operatorname{strongPeriod}\left(G\right)\right) \le \operatorname{Int}.\operatorname{ofNat}\left(\operatorname{Fintype}.\operatorname{card}\left(V, inst\right)\right) - 3))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/DemoStrongPeriodBoundRefutation.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gregory Demo, David Lund, Oleksiy Al-saadi (2026). *On the Periodicity of k-distance Graphs*. URL: <https://arxiv.org/abs/2606.25493v1>.

*Acknowledgement.* William Q. Erickson, Daniel Herden, Jonathan Meddaugh, Mark R. Sepanski, Mitchell Minyard, Kyle Rosengartner (2024). *Limits and Periodicity of Metamour 2-Distance Graphs*. URL: <https://arxiv.org/abs/2409.02306v1>.

*Commentary.*

Take the edgeless simple graph on Unit. It is connected by SimpleGraph.Connected.of_subsingleton. Any two vertices coincide and their self-distance is zero, so distanceTwo G = G. Function.iterate_one and SimpleGraph.Iso.refl give PositiveReturn G 1. Nat.find_spec gives positivity of the least return and Nat.find_min' bounds it above by one; hence strongPeriod G = 1. Singleton cardinality then turns the asserted integer bound into 1 <= -2, a contradiction.

The singleton fixed-point fact is already in the earlier metamour source: Theorem 4.1 characterizes edgeless fixed points, and the proof of Theorem 6.5 explicitly notes that the singleton has period one. The result here is the negation of the later paper's complete printed bound. It establishes no corrected bound for larger graphs and makes no claim of a new fixed-point theorem.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/DemoStrongPeriodBoundRefutation.PositiveReturn`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/DemoStrongPeriodBoundRefutation.claim`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/DemoStrongPeriodBoundRefutation.distanceTwo`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/DemoStrongPeriodBoundRefutation.result`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/DemoStrongPeriodBoundRefutation.strongPeriod`
