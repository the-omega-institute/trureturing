# Matching-twisted clique cycles

## Abstract

Clique fibers joined by arbitrary perfect matchings have the maximal-independent-set spectrum of the preceding cycle power and diameter one greater than the cycle diameter.

The construction, spectrum shift and sharp diameter follow the mathematical argument supplied by Thanh Vu. Literature priority is unassessed. Each successive pair of clique fibers is joined by a bijective matching. The closing matching is unrestricted, so the accumulated twist can be arbitrary.

All parameters m and t are natural numbers: the cycle length is m+3 and the fiber order is t+3. Arithmetic on a base position is modulo m+3. Write applyMatching(M,i,a) for M(i)(a), imageFst(I) for the image of I under the first-coordinate projection, and NatDiv(a,b) for natural-number division. The symbol d denotes the graph-power exponent, while k in the spectrum definition denotes a cardinality. For the connected graphs here, power(G,d) joins distinct vertices at distance at most d; power(G,0) is edgeless. IsMaximalIndep(G,I) means that I is independent and every omitted vertex has a neighbor in I.

**Definition 1.1 (Vertex fibers).**

$$\forall m \in \mathrm{Nat},\; \forall t \in \mathrm{Nat},\; \operatorname{Vertex}\left(m, t\right) = \operatorname{Prod}\left(\operatorname{Fin}\left(m + 3\right), \operatorname{Fin}\left(t + 3\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/Walks/MatchingCliqueCycle.Vertex` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The offsets express every fiber order and cycle length at least three. A vertex consists of its base position and its fiber label.

**Definition 1.2 (The matching family).**

$$\forall m \in \mathrm{Nat},\; \forall t \in \mathrm{Nat},\; \operatorname{Matchings}\left(m, t\right) = \operatorname{Fin}\left(m + 3\right) \Rightarrow \operatorname{Perm}\left(\operatorname{Fin}\left(t + 3\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/Walks/MatchingCliqueCycle.Matchings` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

One arbitrary permutation of the labels is specified for each oriented successor edge, including the edge closing the cycle.

**Definition 1.3 (Matching transport).**

$$\forall m \in \mathrm{Nat},\; \forall t \in \mathrm{Nat},\; \forall M \in \operatorname{Matchings}\left(m, t\right),\; \forall x \in \operatorname{Vertex}\left(m, t\right),\; \operatorname{forward}\left(M, x\right) = \operatorname{pair}\left(\operatorname{fst}\left(x\right) + 1, \operatorname{applyMatching}\left(M, \operatorname{fst}\left(x\right), \operatorname{snd}\left(x\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/Walks/MatchingCliqueCycle.forward` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Forward transport advances the base position and applies that position's matching. Its inverse retreats and applies the inverse matching.

**Definition 1.4 (The actual finite graph).**

$$\forall m \in \mathrm{Nat},\; \forall t \in \mathrm{Nat},\; \forall M \in \operatorname{Matchings}\left(m, t\right),\; \forall x \in \operatorname{Vertex}\left(m, t\right),\; \forall y \in \operatorname{Vertex}\left(m, t\right),\; \operatorname{Adj}\left(\operatorname{graph}\left(M\right), x, y\right) \Leftrightarrow \left(\left(\operatorname{fst}\left(x\right) = \operatorname{fst}\left(y\right) \land x \ne y\right) \lor \left(\operatorname{forward}\left(M, x\right) = y \lor \operatorname{forward}\left(M, y\right) = x\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/Walks/MatchingCliqueCycle.graph` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Within a fiber all distinct vertices are adjacent. Between fibers the only edges are the specified matchings and their reverse orientations.

**Definition 1.5 (The maximal-independent-set spectrum).**

$$\forall V \in \mathrm{Type},\; [\operatorname{Fintype}\left(V\right)], [\operatorname{DecidableEq}\left(V\right)], \forall G \in \operatorname{SimpleGraph}\left(V\right),\; \forall k \in \mathrm{Nat},\; \operatorname{mem}\left(k, \operatorname{spectrum}\left(G\right)\right) \Leftrightarrow \left(\exists I \in \operatorname{Finset}\left(V\right),\; \operatorname{IsMaximalIndep}\left(G, I\right) \land \operatorname{card}\left(I\right) = k\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/Walks/MatchingCliqueCycle.spectrum` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The spectrum records cardinalities of actual finite independent vertex sets that dominate every omitted vertex. It uses the existing maximal-independent-set predicate.

**Lemma 1.6 (Distance in the base cycle).**

$$\forall (m : \mathrm{Nat}), \forall (i : \operatorname{Fin}\left(m + 3\right)), \forall (j : \operatorname{Fin}\left(m + 3\right)), \operatorname{dist}\left(\operatorname{cycleGraph}\left(m + 3\right), i, j\right) = \operatorname{WellCoveredPowerCliqueProduct.cycleMetric}\left(m + 3, i, j\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/MatchingCliqueCycle.cycle_distance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The distance between two cycle vertices is the smaller of their two circular separations.

**Theorem 1.7 (Projection and matching lifts bound distances).**

$$\forall m \in \mathrm{Nat},\; \forall t \in \mathrm{Nat},\; \forall M \in \operatorname{Matchings}\left(m, t\right),\; \forall x \in \operatorname{Vertex}\left(m, t\right),\; \forall y \in \operatorname{Vertex}\left(m, t\right),\; \operatorname{dist}\left(\operatorname{cycleGraph}\left(m + 3\right), \operatorname{fst}\left(x\right), \operatorname{fst}\left(y\right)\right) \le \operatorname{dist}\left(\operatorname{graph}\left(M\right), x, y\right) \land \operatorname{dist}\left(\operatorname{graph}\left(M\right), x, y\right) \le \operatorname{dist}\left(\operatorname{cycleGraph}\left(m + 3\right), \operatorname{fst}\left(x\right), \operatorname{fst}\left(y\right)\right) + 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/MatchingCliqueCycle.distance_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Projecting a walk discards internal fiber steps. Conversely, a shortest cycle walk transports a vertex along its matchings; at most one final step inside the destination clique reaches the desired endpoint.

**Theorem 1.8 (Maximal independent sets project).**

$$\forall m \in \mathrm{Nat},\; \forall t \in \mathrm{Nat},\; \forall M \in \operatorname{Matchings}\left(m, t\right),\; \forall d \in \mathrm{Nat},\; \forall I \in \operatorname{Finset}\left(\operatorname{Vertex}\left(m, t\right)\right),\; \left(1 \le d \land \operatorname{IsMaximalIndep}\left(\operatorname{power}\left(\operatorname{graph}\left(M\right), d\right), I\right)\right) \Rightarrow \left(\operatorname{IsMaximalIndep}\left(\operatorname{power}\left(\operatorname{cycleGraph}\left(m + 3\right), d - 1\right), \operatorname{imageFst}\left(I\right)\right) \land \operatorname{card}\left(\operatorname{imageFst}\left(I\right)\right) = \operatorname{card}\left(I\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/MatchingCliqueCycle.maximal_projection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An independent set in a positive graph power contains at most one point per fiber. If an omitted base fiber could extend the projected set, shortest matching paths in the two cyclic directions would forbid at most two labels there. The fiber has at least three labels, so the original set could be extended.

**Theorem 1.9 (Lawful maximal lifts exist).**

$$\forall m \in \mathrm{Nat},\; \forall t \in \mathrm{Nat},\; \forall M \in \operatorname{Matchings}\left(m, t\right),\; \forall d \in \mathrm{Nat},\; \forall S \in \operatorname{Finset}\left(\operatorname{Fin}\left(m + 3\right)\right),\; \left(1 \le d \land \operatorname{IsMaximalIndep}\left(\operatorname{power}\left(\operatorname{cycleGraph}\left(m + 3\right), d - 1\right), S\right)\right) \Rightarrow \left(\exists I \in \operatorname{Finset}\left(\operatorname{Vertex}\left(m, t\right)\right),\; \operatorname{IsMaximalIndep}\left(\operatorname{power}\left(\operatorname{graph}\left(M\right), d\right), I\right) \land \left(\operatorname{imageFst}\left(I\right) = S \land \operatorname{card}\left(I\right) = \operatorname{card}\left(S\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/MatchingCliqueCycle.maximal_lift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Among independent vertex sets supported over a given base independent set, choose one of maximal cardinality. The same two-label bound forces a representative in every specified fiber. Base maximality and the distance bound then dominate every omitted vertex. The projection is injective and preserves cardinality.

**Theorem 1.10 (All positive powers have the shifted spectrum).**

$$\forall m \in \mathrm{Nat},\; \forall t \in \mathrm{Nat},\; \forall M \in \operatorname{Matchings}\left(m, t\right),\; \forall d \in \mathrm{Nat},\; 1 \le d \Rightarrow \operatorname{spectrum}\left(\operatorname{power}\left(\operatorname{graph}\left(M\right), d\right)\right) = \operatorname{spectrum}\left(\operatorname{power}\left(\operatorname{cycleGraph}\left(m + 3\right), d - 1\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/MatchingCliqueCycle.spectrum_power` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Projection and lawful lift give both inclusions of the spectrum equality. At power one the base exponent is zero: the connected cycle has an edgeless zero-th power. The argument also applies when either power has become complete.

**Theorem 1.11 (The diameter is sharp).**

$$\forall m \in \mathrm{Nat},\; \forall t \in \mathrm{Nat},\; \forall M \in \operatorname{Matchings}\left(m, t\right),\; \operatorname{diam}\left(\operatorname{graph}\left(M\right)\right) = \operatorname{NatDiv}\left(m + 3, 2\right) + 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/MatchingCliqueCycle.diameter` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let D be the cycle diameter, half its length rounded down. Choose base vertices i and j at distance D and start at x=(i,0). Exclude from fiber j the second coordinates of the D-fold forward and inverse transports of x. At most two labels are excluded, so a label a remains. A walk from x to (j,a) of length at most D would project to a shortest cycle walk and end at one of those two excluded transports. Thus this actual vertex has distance greater than D, and the distance bound makes it exactly D+1.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/MatchingCliqueCycle.Matchings`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/MatchingCliqueCycle.Vertex`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/MatchingCliqueCycle.cycle_distance`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/MatchingCliqueCycle.diameter`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/MatchingCliqueCycle.distance_bounds`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/MatchingCliqueCycle.forward`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/MatchingCliqueCycle.graph`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/MatchingCliqueCycle.maximal_lift`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/MatchingCliqueCycle.maximal_projection`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/MatchingCliqueCycle.spectrum`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/MatchingCliqueCycle.spectrum_power`
- Dependency: [D5/S3/Combinatorics/Graph/WellCoveredPowerCliqueProduct](../WellCoveredPowerCliqueProduct.md)
