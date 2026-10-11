# Uniform all-time clock avalanche

## Abstract

A clock for each ordered maximal face realizes every finite complex without ghost original vertices as the original slice of an actual parallel avalanche. The orbit is classified for every natural time, including its final facet and its empty firing tail.

**Definition 1.1 (outdegree).**

$$\forall W \in \operatorname{Type},\; [\operatorname{Fintype}\left(W\right)] [\operatorname{DecidableEq}\left(W\right)] \forall G \in \operatorname{Digraph}\left(W\right),\; [\operatorname{DecidableRel}\left(\operatorname{Adj}\left(G\right)\right)] \forall w \in W,\; \operatorname{outdegree}\left(G, w\right) = \operatorname{card}\left(\operatorname{filter}\left(\operatorname{Adj}\left(G, w\right), \operatorname{univ}\left(W\right)\right)\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/Sandpiles/UniformClockAvalanche.outdegree` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Henri Riihimäki, Jason P. Smith (2026). *Avalanche homology of digraphs via sandpile dynamics*. URL: <https://arxiv.org/abs/2606.26786v1>.

*Commentary.*

Out-degree counts actual outgoing arcs.

**Definition 1.2 (firing).**

$$\forall W \in \operatorname{Type},\; [\operatorname{Fintype}\left(W\right)] [\operatorname{DecidableEq}\left(W\right)] \forall G \in \operatorname{Digraph}\left(W\right),\; [\operatorname{DecidableRel}\left(\operatorname{Adj}\left(G\right)\right)] \forall c \in W \to \mathbb{N},\; \forall w \in W,\; w \in \operatorname{firing}\left(G, c\right) \Leftrightarrow \left(0 < \operatorname{outdegree}\left(G, w\right) \land \operatorname{outdegree}\left(G, w\right) \le c\left(w\right)\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/Sandpiles/UniformClockAvalanche.firing` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Henri Riihimäki, Jason P. Smith (2026). *Avalanche homology of digraphs via sandpile dynamics*. URL: <https://arxiv.org/abs/2606.26786v1>.

*Commentary.*

Every unstable vertex with positive out-degree fires once. This excludes all sinks even when they have accumulated grains.

**Definition 1.3 (step).**

$$\forall W \in \operatorname{Type},\; [\operatorname{Fintype}\left(W\right)] [\operatorname{DecidableEq}\left(W\right)] \forall G \in \operatorname{Digraph}\left(W\right),\; [\operatorname{DecidableRel}\left(\operatorname{Adj}\left(G\right)\right)] \forall c \in W \to \mathbb{N},\; \forall w \in W,\; \operatorname{step}\left(G, c, w\right) = c\left(w\right) - \operatorname{ite}\left(w \in \operatorname{firing}\left(G, c\right), \operatorname{outdegree}\left(G, w\right), 0\right) + \sum_{a \in W} \operatorname{ite}\left(a \in \operatorname{firing}\left(G, c\right) \land \operatorname{Adj}\left(G, a, w\right), 1, 0\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/Sandpiles/UniformClockAvalanche.step` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Henri Riihimäki, Jason P. Smith (2026). *Avalanche homology of digraphs via sandpile dynamics*. URL: <https://arxiv.org/abs/2606.26786v1>.

*Commentary.*

Subtraction uses eligibility in the old configuration, followed by one arrival along each arc from the old complete firing set. Arrivals cannot authorize same-time firing; sink coordinates are retained.

**Definition 1.4 (orbit).**

$$\forall W \in \operatorname{Type},\; [\operatorname{Fintype}\left(W\right)] [\operatorname{DecidableEq}\left(W\right)] \forall G \in \operatorname{Digraph}\left(W\right),\; [\operatorname{DecidableRel}\left(\operatorname{Adj}\left(G\right)\right)] \forall c \in W \to \mathbb{N},\; \forall t \in \mathbb{N},\; \operatorname{orbit}\left(G, c, t\right) = \operatorname{iterate}\left(\operatorname{step}\left(G\right), t, c\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/Sandpiles/UniformClockAvalanche.orbit` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Henri Riihimäki, Jason P. Smith (2026). *Avalanche homology of digraphs via sandpile dynamics*. URL: <https://arxiv.org/abs/2606.26786v1>.

*Commentary.*

The actual orbit iterates the synchronous transition; no firing schedule is an input.

**Definition 1.5 (avalanche).**

$$\forall W \in \operatorname{Type},\; [\operatorname{Fintype}\left(W\right)] [\operatorname{DecidableEq}\left(W\right)] \forall G \in \operatorname{Digraph}\left(W\right),\; [\operatorname{DecidableRel}\left(\operatorname{Adj}\left(G\right)\right)] \forall c \in W \to \mathbb{N},\; \forall T \in \operatorname{Finset}\left(W\right),\; T \in \operatorname{avalanche}\left(G, c\right) \Leftrightarrow \left(\operatorname{Nonempty}\left(T\right) \land \left(\exists t \in \mathbb{N},\; T \subseteq \operatorname{firing}\left(G, \operatorname{orbit}\left(G, c, t\right)\right)\right)\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/Sandpiles/UniformClockAvalanche.avalanche` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Henri Riihimäki, Jason P. Smith (2026). *Avalanche homology of digraphs via sandpile dynamics*. URL: <https://arxiv.org/abs/2606.26786v1>.

*Commentary.*

The native complex omits the empty face and takes the downward closure of actual firing sets at all natural times. Conventional augmentation adds only the empty face.

**Definition 1.6 (original).**

$$\forall V \in \operatorname{Type},\; \forall m \in \mathbb{N},\; \forall v \in V,\; \operatorname{original}\left(m, v\right) = \operatorname{inl}\left(\operatorname{inl}\left(v\right)\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/Sandpiles/UniformClockAvalanche.original` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Henri Riihimäki, Jason P. Smith (2026). *Avalanche homology of digraphs via sandpile dynamics*. URL: <https://arxiv.org/abs/2606.26786v1>.

*Commentary.*

Originals embed into the first summand of W = (V + Fin m) + Unit. Clock i is inl(inr i); the sink is inr(unit).

**Definition 1.7 (neighbours).**

$$\forall V \in \operatorname{Type},\; [\operatorname{DecidableEq}\left(V\right)] \forall m \in \mathbb{N},\; \forall F \in \operatorname{Fin}\left(m\right) \to \operatorname{Finset}\left(V\right),\; \forall w \in \operatorname{Sum}\left(\operatorname{Sum}\left(V, \operatorname{Fin}\left(m\right)\right), \operatorname{Unit}\right),\; \operatorname{neighbours}\left(F, w\right) = \operatorname{N}\left(F, w\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/Sandpiles/UniformClockAvalanche.neighbours` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Henri Riihimäki, Jason P. Smith (2026). *Avalanche homology of digraphs via sandpile dynamics*. URL: <https://arxiv.org/abs/2606.26786v1>.

*Commentary.*

N(F,o(v)) is the sink singleton. N(F,p(i)) is o[F(i)] together with p(i+1) when i+1<m and the sink otherwise. N(F,s) is empty. Distinct summands exclude loops and separate the successor from the facet.

**Definition 1.8 (clockGraph).**

$$\forall V \in \operatorname{Type},\; [\operatorname{DecidableEq}\left(V\right)] \forall m \in \mathbb{N},\; \forall F \in \operatorname{Fin}\left(m\right) \to \operatorname{Finset}\left(V\right),\; \forall a \in \operatorname{Sum}\left(\operatorname{Sum}\left(V, \operatorname{Fin}\left(m\right)\right), \operatorname{Unit}\right),\; \forall w \in \operatorname{Sum}\left(\operatorname{Sum}\left(V, \operatorname{Fin}\left(m\right)\right), \operatorname{Unit}\right),\; \operatorname{Adj}\left(\operatorname{clockGraph}\left(F\right), a, w\right) \Leftrightarrow w \in \operatorname{neighbours}\left(F, a\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/Sandpiles/UniformClockAvalanche.clockGraph` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Henri Riihimäki, Jason P. Smith (2026). *Avalanche homology of digraphs via sandpile dynamics*. URL: <https://arxiv.org/abs/2606.26786v1>.

*Commentary.*

Adjacency is membership in the actual outgoing neighbor set. Original out-degree is one; clock out-degree is the facet cardinality plus one; sink out-degree is zero.

**Definition 1.9 (initial).**

$$\forall V \in \operatorname{Type},\; [\operatorname{DecidableEq}\left(V\right)] \forall m \in \mathbb{N},\; \forall F \in \operatorname{Fin}\left(m\right) \to \operatorname{Finset}\left(V\right),\; \forall b \in V,\; \forall w \in \operatorname{Sum}\left(\operatorname{Sum}\left(V, \operatorname{Fin}\left(m\right)\right), \operatorname{Unit}\right),\; \operatorname{initial}\left(F, b, w\right) = \operatorname{C}\left(F, b, w\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/Sandpiles/UniformClockAvalanche.initial` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Henri Riihimäki, Jason P. Smith (2026). *Avalanche homology of digraphs via sandpile dynamics*. URL: <https://arxiv.org/abs/2606.26786v1>.

*Commentary.*

C(F,b,o(v)) is one exactly at b. C(F,b,p(i)) is |F(i)| + [i=0]. C(F,b,s)=0. No restriction on facet overlap, repetition, order, or the choice of b is imposed.

**Theorem 1.10 (uniform clock all time).**

$$\forall V \in \operatorname{Type},\; [\operatorname{Fintype}\left(V\right)] [\operatorname{DecidableEq}\left(V\right)] \forall K \in \operatorname{AbstractSimplicialComplex}\left(V\right),\; \forall m \in \mathbb{N},\; 1 \le m \Rightarrow \left(\forall f \in \operatorname{Fin}\left(m\right) \to \operatorname{facets}\left(K\right),\; \operatorname{Surjective}\left(f\right) \Rightarrow \left(\forall b \in V,\; \left(\left(\forall t \in \mathbb{N},\; \forall v \in V,\; \operatorname{orbit}\left(\operatorname{clockGraph}\left(\operatorname{values}\left(f\right)\right), \operatorname{initial}\left(\operatorname{values}\left(f\right), b\right), t\right)\left(\operatorname{original}\left(m, v\right)\right) = \operatorname{O}\left(\operatorname{values}\left(f\right), b, t, v\right)\right) \land \left(\forall t \in \mathbb{N},\; \forall i \in \operatorname{Fin}\left(m\right),\; \operatorname{orbit}\left(\operatorname{clockGraph}\left(\operatorname{values}\left(f\right)\right), \operatorname{initial}\left(\operatorname{values}\left(f\right), b\right), t\right)\left(\operatorname{clock}\left(i\right)\right) = \operatorname{P}\left(\operatorname{values}\left(f\right), t, i\right)\right)\right) \land \left(\left(\forall t \in \mathbb{N},\; \operatorname{firing}\left(\operatorname{clockGraph}\left(\operatorname{values}\left(f\right)\right), \operatorname{orbit}\left(\operatorname{clockGraph}\left(\operatorname{values}\left(f\right)\right), \operatorname{initial}\left(\operatorname{values}\left(f\right), b\right), t\right)\right) = \operatorname{S}\left(\operatorname{values}\left(f\right), b, t\right)\right) \land \left(\forall T \in \operatorname{Finset}\left(\operatorname{Sum}\left(\operatorname{Sum}\left(V, \operatorname{Fin}\left(m\right)\right), \operatorname{Unit}\right)\right),\; T \in \operatorname{avalanche}\left(\operatorname{clockGraph}\left(\operatorname{values}\left(f\right)\right), \operatorname{initial}\left(\operatorname{values}\left(f\right), b\right)\right) \Leftrightarrow \left(\operatorname{Nonempty}\left(T\right) \land \left(\left(\exists A \in \operatorname{Finset}\left(V\right),\; A \in K \land T = \operatorname{map}\left(\operatorname{original}\left(m\right), A\right)\right) \lor \left(\exists i \in \operatorname{Fin}\left(m\right),\; T \subseteq \operatorname{insert}\left(\operatorname{clock}\left(i\right), \operatorname{map}\left(\operatorname{original}\left(m\right), \operatorname{B}\left(\operatorname{values}\left(f\right), b, i\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Sandpiles/UniformClockAvalanche.uniform_clock_all_time` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Henri Riihimäki, Jason P. Smith (2026). *Avalanche homology of digraphs via sandpile dynamics*. URL: <https://arxiv.org/abs/2606.26786v1>.

*Commentary.*

Here F(i) is the underlying maximal face of f(i), and f is an arbitrary surjective ordered enumeration, permitting repetitions. O(F,b,0,v)=[v=b]; O(F,b,t,v)=[v in F(t-1)] for 1<=t<=m and zero thereafter. P(F,t,i)=|F(i)| for t<i, |F(i)|+1 for t=i, and zero for t>i. S(F,b,0)={o(b),p(0)}; S(F,b,t)=o[F(t-1)] union {p(t)} for 1<=t<m; S(F,b,m)=o[F(m-1)]; S(F,b,t) is empty for t>m. B(F,b,0)={b}, and B(F,b,i)=F(i-1) for i>0. The induction removes the current original indicator, replaces it by the active clock's facet indicator, and passes one grain only to the successor clock. At the last facet all clocks are zero; at every later time all nonsinks are zero, while the sink retains its accumulated grains. Maximal-face coverage identifies the original faces with K and the remaining generators with the clock attachment simplices. Every face containing the sink or two clocks is excluded. No topology, collapse, homology, or torsion conclusion is included.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Sandpiles/UniformClockAvalanche.avalanche`
- Truth anchor: `D5/S3/StatisticalMechanics/Sandpiles/UniformClockAvalanche.clockGraph`
- Truth anchor: `D5/S3/StatisticalMechanics/Sandpiles/UniformClockAvalanche.firing`
- Truth anchor: `D5/S3/StatisticalMechanics/Sandpiles/UniformClockAvalanche.initial`
- Truth anchor: `D5/S3/StatisticalMechanics/Sandpiles/UniformClockAvalanche.neighbours`
- Truth anchor: `D5/S3/StatisticalMechanics/Sandpiles/UniformClockAvalanche.orbit`
- Truth anchor: `D5/S3/StatisticalMechanics/Sandpiles/UniformClockAvalanche.original`
- Truth anchor: `D5/S3/StatisticalMechanics/Sandpiles/UniformClockAvalanche.outdegree`
- Truth anchor: `D5/S3/StatisticalMechanics/Sandpiles/UniformClockAvalanche.step`
- Truth anchor: `D5/S3/StatisticalMechanics/Sandpiles/UniformClockAvalanche.uniform_clock_all_time`
