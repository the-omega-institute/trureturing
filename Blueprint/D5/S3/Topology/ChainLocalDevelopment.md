# Local developments across original gluing faces

## Abstract

Source maps that are short near a complete orbit give lower bounds for the original global chain distance, including chains through paired faces.

Let I and J be types in independent universes, X an I-indexed family of extended metric spaces, and A(X) their original disjoint union. The datum G is FiniteOrbitChainMetric.Datum. Write Rel(G,a,b) for its complete original equivalence relation and delta(G,x,y) for the infimum of costs of all original finite chains from x to y. Paid source moves have their original extended distance as cost; either direction of an actual gluing costs zero.

Let Y be an extended metric space and f:A(X) to Y. Respects(G,f) means that Rel(G,b,c) implies f(b)=f(c) for every pair b,c. For a in A(X), Short(G,a,f,R) means the following for every source piece i and every c in X(i) related to a: for every x,y in X(i) with edist(c,x)<R and edist(c,y)<R, edist(f(i,x),f(i,y)) is at most edist(x,y). No distance bound is assumed for a source move outside these balls.

Guard(G,a,R) is the conjunction of two incidence conditions. For every generator j, every center c in its source piece related to a, and every x in its actual domain, edist(c,x)<R implies that c also lies in that domain. The second condition replaces source and domain by target and actual range. Both conditions use every actual generator, including inverse moves and self-gluings.

For x in A(X), first(x) is its source index and second(x) its original point. The expression Point(i,c) denotes the corresponding point of A(X). A radius r in NNReal is finite when viewed as an extended real, and all extended-distance comparisons below use that coercion.

**Theorem 1.1 (The developed distance bounds every original chain).**

$$\forall I \in Types,\; \forall J \in Types,\; \forall X \in I \to Types,\; [\forall i \in I,\; EMetricSpace\left(X\left(i\right)\right)] \forall G \in Datum\left(I, J, X\right),\; \forall Y \in Types,\; [EMetricSpace\left(Y\right)] \forall f \in A\left(X\right) \to Y,\; \forall a \in A\left(X\right),\; \forall r \in NNReal,\; \forall x \in A\left(X\right),\; \forall y \in A\left(X\right),\; \forall c \in X\left(first\left(x\right)\right),\; \forall d \in X\left(first\left(y\right)\right),\; \left(Respects\left(G, f\right) \land \left(0 < r \land \left(Short\left(G, a, f, 3 r\right) \land \left(Guard\left(G, a, 3 r\right) \land \left(Rel\left(G, a, Point\left(first\left(x\right), c\right)\right) \land \left(Rel\left(G, a, Point\left(first\left(y\right), d\right)\right) \land \left(edist\left(c, second\left(x\right)\right) < r \land edist\left(d, second\left(y\right)\right) < r\right)\right)\right)\right)\right)\right)\right) \Rightarrow edist\left(f\left(x\right), f\left(y\right)\right) \le delta\left(G, x, y\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/ChainLocalDevelopment.local_development_distance_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The two endpoints may lie near different representatives of the complete orbit, and chains may cross the actual gluing faces. The hypotheses do not require finite index types, compact pieces, finite diameter or an attained chain infimum. They explicitly require the local incidence guards; this statement does not construct a radius satisfying those guards.

Put a source center beside the starting point and follow it through a chain of cost less than 2r. At every stage its source displacement to the current endpoint is at most the initial displacement plus the accumulated cost, hence less than 3r. A paid move therefore has both endpoints in the same controlled source ball, where Short bounds its developed distance. At a forward gluing the domain guard places the center in the same actual domain, so the partial isometry transports it and preserves its displacement. The range guard does the same for an inverse gluing. Respects makes the developed point unchanged across either gluing. Induction bounds the developed endpoint distance by the accumulated cost for every finite chain, without a length bound.

Each endpoint develops within r of f(a), since its nearby orbit center has the same f-value as a. Their developed distance is therefore less than 2r. Any original chain cheaper than that distance falls under the preceding estimate and contradicts it. Taking the infimum over all original chains gives the displayed lower bound.

This is a sufficient lower-bound principle for a local model. It does not assert equality of model and quotient distances. A local isometry also needs a reverse comparison, for example by lifting sufficiently short model paths into compatible source pieces. Constructing hyperbolic charts, checking their actual face transports and local nonexpansion, and supplying their incidence guards are additional geometric conditions.

## References

- Truth anchor: `D5/S3/Topology/ChainLocalDevelopment.local_development_distance_le`
- Dependency: [D5/S3/Topology/FiniteOrbitChainMetric](FiniteOrbitChainMetric.md)
