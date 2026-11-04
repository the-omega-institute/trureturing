# Finite-orbit chain extended metrics

## Abstract

Finite actual equivalence classes of closed partial isometries give a chain extended metric with the original quotient topology.

Let I and J be types in independent universes and X an I-indexed family of types in a third universe. Each X(i) carries an extended metric, with values in ENNReal, the nonnegative reals together with infinity. Types denotes the appropriate universe of types; maps and dependent families retain these independent universes. Write Y(X) for the topological disjoint union, index(b) and point(b) for the two components of a point, and tag(i,x) for its tagged inclusion. No piece is assumed finite, nonempty, compact, complete or a length space.

A datum G consists of src,dst:J to I, closed subsets dom(j) of X(src(j)) and ran(j) of X(dst(j)), and a bijective isometry iso(j) between these subspaces. Thus ClosedPartialIsometryData(I,J,X) below denotes exactly the dependent record of these five fields together with their closed-domain and closed-range proofs. Empty generators, empty pieces, empty domains and self-identifications are allowed. The relation R is the full equivalence closure of the actual generator relation; finite orbit always means this entire class, including arbitrary finite words and inverses.

**Definition 1.1 (Closed partial isometry data).**

$$\forall I \in Types,\; \forall J \in Types,\; \forall X \in I \to Types,\; [\forall i \in I,\; EMetricSpace\left(X\left(i\right)\right)] Datum\left(I, J, X\right) = ClosedPartialIsometryData\left(I, J, X\right)$$

*Formalization.* `D5/S3/Topology/FiniteOrbitChainMetric.Datum` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The isometry is between the actual closed subspaces with their induced extended metrics. There is no noncollapse or topology-compatibility field.

**Definition 1.2 (The generating relation).**

$$\forall I \in Types,\; \forall J \in Types,\; \forall X \in I \to Types,\; [\forall i \in I,\; EMetricSpace\left(X\left(i\right)\right)] \forall G \in Datum\left(I, J, X\right),\; \forall a \in Y\left(X\right),\; \forall b \in Y\left(X\right),\; Step\left(G, a, b\right) \Leftrightarrow \left(\exists j \in J,\; \exists x \in dom\left(G, j\right),\; a = tag\left(src\left(G, j\right), val\left(x\right)\right) \land b = tag\left(dst\left(G, j\right), val\left(iso\left(G, j, x\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Topology/FiniteOrbitChainMetric.Step` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

One step uses a supplied generator at a point of its actual domain. Val forgets a subspace membership proof.

**Definition 1.3 (The full generated relation).**

$$\forall I \in Types,\; \forall J \in Types,\; \forall X \in I \to Types,\; [\forall i \in I,\; EMetricSpace\left(X\left(i\right)\right)] \forall G \in Datum\left(I, J, X\right),\; Rel\left(G\right) = EqvGen\left(Step\left(G\right)\right)$$

*Formalization.* `D5/S3/Topology/FiniteOrbitChainMetric.Rel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

EqvGen includes reflexivity, symmetry and transitivity without a bound on word length. O(G,a) denotes the set of all b in Y(X) for which Rel(G,a,b).

**Definition 1.4 (Finite chains and extended costs).**

$$\forall I \in Types,\; \forall J \in Types,\; \forall X \in I \to Types,\; [\forall i \in I,\; EMetricSpace\left(X\left(i\right)\right)] \forall G \in Datum\left(I, J, X\right),\; \forall a \in Y\left(X\right),\; Chain\left(G, a\right) = LeastChainFamily\left(G, a\right)$$

*Formalization.* `D5/S3/Topology/FiniteOrbitChainMetric.Chain` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

LeastChainFamily(G,a) is the least predicate on Y(X) times ENNReal closed under four rules: Chain(G,a,a,0); from Chain(G,a,tag(i,x),t), infer Chain(G,a,tag(i,y),t+edist(x,y)); from Chain(G,a,tag(src(j),val(x)),t) for x in dom(j), infer Chain(G,a,tag(dst(j),val(iso(j,x))),t); and from Chain(G,a,tag(dst(j),val(x)),t) for x in ran(j), infer Chain(G,a,tag(src(j),val(inverse(iso(j),x))),t). Every rule ranges over all its well-typed arguments. A finite derivation can have infinite cost.

**Definition 1.5 (The chain distance).**

$$\forall I \in Types,\; \forall J \in Types,\; \forall X \in I \to Types,\; [\forall i \in I,\; EMetricSpace\left(X\left(i\right)\right)] \forall G \in Datum\left(I, J, X\right),\; \forall a \in Y\left(X\right),\; \forall b \in Y\left(X\right),\; distance\left(G, a, b\right) = infimum\left(chainCosts\left(G, a, b\right)\right)$$

*Formalization.* `D5/S3/Topology/FiniteOrbitChainMetric.distance` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

ChainCosts(G,a,b) is the set of t in ENNReal satisfying Chain(G,a,b,t). Its infimum is taken in ENNReal; the empty infimum is infinity. In particular, infinity does not mean that there is no finite derivation.

**Theorem 1.6 (Short-chain capture and exact local balls).**

$$\forall I \in Types,\; \forall J \in Types,\; \forall X \in I \to Types,\; [\forall i \in I,\; EMetricSpace\left(X\left(i\right)\right)] [Fintype\left(J\right)] \forall G \in Datum\left(I, J, X\right),\; \forall a \in Y\left(X\right),\; Finite\left(O\left(G, a\right)\right) \Rightarrow \left(\exists rho \in ENNReal,\; 0 < rho \land \left(rho < \infty \land \left(\left(\forall b \in Y\left(X\right),\; \forall t \in ENNReal,\; \left(Chain\left(G, a, b, t\right) \land t < rho\right) \Rightarrow \left(\exists c \in X\left(index\left(b\right)\right),\; Rel\left(G, a, tag\left(index\left(b\right), c\right)\right) \land edist\left(c, point\left(b\right)\right) \le t\right)\right) \land \left(\forall b \in Y\left(X\right),\; \forall s \in ENNReal,\; \left(0 < s \land s < rho\right) \Rightarrow \left(distance\left(G, a, b\right) < s \Leftrightarrow \left(\exists c \in X\left(index\left(b\right)\right),\; Rel\left(G, a, tag\left(index\left(b\right), c\right)\right) \land edist\left(c, point\left(b\right)\right) < s\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/FiniteOrbitChainMetric.finite_orbit_local_model` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Only J and the actual orbit at a need be finite here. For each generator, the finitely many orbit centers outside its closed domain have a positive uniform separation from that domain; do the same for its closed range. Take the minimum of these finitely many positive radii and one. If an orbit center lies within this radius of a domain point, it belongs to the domain; the analogous implication holds for the range.

Induct on the actual chain, tracking an orbit center in the current piece at distance at most the accumulated cost. A paid step uses the triangle inequality. At a generator step the exclusion radius puts the center in the same domain, and the isometry transports both points without changing their distance; inverse steps use the closed range. For the local-ball formula, an infimum strictly below s supplies a chain of cost below s. Conversely a zero-cost relation chain followed by one paid step gives the required upper bound.

**Theorem 1.7 (An extended metric on the original quotient).**

$$\forall I \in Types,\; \forall J \in Types,\; \forall X \in I \to Types,\; [\forall i \in I,\; EMetricSpace\left(X\left(i\right)\right)] [Fintype\left(I\right)] [Fintype\left(J\right)] \forall G \in Datum\left(I, J, X\right),\; \left(\forall a \in Y\left(X\right),\; Finite\left(O\left(G, a\right)\right)\right) \Rightarrow \left(\exists m \in EMetricSpace\left(Q\left(G\right)\right),\; Topology\left(m\right) = quotientTopology\left(G\right) \land \left(\left(\forall a \in Y\left(X\right),\; \forall b \in Y\left(X\right),\; edist\left(m, q\left(G, a\right), q\left(G, b\right)\right) = distance\left(G, a, b\right)\right) \land \left(\left(\forall a \in Y\left(X\right),\; \forall b \in Y\left(X\right),\; distance\left(G, a, b\right) = 0 \Leftrightarrow Rel\left(G, a, b\right)\right) \land \left(\left(\forall a \in Y\left(X\right),\; \forall b \in Y\left(X\right),\; distance\left(G, a, b\right) = \infty \Leftrightarrow \neg (\exists t \in ENNReal,\; Chain\left(G, a, b, t\right) \land t < \infty)\right) \land \left(\forall i \in I,\; \forall x \in X\left(i\right),\; \forall y \in X\left(i\right),\; edist\left(m, q\left(G, tag\left(i, x\right)\right), q\left(G, tag\left(i, y\right)\right)\right) \le edist\left(x, y\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/FiniteOrbitChainMetric.chain_metric_on_original_quotient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Now both I and J are finite and every actual orbit is finite. Q(G) is Quotient(EqvGen.setoid(Step(G))); q(G,a) is the original quotient map and quotientTopology(G) is the quotient topology of the topological disjoint union before any new metric is installed. Topology(m) and edist(m) are the topology and distance of the displayed extended metric m. The last clause means every piece map is 1-Lipschitz for this same m.

If the chain distance is zero, short-chain capture puts the endpoint in the closure of its piece's finite orbit fiber. That fiber is closed, so the endpoint already belongs to the original equivalence class. Reverse chains and concatenation give symmetry and the triangle inequality; zero-cost relation chains make the distance invariant under replacing representatives. These facts construct the extended metric on the original quotient, without another zero-distance quotient.

For an open saturated set V in the original disjoint union and a in V, separate each finite orbit fiber from its piece's closed complement of V. The minimum of these finitely many separation radii and the capture radius is positive. Every smaller chain ball about a lies in V by capture. This proves that every original quotient-open set is metric-open. Conversely the one-step bound makes each piece map 1-Lipschitz, so every metric-open set has open preimage. Thus the topologies agree even for noncompact pieces.

A finite-cost chain bounds the infimum strictly below infinity, and an infimum strictly below infinity supplies a finite-cost chain. For a two-point piece whose distinct points have infinite distance and no generators, there is still a one-step chain of infinite cost. Identifying those two points by a closed singleton self-gluing instead makes their quotient distance zero. Hence the finite-cost qualifier is necessary and the piece maps need not be isometric embeddings.

The chain pseudometric construction is classical: Bridson and Haefliger, Metric Spaces of Non-Positive Curvature (1999), I.3 opening and I.5.18-5.19, allow infinity and describe the disjoint union and chain quotient. Their I.5.27-5.28 criterion explicitly assumes a saturated union of representative balls and equality of radial distances at related nearby points. The finite-orbit capture and noncompact topology argument above are deductions proved here, with no claim of novelty or verbatim reproduction of that criterion. Burago, Burago and Ivanov, A Course in Metric Geometry (2001), Definition 3.1.12 and Theorem 3.1.27 describe the chain semimetric; Exercise 3.1.14 gives topology equality under compactness and absence of extra identifications. It does not supply the general noncompact conclusion used here.

Application to a specified geometric realization still requires its actual pieces, closed partial isometries, full finite orbits, and an identification with its original marked quotient. The theorem alone asserts no geodesicity, cell isometric embedding, hyperbolic cone model, angle sum or curvature formula.

## References

- Truth anchor: `D5/S3/Topology/FiniteOrbitChainMetric.Chain`
- Truth anchor: `D5/S3/Topology/FiniteOrbitChainMetric.Datum`
- Truth anchor: `D5/S3/Topology/FiniteOrbitChainMetric.Rel`
- Truth anchor: `D5/S3/Topology/FiniteOrbitChainMetric.Step`
- Truth anchor: `D5/S3/Topology/FiniteOrbitChainMetric.chain_metric_on_original_quotient`
- Truth anchor: `D5/S3/Topology/FiniteOrbitChainMetric.distance`
- Truth anchor: `D5/S3/Topology/FiniteOrbitChainMetric.finite_orbit_local_model`
