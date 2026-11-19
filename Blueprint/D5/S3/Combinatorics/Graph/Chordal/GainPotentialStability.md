# Stability of chordal group gain potentials

## Abstract

Uniform triangle defects bound simultaneous vertex-potential errors on finite chordal graphs.

Let V be a finite vertex type and H a group with a pseudometric invariant under both left and right multiplication. An oriented edge from i to j carries a label g(i,j). Reversing an edge inverts its label exactly. For each ordered triangle, the distance between g(i,j)g(j,k) and g(i,k) is at most a common nonnegative real number epsilon.

**Theorem 1.1 (A simultaneous approximate potential).**

$$\forall u \in \operatorname{Universe}\left(\right),\; \forall v \in \operatorname{Universe}\left(\right),\; \forall V \in \operatorname{Type}\left(u\right),\; \forall H \in \operatorname{Type}\left(v\right),\; [\operatorname{Finite}\left(V\right)] [\operatorname{Group}\left(H\right)] [\operatorname{PseudoMetricSpace}\left(H\right)] [\operatorname{IsIsometricSMul}\left(H, H\right)] [\operatorname{IsIsometricSMul}\left(\operatorname{MulOpposite}\left(H\right), H\right)], \forall G \in \operatorname{SimpleGraph}\left(V\right),\; (\operatorname{IsChordal}\left(G\right)) \Rightarrow (\forall g \in V \to \left(V \to H\right),\; \forall epsilon \in \operatorname{Real}\left(\right),\; (0 \le epsilon) \Rightarrow ((\forall i \in V,\; \forall j \in V,\; (\operatorname{Adj}\left(G, i, j\right)) \Rightarrow (\operatorname{g}\left(j, i\right) = \operatorname{inv}\left(\operatorname{g}\left(i, j\right)\right))) \Rightarrow ((\forall i \in V,\; \forall j \in V,\; \forall k \in V,\; (\operatorname{Adj}\left(G, i, j\right)) \Rightarrow ((\operatorname{Adj}\left(G, j, k\right)) \Rightarrow ((\operatorname{Adj}\left(G, i, k\right)) \Rightarrow (\operatorname{dist}\left(\operatorname{g}\left(i, j\right) \cdot \operatorname{g}\left(j, k\right), \operatorname{g}\left(i, k\right)\right) \le epsilon)))) \Rightarrow (\exists phi \in V \to H,\; \forall i \in V,\; \forall j \in V,\; (\operatorname{Adj}\left(G, i, j\right)) \Rightarrow (\operatorname{dist}\left(\operatorname{g}\left(i, j\right), \operatorname{inv}\left(\operatorname{phi}\left(i\right)\right) \cdot \operatorname{phi}\left(j\right)\right) \le \operatorname{NatToReal}\left(\operatorname{NatSub}\left(\operatorname{NatCard}\left(V\right), 2\right)\right) \cdot epsilon)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Chordal/GainPotentialStability.exists_approximate_gain_potential` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Here NatCard is the finite cardinality, NatSub denotes subtraction truncated at zero in the natural numbers, and NatToReal is the natural-number embedding into the reals. Thus the coefficient is exactly max(cardinality(V) minus two, zero). The assumptions IsIsometricSMul(H,H) and IsIsometricSMul(MulOpposite(H),H) express invariance under left and right translation. The existential quantifier selects one potential phi that satisfies the displayed error bound on every oriented edge simultaneously.

Induct on a finite set s of vertices, with error coefficient NatSub(cardinality(s),2). Chordality of the induced graph supplies a simplicial vertex x. Remove x and construct a potential psi on the remaining vertices. If x has no remaining neighbor, keep psi. Otherwise choose a neighbor w and set phi(x) = psi(w) times the inverse of g(x,w), leaving other values unchanged. This satisfies the edge from x to w exactly.

For another neighbor j distinct from w, simpliciality supplies the edge from w to j. The metric triangle inequality bounds the new edge error by the triangle defect at (x,w,j) plus the inherited error on (w,j). Left translation preserves that inherited distance. Since x,w,j are distinct, s has at least three vertices, and adding one to NatSub(cardinality(s) minus one,2) gives NatSub(cardinality(s),2). The opposite orientation has the same error because inversion is an isometry under the two translation assumptions. The inherited edges satisfy the enlarged bound by nonnegativity of epsilon.

The group may be noncommutative and may lie in an arbitrary universe. The graph may be empty or disconnected. Values of the total label function on nonedges and on the diagonal are unrestricted. The theorem assumes no completeness, compactness, finite group, diameter bound, or previously supplied potential. At epsilon zero the conclusion is zero distance on every edge; a pseudometric alone does not turn zero distance into equality. Equality follows when the pseudometric separates points.

The result is an existence and uniform error estimate for deterministic triangle constraints. It makes no assertion of optimality of the coefficient, statistical recovery, latent-state identification, or executable running time. Lerman and Shi, Robust Group Synchronization via Cycle-Edge Message Passing, https://arxiv.org/abs/1912.11347v3 , provides background on synchronization with bi-invariant metrics. Its corruption and iterative recovery models impose additional assumptions and do not supply this chordal triangle-only existence statement.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Chordal/GainPotentialStability.exists_approximate_gain_potential`
- Dependency: [D5/S3/Combinatorics/Graph/Chordal/Dirac](Dirac.md)
