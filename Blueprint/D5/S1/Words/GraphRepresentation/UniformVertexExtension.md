# Uniform Extension by One Vertex

## Abstract

A representation of a vertex deletion by two k-uniform words extends to the whole graph by two (k+1)-uniform words, with an arbitrary neighborhood.

All vertex types have decidable equality. Finite(V) means V has a finite enumeration; an empty V is allowed. Option(V) is the disjoint union of the old vertices some(a) and the fresh vertex none. Words are actual finite lists. The projection proj(a,b,w) deletes every other letter, preserving order and repetitions, using `D5/S1/Words/GraphRepresentation/ExplicitNonTwoUniform.twoProjection`. Natural numbers in the definition below include zero, but the positive condition restricts the representation class to k at least one. No connectedness, nonempty-carrier or neighborhood restriction is imposed.

**Definition 1.1 (Positive uniform projection-equality representation).**

$$\forall V: \operatorname{Type}, \forall k: \mathbb{N}, \forall G: \operatorname{SimpleGraph}\left(V\right), (\operatorname{InG}\left(k, G\right)) \iff ((0 < k) \land (\exists w,v: \operatorname{List}\left(V\right), (\forall a: V, \operatorname{count}\left(a, w\right) = k) \land ((\forall a: V, \operatorname{count}\left(a, v\right) = k) \land (\forall a: V, \forall b: V, (a \neq b) \implies ((\operatorname{Adj}\left(G, a, b\right)) \iff (\operatorname{proj}\left(a, b, w\right) = \operatorname{proj}\left(a, b, v\right)))))))$$

*Formalization.* `D5/S1/Words/GraphRepresentation/UniformVertexExtension.InG` (`✓ std3`).

*Citation.* Duncan Adamson, Amanita Dietz, Pamela Fleischmann, Annika Huch, and Silas Cato Sacher (2026). *2-word-π-representable Graphs*. URL: <https://arxiv.org/abs/2605.27183v1>.

*Commentary.*

Both count conditions quantify over every vertex of the same carrier. Their positivity ensures that both word alphabets equal that carrier. For every distinct pair, adjacency holds exactly when the ordered two-letter projections agree. SimpleGraph supplies symmetry and excludes loops.

**Theorem 1.2 (An arbitrary neighborhood costs at most one unit of uniformity).**

$$\forall V: \operatorname{Type}, (\operatorname{Finite}\left(V\right)) \implies (\forall k: \mathbb{N}, \forall G: \operatorname{SimpleGraph}\left(\operatorname{Option}\left(V\right)\right), (\operatorname{InG}\left(k, \operatorname{D}\left(G\right)\right)) \implies (\operatorname{InG}\left(k + 1, G\right)))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/GraphRepresentation/UniformVertexExtension.vertex_extension` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Duncan Adamson, Amanita Dietz, Pamela Fleischmann, Annika Huch, and Silas Cato Sacher (2026). *2-word-π-representable Graphs*. URL: <https://arxiv.org/abs/2605.27183v1>.

*Commentary.*

The graph D(G) is G.comap(some): its old vertices are V, with D(G).Adj(a,b) equivalent to G.Adj(some(a),some(b)). Choose its representing words w,v. Enumerate old nonneighbors of none once in N and old neighbors once in T. Put Q=NT and construct W=none^k w none NT and Z=none^k v N none T, mapping every old letter through some. Each old vertex occurs k+1 times and none occurs k+1 times in both lists. For an old pair, both projections append the same projection of Q, so right cancellation preserves equality and inequality. For a neighbor a, both fresh/old projections are none^k some(a)^k none some(a). For a nonneighbor a, Z instead projects to none^k some(a)^(k+1) none. After cancelling the common prefix none^k some(a)^k, the remaining heads are none and some(a), hence unequal. Symmetry handles reversed arguments. With no old vertices the words consist of k+1 copies of none.

This theorem supplies vertex extension. The all-positive-k adjacent strictness question also needs nonuniversality and a finite minimal nonmember argument; neither conclusion is asserted here.

## References

- Truth anchor: `D5/S1/Words/GraphRepresentation/ExplicitNonTwoUniform.twoProjection`
- Truth anchor: `D5/S1/Words/GraphRepresentation/UniformVertexExtension.InG`
- Truth anchor: `D5/S1/Words/GraphRepresentation/UniformVertexExtension.vertex_extension`
- Dependency: [D5/S1/Words/GraphRepresentation/ExplicitNonTwoUniform](ExplicitNonTwoUniform.md)
