# Induced lattice routing certificates

## Abstract

A sparse occupancy checker certifies injectivity and both directions of lattice adjacency.

Points are pairs of integers. Square adjacency means Manhattan distance one. The checker uses complete vertex and oriented-edge lists and a complete list of coordinate buckets. The supplied tree of every listed bucket must equal its actual successful fresh fill. Each bucket then checks outgoing edges locally; every spatial query selects the bucket of its queried coordinate, including across bucket boundaries. It neither assumes an embedding nor takes a certificate-correctness record as a hypothesis.

**Theorem 1.1 (Insertion records a fresh key and preserves old lookups).**

$$\forall V \in \mathrm{Type},\; \forall key \in \operatorname{List}\left(\mathrm{Bool}\right),\; \forall t \in \operatorname{Occupancy}\left(V\right),\; \forall r \in \operatorname{Occupancy}\left(V\right),\; \forall a \in V,\; \operatorname{insert}\left(t, key, a\right) = \operatorname{some}\left(r\right) \Rightarrow \left(\operatorname{read}\left(r, key\right) = \operatorname{some}\left(a\right) \land \left(\forall q \in \operatorname{List}\left(\mathrm{Bool}\right),\; \forall w \in V,\; \operatorname{read}\left(t, q\right) = \operatorname{some}\left(w\right) \Rightarrow \operatorname{read}\left(r, q\right) = \operatorname{some}\left(w\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Products/LatticeRouting.insert_spec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A successful insertion gives read(next,key)=some(v) and preserves every previous successful lookup. Occupied keys are rejected even when their stored value equals the proposed value. Induction on the key proves this invariant.

**Theorem 1.2 (Filling preserves occupancy and stores every listed vertex).**

$$\forall V \in \mathrm{Type},\; \forall key \in \operatorname{Function}\left(V, \operatorname{List}\left(\mathrm{Bool}\right)\right),\; \forall xs \in \operatorname{List}\left(V\right),\; \forall t \in \operatorname{Occupancy}\left(V\right),\; \forall r \in \operatorname{Occupancy}\left(V\right),\; \operatorname{fill}\left(key, xs, t\right) = \operatorname{some}\left(r\right) \Rightarrow \left(\left(\forall q \in \operatorname{List}\left(\mathrm{Bool}\right),\; \forall w \in V,\; \operatorname{read}\left(t, q\right) = \operatorname{some}\left(w\right) \Rightarrow \operatorname{read}\left(r, q\right) = \operatorname{some}\left(w\right)\right) \land \left(\forall a \in V,\; \operatorname{ListMem}\left(a, xs\right) \Rightarrow \operatorname{read}\left(r, \operatorname{apply}\left(key, a\right)\right) = \operatorname{some}\left(a\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Products/LatticeRouting.fill_spec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Successful fill preserves all old lookups and stores every a in xs at key(a). No injective hash assumption is needed: successful fresh insertion proves the needed uniqueness on the actual occupied vertices.

**Theorem 1.3 (Success proves an induced routing).**

$$\forall V \in \mathrm{Type},\; \forall B \in \mathrm{Type},\; [\operatorname{DecidableEq}\left(B\right)] \forall bucket \in \operatorname{Function}\left(\mathrm{Point}, B\right),\; \forall bs \in \operatorname{List}\left(B\right),\; \forall vs \in \operatorname{List}\left(V\right),\; \forall es \in \operatorname{List}\left(\operatorname{Prod}\left(V, V\right)\right),\; \forall c \in \operatorname{Function}\left(V, \mathrm{Point}\right),\; \forall G \in \operatorname{SimpleGraph}\left(V\right),\; [\operatorname{DecidableRel}\left(\operatorname{Adj}\left(G\right)\right)] \forall W \in \mathrm{Type},\; \forall trees \in \operatorname{Function}\left(B, \operatorname{Occupancy}\left(V\right)\right),\; \forall H \in \operatorname{SimpleGraph}\left(W\right),\; \forall f \in \operatorname{Function}\left(W, V\right),\; \left(\forall q \in \mathrm{Point},\; \operatorname{ListMem}\left(\operatorname{apply}\left(bucket, q\right), bs\right)\right) \Rightarrow \left(\left(\forall b \in B,\; \operatorname{ListMem}\left(b, bs\right) \Rightarrow \operatorname{bucketFill}\left(bucket, vs, c, b\right) = \operatorname{some}\left(\operatorname{apply}\left(trees, b\right)\right)\right) \Rightarrow \left(\operatorname{Injective}\left(f\right) \Rightarrow \left(\left(\forall a \in W,\; \operatorname{ListMem}\left(\operatorname{apply}\left(f, a\right), vs\right)\right) \Rightarrow \left(\left(\forall a \in W,\; \forall b \in W,\; \operatorname{Adj}\left(H, a, b\right) \Leftrightarrow \left(\operatorname{ListMem}\left(\operatorname{Pair}\left(\operatorname{apply}\left(f, a\right), \operatorname{apply}\left(f, b\right)\right), es\right) \lor \operatorname{ListMem}\left(\operatorname{Pair}\left(\operatorname{apply}\left(f, b\right), \operatorname{apply}\left(f, a\right)\right), es\right)\right)\right) \Rightarrow \left(\left(\forall a \in W,\; \forall b \in W,\; \operatorname{Adj}\left(G, \operatorname{apply}\left(f, a\right), \operatorname{apply}\left(f, b\right)\right) \Leftrightarrow \operatorname{Adj}\left(H, a, b\right)\right) \Rightarrow \left(\operatorname{routingCheck}\left(bucket, bs, vs, es, c, G, trees\right) = \mathrm{true} \Rightarrow \left(\operatorname{Injective}\left(\operatorname{comp}\left(c, f\right)\right) \land \left(\forall a \in W,\; \forall b \in W,\; \operatorname{Adj}\left(H, a, b\right) \Leftrightarrow \operatorname{squareAdj}\left(\operatorname{apply}\left(c, \operatorname{apply}\left(f, a\right)\right), \operatorname{apply}\left(c, \operatorname{apply}\left(f, b\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Products/LatticeRouting.routingCheck_sound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let f inject the vertices of H into the checked tag type of G. Every f(w) must occur in vs; H adjacency must be exactly the listed tag-pair inventory and must agree with G adjacency on the image of f. Every coordinate must select a listed bucket, and each supplied tree must equal the actual successful fresh fill of that bucket. If routingCheck is true, c composed with f is injective and preserves and reflects H adjacency. Edge checking proves the forward implication. Four spatial queries per occupied tag and the fill invariant prove the reverse implication. A retrieved hash-collision value is checked against its actual coordinate. The concrete consumer proves its tag injection and graph correspondence; neither is an assumed certificate-correctness record.

**Theorem 1.4 (The integral rotation preserves the required adjacency).**

$$\forall p \in \mathrm{Point},\; \forall q \in \mathrm{Point},\; \operatorname{kingAdj}\left(\operatorname{rotate}\left(p\right), \operatorname{rotate}\left(q\right)\right) \Leftrightarrow \operatorname{squareAdj}\left(p, q\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Products/LatticeRouting.rotation_adjacency` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

rotate(x,y)=(x+y+25,x-y+1705). The identity max(abs(a+b),abs(a-b))=abs(a)+abs(b) gives the exact equivalence, including all coordinate signs. The rotation is injective.

**Definition 1.5 (The actual strong product).**

$$\forall V \in \mathrm{Type},\; \forall W \in \mathrm{Type},\; \forall G \in \operatorname{SimpleGraph}\left(V\right),\; \forall H \in \operatorname{SimpleGraph}\left(W\right),\; \operatorname{strongProduct}\left(G, H\right):\operatorname{SimpleGraph}\left(\operatorname{Prod}\left(V, W\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/Products/LatticeRouting.strongProduct` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Adjacency is Mathlib boxProd adjacency or simultaneous adjacency in both factors. Thus one coordinate may stay fixed while the other follows an edge, or both may follow edges. This is the strong product required for king grids.

**Theorem 1.6 (Finite path factors give king adjacency).**

$$\forall n \in \mathrm{Nat},\; \forall m \in \mathrm{Nat},\; \forall p \in \operatorname{Prod}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(m\right)\right),\; \forall q \in \operatorname{Prod}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(m\right)\right),\; \operatorname{Adj}\left(\operatorname{strongProduct}\left(\operatorname{pathGraph}\left(n\right), \operatorname{pathGraph}\left(m\right)\right), p, q\right) \Leftrightarrow \operatorname{kingAdj}\left(\operatorname{Pair}\left(\operatorname{IntCast}\left(\operatorname{val}\left(\operatorname{fst}\left(p\right)\right)\right), \operatorname{IntCast}\left(\operatorname{val}\left(\operatorname{snd}\left(p\right)\right)\right)\right), \operatorname{Pair}\left(\operatorname{IntCast}\left(\operatorname{val}\left(\operatorname{fst}\left(q\right)\right)\right), \operatorname{IntCast}\left(\operatorname{val}\left(\operatorname{snd}\left(q\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Products/LatticeRouting.strong_paths_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For p,q in Fin n times Fin m, the strong product of the pinned Mathlib path graphs is adjacent exactly when the maximum absolute coordinate difference is one.

**Definition 1.7 (Convert inclusive bounds into a finite induced embedding).**

$$\forall V \in \mathrm{Type},\; \forall G \in \operatorname{SimpleGraph}\left(V\right),\; \forall c \in \operatorname{Function}\left(V, \mathrm{Point}\right),\; \operatorname{Injective}\left(c\right) \Rightarrow \left(\left(\forall a \in V,\; \forall b \in V,\; \operatorname{Adj}\left(G, a, b\right) \Leftrightarrow \operatorname{squareAdj}\left(\operatorname{apply}\left(c, a\right), \operatorname{apply}\left(c, b\right)\right)\right) \Rightarrow \left(\forall n \in \mathrm{Nat},\; \forall m \in \mathrm{Nat},\; \left(\forall a \in V,\; 1 \le \operatorname{fst}\left(\operatorname{rotate}\left(\operatorname{apply}\left(c, a\right)\right)\right) \land \left(\operatorname{fst}\left(\operatorname{rotate}\left(\operatorname{apply}\left(c, a\right)\right)\right) \le n \land \left(1 \le \operatorname{snd}\left(\operatorname{rotate}\left(\operatorname{apply}\left(c, a\right)\right)\right) \land \operatorname{snd}\left(\operatorname{rotate}\left(\operatorname{apply}\left(c, a\right)\right)\right) \le m\right)\right)\right) \Rightarrow \operatorname{GraphEmbedding}\left(G, \operatorname{strongProduct}\left(\operatorname{pathGraph}\left(n\right), \operatorname{pathGraph}\left(m\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/Products/LatticeRouting.oneBasedRectangleEmbedding` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Given coordinate injectivity, exact square adjacency and bounds 1 <= rotate(c(v)).x <= n and 1 <= rotate(c(v)).y <= m for every v, subtract one from both rotated coordinates and obtain a graph embedding into Fin n times Fin m. A graph embedding reflects as well as preserves adjacency. The bounds and local checker remain actual proof obligations in its concrete consumer.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Products/LatticeRouting.fill_spec`
- Truth anchor: `D5/S3/Combinatorics/Graph/Products/LatticeRouting.insert_spec`
- Truth anchor: `D5/S3/Combinatorics/Graph/Products/LatticeRouting.oneBasedRectangleEmbedding`
- Truth anchor: `D5/S3/Combinatorics/Graph/Products/LatticeRouting.rotation_adjacency`
- Truth anchor: `D5/S3/Combinatorics/Graph/Products/LatticeRouting.routingCheck_sound`
- Truth anchor: `D5/S3/Combinatorics/Graph/Products/LatticeRouting.strongProduct`
- Truth anchor: `D5/S3/Combinatorics/Graph/Products/LatticeRouting.strong_paths_iff`
