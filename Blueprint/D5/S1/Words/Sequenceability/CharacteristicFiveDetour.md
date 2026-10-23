# Characteristic-five relative paths

## Abstract

Three cuts join the two row-lift cycles into an exact relative path.

Let K be any finite field of characteristic five and let u be nonzero. Write B for the vectors (a,h) in ZMod(5) times K with a nonzero. All directed labels are differences of actual vertices with coefficient one.

**Theorem 1.1 (A path with exact vertices, labels and bounded sums).**

$$\forall K \in \operatorname{Type}\left(\right),\; [\operatorname{Field}\left(K\right)] [\operatorname{Finite}\left(K\right)] [\operatorname{CharP}\left(K, 5\right)] \forall u \in K,\; u \ne 0 \Rightarrow \operatorname{let} M=4\cdot\operatorname{card}\left(K\right) + 1;\exists v \in \operatorname{Nat}\left(\right)\to \operatorname{ZMod}\left(5\right) \times K,\; \operatorname{v}\left(0\right) = (0,0) \land \left(\operatorname{v}\left(M\right) = (0,u) \land \left(\operatorname{Injective}\left((n:\operatorname{Fin}\left(M + 1\right)\mapsto \operatorname{v}\left(\operatorname{val}\left(n\right)\right))\right) \land \left(\operatorname{BijOn}\left(v, \operatorname{Ioo}\left(0, M\right), \{z:\operatorname{ZMod}\left(5\right) \times K\mid\operatorname{fst}\left(z\right) \ne 0\}\right) \land \left(\operatorname{BijOn}\left((n:\operatorname{Nat}\left(\right)\mapsto \operatorname{v}\left(n + 1\right) - \operatorname{v}\left(n\right)), \operatorname{Iio}\left(M\right), \{z:\operatorname{ZMod}\left(5\right) \times K\mid\operatorname{fst}\left(z\right) \ne 0\}\cup\{(0,u)\}\right) \land \left(\operatorname{Injective}\left((k:\operatorname{Fin}\left(M + 1\right)\mapsto \sum_{i<\operatorname{val}\left(k\right)}(\operatorname{v}\left(i + 1\right) - \operatorname{v}\left(i\right)))\right) \land \left(\left(\forall a \in \operatorname{Nat}\left(\right),\; \forall b \in \operatorname{Nat}\left(\right),\; \left(a < b \land b \le M\right) \Rightarrow \sum_{a\le i<b}(\operatorname{v}\left(i + 1\right) - \operatorname{v}\left(i\right)) \ne 0\right) \land \sum_{i<M}(\operatorname{v}\left(i + 1\right) - \operatorname{v}\left(i\right)) = (0,u)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Sequenceability/CharacteristicFiveDetour.exists_characteristic_five_relative_path` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The path has M+1=4*card(K)+2 distinct vertices and M=4*card(K)+1 edges. Its endpoints are (0,0) and (0,u). BijOn on the open interval of indices means that the interior contains every vector of B exactly once. BijOn for the edge differences means that their inventory is exactly B together with the single label (0,u), each once. Every prefix through the full endpoint is distinct, including the empty prefix. Every nonempty interval, including the whole path, has nonzero sum, and the total is (0,u). Values of v beyond index M are unrestricted.

Use the row lift with center 4u and quotient columns (1,2,4,3). Its carrier phases 0,1,2,3 denote those four column values, respectively. The removed edges are (1,2u) to (2,3u), (2,u) to (4,4u), and (4,3u) to (3,2u). Their labels are (1,u), (2,3u), and (4,4u). The middle removed edge lies on the small row-lift cycle; the first and third lie on the other cycle.

On the carrier (Fin(4) times K) plus Fin(2), extend the lift P by fixing s and t. In phase coordinates set h=(1,3u), j=(2,4u), k=(3,2u); their actual group coordinates are (2,3u), (4,4u), (3,2u). Take Q=swap(h,s)*swap(h,t)*swap(j,k)*P, with the rightmost action first. Swapping the two attachments merges the disjoint old cycles. The next two swaps insert the fixed points t and s. A first-return argument also applies to singleton cycles and leaves unrelated ambient cycles alone. Thus Q is one cycle on the full carrier.

Read the orbit of Q from s through t, and omit its closing edge t to s. The four new joins have labels (2,3u), (0,u), (1,u), and (4,4u). The first, third and fourth replace the three removed old labels once each. An explicit permutation of the three cut tails and s proves the punctured difference bijection. The closing label (0,-u) is excluded. Orbit injectivity and its exact period identify t as the last vertex. Telescoping then gives the prefix, interval and total clauses.

This relative path can replace an edge of an existing path in the zero column: translate it to the chosen edge's source, so its last vertex is the old target. The interior stays outside the zero column, and the replacement adds every outside label. A prime seed, the branch for primes at least seven, insertion in a complete induction, and transport to arbitrary original coordinates require their own proofs.

## References

- Truth anchor: `D5/S1/Words/Sequenceability/CharacteristicFiveDetour.exists_characteristic_five_relative_path`
- Dependency: [D5/S1/Words/Sequenceability/RowOrbitLift](RowOrbitLift.md)
- Dependency: [D5/S3/Combinatorics/PerfectMatchings/WeightedReattachment](../../../S3/Combinatorics/PerfectMatchings/WeightedReattachment.md)
