# Callan's A002067 hafnian and Dyck identities

## Abstract

Both of Callan's 2017 A002067 assertions hold for all natural indices, including the empty matching and empty path.

**Definition 1.1 (Hafnian of the constant-row array).**

$$\forall n: \mathbb{N}, \operatorname{hafnian}\left(n\right) = \sum_{M: \operatorname{SimpleGraph.Subgraph}\left((\operatorname{Top.top}: \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(2 \cdot n\right)\right))\right)} \operatorname{ite}\left(\operatorname{SimpleGraph.Subgraph.IsPerfectMatching}\left(M\right), \prod_{i: \operatorname{Fin}\left(2 \cdot n\right)} \prod_{j: \operatorname{Fin}\left(2 \cdot n\right)} \operatorname{ite}\left((i < j) \land (\operatorname{SimpleGraph.Subgraph.Adj}\left(M, i, j\right)), \operatorname{val}\left(i\right) + 1, 1\right), 0\right)$$

*Formalization.* `D5/S3/Combinatorics/PerfectMatchings/CallanA002067Hafnian.hafnian` (`✓ std3`).

*Citation.* David Callan (2017). *Two conjectures in OEIS A002067: hafnians and weighted Dyck paths*. URL: <https://oeis.org/A002067>.

*Commentary.*

OEIS A002067, Callan COMMENTS (unnumbered entry, no page number): "a(n) is the Hafnian of the triangular array (u(i,j))_{1 <= i < j <= 2n} with u(i,j)=i. The Hafnian is the same as the Pfaffian except without the alternating signs just as the permanent of a matrix is the determinant without the signs." A matching is a subgraph of the complete graph on Fin(2*n). Vertex i has source label i.val+1. The nested product includes each edge once, at its smaller endpoint; the empty product is one.

**Definition 1.2 (The two source assertions).**

$$claim = \left((\exists a: \mathbb{N} \to \mathbb{N}, \operatorname{CallanA002067Dyck.IsSourceSequence}\left(a\right)) \land (\forall a: \mathbb{N} \to \mathbb{N}, (\operatorname{CallanA002067Dyck.IsSourceSequence}\left(a\right)) \Rightarrow (\forall n: \mathbb{N}, (a\left(n\right) = \operatorname{hafnian}\left(n\right)) \land (a\left(n\right) = \operatorname{CallanA002067Dyck.weightedDyckSum}\left(n\right))))\right)$$

*Formalization.* `D5/S3/Combinatorics/PerfectMatchings/CallanA002067Hafnian.claim` (`✓ std3`).

*Citation.* David Callan (2017). *Two conjectures in OEIS A002067: hafnians and weighted Dyck paths*. URL: <https://oeis.org/A002067>.

*Commentary.*

OEIS A002067, Callan COMMENTS (unnumbered entry, no page number): "a(n) is the Hafnian of the triangular array (u(i,j))_{1 <= i < j <= 2n} with u(i,j)=i. The Hafnian is the same as the Pfaffian except without the alternating signs just as the permanent of a matrix is the determinant without the signs." "a(n) is the total weight of Dyck n-paths with weight defined as follows. Given a Dyck path, for each upstep, record its position in the path and the height of its upper endpoint; then multiply together all of these positions and heights. For example, the Dyck 4-path P = UUDUUDDD has upsteps in positions 1,2,4,5 ending at heights 1,2,2,3 respectively, and hence weight(P) = 480. (In fact the positions determine the heights because, for the k-th upstep, position + height = 2k.)" The proposition includes existence of the sequence and quantifies over every solution of the NAME recurrence and every n : Nat. Empty matching and path weights are one.

**Theorem 1.3 (Both identities for every index).**

$$(\exists a: \mathbb{N} \to \mathbb{N}, \operatorname{CallanA002067Dyck.IsSourceSequence}\left(a\right)) \land (\forall a: \mathbb{N} \to \mathbb{N}, (\operatorname{CallanA002067Dyck.IsSourceSequence}\left(a\right)) \Rightarrow (\forall n: \mathbb{N}, (a\left(n\right) = \operatorname{hafnian}\left(n\right)) \land (a\left(n\right) = \operatorname{CallanA002067Dyck.weightedDyckSum}\left(n\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PerfectMatchings/CallanA002067Hafnian.result` (`✓ std3`). ∎

*Resolves.* `Problems/callan-a002067` (proved) by `D5/S3/Combinatorics/PerfectMatchings/CallanA002067Hafnian.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"callan-a002067","declaration_gid":"D5/S3/Combinatorics/PerfectMatchings/CallanA002067Hafnian.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* David Callan (2017). *Two conjectures in OEIS A002067: hafnians and weighted Dyck paths*. URL: <https://oeis.org/A002067>.

*Commentary.*

Adjoining the largest label to an involution either creates a fixed point or joins it to an existing fixed point. The resulting weighted generating polynomial obeys derivative plus (r+1)X multiplication. Evaluation at zero retains precisely the fixed-point-free involutions, which correspond to perfect matchings. The same polynomial counts weighted Dyck paths and its even constant terms satisfy the source convolution.

## References

- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/CallanA002067Hafnian.claim`
- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/CallanA002067Hafnian.hafnian`
- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/CallanA002067Hafnian.result`
- Dependency: [D5/S0/Certificates/Combinatorics/DeformedJucysMurphyNoncommutation](../../../S0/Certificates/Combinatorics/DeformedJucysMurphyNoncommutation.md)
- Dependency: [D5/S3/Combinatorics/PerfectMatchings/CallanA002067Dyck](CallanA002067Dyck.md)
