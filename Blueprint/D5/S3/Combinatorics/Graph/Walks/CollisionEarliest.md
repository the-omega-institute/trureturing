# The earliest full-coverage edge collision

## Abstract

The earliest full-coverage edge collision is counted by n!: T(n,n+1)=n!.

**Theorem 1.1 (T(n, n+1) = n!).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/CollisionEarliest.earliest_count`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/CollisionEarliest.earliest_count` (`✓ std3`). ∎

*Citation.* Haobo Ma; Wenlin Zhang (2026). *Proof of Arkadeep Dutta's edge-collision ratio conjecture (OEIS A396659)*. DOI: [10.5281/zenodo.23885975](https://doi.org/10.5281/zenodo.23885975). URL: <https://zenodo.org/records/23885975>.

*Commentary.*

For every natural n and start v in Fin(n), collisionCount n v (n+1)=n!. A counted walk has n+2 vertices x(0),…,x(n+1) with x(0)=v. Its last edge repeats the edge at some i<n, so x(n)=x(i) and x(n+1)=x(i+1); hence the first n vertices already visit every vertex and form an ordering of Fin(n) starting at v. Conversely an ordering σ with σ(0)=v and any vertex a give the walk σ(0),…,σ(n−1),a,x(n+1), where x(n+1) is the successor of the position of a in σ (or a itself when that position is n−1); its first n edges have distinct tails, its last edge repeats the edge leaving the first visit to a, and it visits every vertex. The two constructions are inverse, and orderings with a fixed first value correspond to permutations of Fin(n−1) through Equiv.Perm.decomposeFin, giving (n−1)!·n=n!.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/CollisionEarliest.earliest_count`
- Dependency: [D5/S3/Combinatorics/Graph/Walks/CollisionPrefix](CollisionPrefix.md)
