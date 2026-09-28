# Boundary Arithmetic-Progression Intersection Bound

## Abstract

Boundary families with one common avoider difference satisfy the pair-count bound.

**Theorem 1.1 (At most one more member than unordered pairs).**

$$claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/APIntersectionBoundaryEndgame.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive d and a family F of subsets of [1,N], suppose distinct members intersect in nonempty arithmetic progressions, members of size at least four are arithmetic progressions, and members avoiding 1 have at least four terms and difference d. Then |F| is at most C(N,2)+1. Code each member by a point of [2,N], a pair from [2,N], or one extra value. The code is injective: equal extra codes, equal point codes, and equal pair codes are excluded. For pair codes, the six unordered cases are triple with triple, triple with longer boundary progression, triple with avoider, two longer boundary progressions, longer boundary progression with avoider, and two avoiders.

## References

- Truth anchor: `D5/S3/Combinatorics/APIntersectionBoundaryEndgame.result`
- Dependency: [D5/S3/Combinatorics/APIntersectionBoundaryEndgameDefs](APIntersectionBoundaryEndgameDefs.md)
