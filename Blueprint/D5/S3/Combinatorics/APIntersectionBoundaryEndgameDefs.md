# Arithmetic Progressions and Boundary Codes

## Abstract

Boundary arithmetic-progression families admit recoverable endpoint codes.

**Definition 1.1 (Arithmetic progression of fixed difference).**

$$\forall d \in \mathrm{Nat},\; \forall S \in \operatorname{Finset}\left(\mathrm{Nat}\right),\; \operatorname{IsAPDiff}\left(d, S\right) \Leftrightarrow \left(\exists a \in \mathrm{Nat},\; \exists n \in \mathrm{Nat},\; 0 < n \land S = \operatorname{apRange}\left(a, d, n\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/APIntersectionBoundaryEndgameDefs.IsAPDiff` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A set is a finite arithmetic progression of difference d when it consists of a positive number of consecutive d-spaced terms starting at some natural number. The difference may be zero in this fixed-difference predicate.

**Definition 1.2 (Nonempty arithmetic progression).**

$$\forall S \in \operatorname{Finset}\left(\mathrm{Nat}\right),\; \operatorname{IsAP}\left(S\right) \Leftrightarrow \left(\exists d \in \mathrm{Nat},\; 0 < d \land \operatorname{IsAPDiff}\left(d, S\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/APIntersectionBoundaryEndgameDefs.IsAP` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A finite set is an arithmetic progression if it has a positive common difference and at least one term. Singletons and two-point sets qualify.

**Definition 1.3 (Boundary single-difference bound).**

Lean statement: `D5/S3/Combinatorics/APIntersectionBoundaryEndgameDefs.claim`

*Formalization.* `D5/S3/Combinatorics/APIntersectionBoundaryEndgameDefs.claim` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Let F be a family of subsets of [1,N], and let d be positive. Suppose intersections of distinct members are nonempty arithmetic progressions, every member of size at least four is an arithmetic progression, and every member avoiding 1 has at least four terms and difference d. Then F has at most C(N,2)+1 members.

**Lemma 1.4 (Terminal triple is not a progression).**

Lean statement: `D5/S3/Combinatorics/APIntersectionBoundaryEndgameDefs.terminal_triple_not_ap`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/APIntersectionBoundaryEndgameDefs.terminal_triple_not_ap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive d and k at least three, the set consisting of 1 and the two consecutive terminal points 1+(k-1)d and 1+kd is not an arithmetic progression.

**Lemma 1.5 (Terminal pair separates an avoider).**

Lean statement: `D5/S3/Combinatorics/APIntersectionBoundaryEndgameDefs.terminal_avoider_disjoint`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/APIntersectionBoundaryEndgameDefs.terminal_avoider_disjoint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let a progression from 1 have at least four terms, and let a second progression have positive length and positive difference. If its two external neighbours are the first progression's two terminal points and its left neighbour is at least 2, the progressions are disjoint.

**Lemma 1.6 (Recover a left-blocked residue).**

Lean statement: `D5/S3/Combinatorics/APIntersectionBoundaryEndgameDefs.left_blocked_residue_recovery`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/APIntersectionBoundaryEndgameDefs.left_blocked_residue_recovery` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a positive common difference, two starts at least 2 whose left neighbours lie below 2 represent the same residue only when the starts agree. Equality of a point from each progression then also forces their indices to agree.

**Lemma 1.7 (Recover a right-blocked length).**

Lean statement: `D5/S3/Combinatorics/APIntersectionBoundaryEndgameDefs.right_blocked_length_recovery`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/APIntersectionBoundaryEndgameDefs.right_blocked_length_recovery` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At a fixed start and positive difference, two nonempty progressions whose final points do not exceed N and whose next points exceed N have the same length.

**Lemma 1.8 (Recover a progression without external neighbours).**

Lean statement: `D5/S3/Combinatorics/APIntersectionBoundaryEndgameDefs.avoider_no_neighbour_recovery`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/APIntersectionBoundaryEndgameDefs.avoider_no_neighbour_recovery` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Two nonempty progressions with the same positive difference, starts at least 2, and no external neighbour in [2,N] are equal if they intersect. Their shared point identifies the left-blocked residue, and the right boundary fixes the length.

**Lemma 1.9 (Separate triples from terminal pairs).**

Lean statement: `D5/S3/Combinatorics/APIntersectionBoundaryEndgameDefs.triple_terminal_separate`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/APIntersectionBoundaryEndgameDefs.triple_terminal_separate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In a family whose distinct members intersect in nonempty arithmetic progressions, a member of size three containing 1 cannot share its two other points with the terminal pair of a member of at least four terms starting at 1. The resulting triple would be a non-progression contained in the longer member.

**Lemma 1.10 (Uniqueness of the extra code).**

Lean statement: `D5/S3/Combinatorics/APIntersectionBoundaryEndgameDefs.none_code_separate`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/APIntersectionBoundaryEndgameDefs.none_code_separate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the boundary-family containment, intersection, and common-difference conditions, two distinct members cannot both receive the extra code. Members containing 1 would both be its singleton, while two members avoiding 1 would intersect as complete segments of the same residue class and hence coincide.

**Lemma 1.11 (Uniqueness of point codes).**

Lean statement: `D5/S3/Combinatorics/APIntersectionBoundaryEndgameDefs.point_code_separate`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/APIntersectionBoundaryEndgameDefs.point_code_separate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the same containment, intersection, and avoider conditions, two distinct members cannot receive the same point code. A two-point member containing 1 is separated from an avoider by intersection, and an avoider's available neighbour determines its progression.

## References

- Truth anchor: `D5/S3/Combinatorics/APIntersectionBoundaryEndgameDefs.IsAP`
- Truth anchor: `D5/S3/Combinatorics/APIntersectionBoundaryEndgameDefs.IsAPDiff`
- Truth anchor: `D5/S3/Combinatorics/APIntersectionBoundaryEndgameDefs.avoider_no_neighbour_recovery`
- Truth anchor: `D5/S3/Combinatorics/APIntersectionBoundaryEndgameDefs.claim`
- Truth anchor: `D5/S3/Combinatorics/APIntersectionBoundaryEndgameDefs.left_blocked_residue_recovery`
- Truth anchor: `D5/S3/Combinatorics/APIntersectionBoundaryEndgameDefs.none_code_separate`
- Truth anchor: `D5/S3/Combinatorics/APIntersectionBoundaryEndgameDefs.point_code_separate`
- Truth anchor: `D5/S3/Combinatorics/APIntersectionBoundaryEndgameDefs.right_blocked_length_recovery`
- Truth anchor: `D5/S3/Combinatorics/APIntersectionBoundaryEndgameDefs.terminal_avoider_disjoint`
- Truth anchor: `D5/S3/Combinatorics/APIntersectionBoundaryEndgameDefs.terminal_triple_not_ap`
- Truth anchor: `D5/S3/Combinatorics/APIntersectionBoundaryEndgameDefs.triple_terminal_separate`
