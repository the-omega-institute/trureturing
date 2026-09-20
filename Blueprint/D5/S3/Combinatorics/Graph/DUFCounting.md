# Two incidence counts and the codegree-four bound

## Abstract

Let H be a finite family of subsets of an n-element vertex type, m=card(H), and P=binom(n,2). The counts are defined for every H and include absent ground pairs; write hi=h(H,i) and qi=q(H,i). The cap means at most four neighbors per ground pair. Under the hypotheses stated below, fiber and incidence counts yield the bounds and exact correction identity.

**Definition 1.1 (Codegree distribution).**

Lean statement: `D5/S3/Combinatorics/Graph/DUFCounting.h`

*Formalization.* `D5/S3/Combinatorics/Graph/DUFCounting.h` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

h(H,i) counts ground pairs with exactly i neighbors. In particular h0 includes absent pairs.

**Definition 1.2 (Common-link size distribution).**

Lean statement: `D5/S3/Combinatorics/Graph/DUFCounting.q`

*Formalization.* `D5/S3/Combinatorics/Graph/DUFCounting.q` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

q(H,i) counts ground pairs whose common link has exactly i edges. The count includes q0.

**Definition 1.3 (Small nonempty fibers).**

Lean statement: `D5/S3/Combinatorics/Graph/DUFCounting.a`

*Formalization.* `D5/S3/Combinatorics/Graph/DUFCounting.a` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

a(H) counts four-element sets S for which the exact neighborhood fiber has one or two edges.

**Definition 1.4 (Four-edge fibers).**

Lean statement: `D5/S3/Combinatorics/Graph/DUFCounting.b`

*Formalization.* `D5/S3/Combinatorics/Graph/DUFCounting.b` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

b(H) counts four-element sets S whose exact neighborhood fiber has four edges. Under DUF and the cap these fibers are four-edge stars.

**Theorem 1.5 (The fiber correction).**

Lean statement: `D5/S3/Combinatorics/Graph/DUFCounting.fiber_counts`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/DUFCounting.fiber_counts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For H satisfying DUF and the cap, q4+a=h4+2b, 4b<=h4, and 2q4<=3h4. Each fiber F(S) with card(S)=4 and k=card(F(S)) contributes binom(k,2) wedges and k codegree-four pairs; k is at most four.

**Theorem 1.6 (The two actual incidence sums).**

Lean statement: `D5/S3/Combinatorics/Graph/DUFCounting.incidence_counts`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/DUFCounting.incidence_counts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a three-uniform H, the sum over ground pairs of card(N(p)) is 3m. The sum of binom(card(N(p)),2) equals the sum of card(K(q)); both sums also range over all ground pairs. The first equality counts pair-triple incidences; the second counts ordered incidences (p,q) with q contained in N(p).

**Theorem 1.7 (The bound and the fiber identity).**

Lean statement: `D5/S3/Combinatorics/Graph/DUFCounting.counting_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/DUFCounting.counting_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a three-uniform DUF family with maximum pair codegree at most four, 21m+10h0+3h1+h3<=22P. Also 6m+a+q2+2q1+3q0+h1+3h0=6P+2b. These are additive natural-number formulas, so they remain valid when m<P without interpreting truncated subtraction as a signed difference.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/DUFCounting.a`
- Truth anchor: `D5/S3/Combinatorics/Graph/DUFCounting.b`
- Truth anchor: `D5/S3/Combinatorics/Graph/DUFCounting.counting_bound`
- Truth anchor: `D5/S3/Combinatorics/Graph/DUFCounting.fiber_counts`
- Truth anchor: `D5/S3/Combinatorics/Graph/DUFCounting.h`
- Truth anchor: `D5/S3/Combinatorics/Graph/DUFCounting.incidence_counts`
- Truth anchor: `D5/S3/Combinatorics/Graph/DUFCounting.q`
- Dependency: [D5/S3/Combinatorics/Graph/DUFWedges](DUFWedges.md)
