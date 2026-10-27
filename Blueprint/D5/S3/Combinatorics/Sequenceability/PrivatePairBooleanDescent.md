# Exact Boolean coverage descent at a private pair

## Abstract

Exact Boolean coverage descent at a private pair

**Theorem 1.1 (An interval avoiding a separator lies on one side).**

$$\forall X \in \operatorname{Type}\left(\right),\; \forall a \in X,\; \forall t \in \operatorname{List}\left(X\right),\; \forall l \in \operatorname{List}\left(X\right),\; \forall r \in \operatorname{List}\left(X\right),\; \left(\operatorname{IsInfix}\left(t, \operatorname{append}\left(l, \operatorname{cons}\left(a, r\right)\right)\right) \land \left(\neg a \in t\right)\right) \Rightarrow \left(\operatorname{IsInfix}\left(t, l\right) \lor \operatorname{IsInfix}\left(t, r\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Sequenceability/PrivatePairBooleanDescent.infix_avoid_separator` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary lists l,r,t and a coordinate a, if t is an interval of l ++ a::r and does not contain a, then t is an interval of l or r. This includes the empty interval. No decidable equality or duplicate-free premise is required.

**Theorem 1.2 (A private pair preserves every reduced permutation).**

$$\forall X \in \operatorname{Type}\left(\right),\; \forall inst \in \operatorname{DecidableEq}\left(X\right),\; \forall M \in \operatorname{Submodule}\left(\mathbb{Z}, \operatorname{Function}\left(X, \mathbb{Z}\right)\right),\; \forall E \in \operatorname{Finset}\left(X\right),\; \forall S \in \operatorname{Finset}\left(X\right),\; \forall u \in X,\; \forall v \in X,\; \left(\operatorname{Covers}\left(M, E\right) \land \left(\operatorname{Minimal}\left(M, E, S\right) \land \left(3 \le \operatorname{card}\left(S\right) \land \left(u \in S \land \left(v \in S \land \left(u \ne v \land \left(\forall B \in \operatorname{Finset}\left(X\right),\; \left(\operatorname{Minimal}\left(M, E, B\right) \land \left(u \in B \lor v \in B\right)\right) \Rightarrow B = S\right)\right)\right)\right)\right)\right)\right) \Rightarrow \left(\operatorname{Covers}\left(M, \operatorname{erase}\left(\operatorname{erase}\left(E, u\right), v\right)\right) \land \left(\operatorname{card}\left(\operatorname{erase}\left(\operatorname{erase}\left(E, u\right), v\right)\right) + 2 = \operatorname{card}\left(E\right) \land \left(\left(\forall z \in \operatorname{Function}\left(\operatorname{erase}\left(\operatorname{erase}\left(E, u\right), v\right), \mathbb{Z}\right),\; z \in \operatorname{reducedSpan}\left(M, \operatorname{erase}\left(\operatorname{erase}\left(E, u\right), v\right)\right) \Rightarrow \operatorname{embed}\left(\operatorname{erase}\left(\operatorname{erase}\left(E, u\right), v\right), z\right) \in M\right) \land \left(\left(\forall B \in \operatorname{Finset}\left(\operatorname{erase}\left(\operatorname{erase}\left(E, u\right), v\right)\right),\; \left(\operatorname{Nonempty}\left(B\right) \land B \ne \operatorname{univ}\left(\right)\right) \Rightarrow \left(\operatorname{row}\left(B\right) \in \operatorname{reducedSpan}\left(M, \operatorname{erase}\left(\operatorname{erase}\left(E, u\right), v\right)\right) \Leftrightarrow \operatorname{row}\left(\operatorname{image}\left(\operatorname{val}\left(\right), B\right)\right) \in M\right)\right) \land \left(\left(\forall i \in \operatorname{erase}\left(\operatorname{erase}\left(E, u\right), v\right),\; \operatorname{embed}\left(\operatorname{erase}\left(\operatorname{erase}\left(E, u\right), v\right), \operatorname{single}\left(i, 1\right)\right) = \operatorname{single}\left(\operatorname{val}\left(i\right), 1\right)\right) \land \left(\forall i \in \operatorname{erase}\left(\operatorname{erase}\left(E, u\right), v\right),\; \forall j \in \operatorname{erase}\left(\operatorname{erase}\left(E, u\right), v\right),\; \operatorname{embed}\left(\operatorname{erase}\left(\operatorname{erase}\left(E, u\right), v\right), \operatorname{single}\left(i, 1\right) - \operatorname{single}\left(j, 1\right)\right) = \operatorname{single}\left(\operatorname{val}\left(i\right), 1\right) - \operatorname{single}\left(\operatorname{val}\left(j\right), 1\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Sequenceability/PrivatePairBooleanDescent.private_pair_exact_boolean_descent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

M is an integer submodule of functions on the unchanged original indices. Complete M E consists of all nonempty proper subsets of the finite original ground set E whose coefficient-one Boolean rows lie in M. Covers quantifies over every duplicate-free literal list enumerating E, with an actual nonempty proper contiguous interval. Minimal is inclusion minimality in that complete family. Only the selected support S has cardinality at least three; the other minimal supports can have arbitrary cardinalities. The distinct original indices u,v lie in S and in no other minimal member.

For a row A containing a private index, choose a minimal nonempty Boolean row B inside A. If B contains that index, privacy identifies B with S. Otherwise subtract its actual Boolean row and recurse on A minus B. The strict finite descent proves S is contained in A. Thus every complete row meeting u or v contains u,v and an actual retained x in S minus {u,v}. All larger mixed rows remain in scope.

Write Y = E minus {u,v}. For each given reduced order b, split on actual membership of row Y in M. If it is absent, apply original coverage to (u,b,v). A covering row meeting the deleted pair contains both endpoints and is full, a contradiction. An avoiding row is an interval of b, and cannot be full Y by the membership split.

If row Y belongs to M, rotate the given b just after x, obtaining (c1,...,x), and apply original coverage to (u,c1,v,c2,...,x). A row meeting the pair contains both endpoints u,x and is full. An avoiding row lies inside one of two proper pieces. The existing ZeroTotalCircleGood.rotated_two_runs supplier makes either that run or its complement an interval of the SAME original b. The exact identity row(complement) = row(Y) - row(run) gives membership in M. Both witnesses are nonempty and proper; full Y is excluded even in this second case. The reduced length two boundary is included.

The reducedSpan definition is exactly the integer span of ALL proper reduced Boolean rows whose extension by zero belongs to M. Its image under embed lies in M. Conversely every nonempty proper reduced Boolean row with image in M is a generator, so this is its complete proper Boolean family. Extension sends a unit and a difference to the same coefficient-one original coordinate vectors. No equality with an intersection lattice, rational saturation, division, original total-sum or torsion assumption is asserted.

For the original source family H, instantiate M with Submodule.span over integer Boolean rows of H. Original H coverage implies Covers because each source row is a generator. Each output image in M therefore has finite ORIGINAL-H integer coefficients, by Mathlib's Submodule.mem_span_image_finset_iff_exists_fun. For an original interval source A, the direct witness has its original generator coefficients; the complement witness subtracts those coefficients from an actual certificate for row Y. Finite linear combinations compose these coefficients. This exact application is compiled transiently rather than retained as a named binding theorem.

This is a repository-derived descent lemma. The unrestricted original connector, Good and adaptive merge statements remain open. No forest constructor or literature-priority claim is part of this delivery.

## References

- Truth anchor: `D5/S3/Combinatorics/Sequenceability/PrivatePairBooleanDescent.infix_avoid_separator`
- Truth anchor: `D5/S3/Combinatorics/Sequenceability/PrivatePairBooleanDescent.private_pair_exact_boolean_descent`
- Dependency: [D5/S3/Combinatorics/Sequenceability/ZeroTotalCircleGood](ZeroTotalCircleGood.md)
