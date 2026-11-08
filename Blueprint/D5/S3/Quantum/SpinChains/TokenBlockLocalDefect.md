# Outside-occupancy coordinates for the local Boolean defect

## Abstract

The original complex subset carrier splits by actual outside occupied sets, with additive source and predecessor rank equations and coefficient-one block lowering.

Let Omega=Fin(m)×Fin(s), fix i in Fin(m), and let O_i consist of those vertices whose first coordinate differs from i. Rank(m,s,r) is the type of all r-element subsets of Omega; Space(m,s,r) is its complex counting Euclidean space. PreviousRank consists of subsets T with card(T)+1=r, and PreviousSpace uses the same counting convention. Thus at r=0 the predecessor type is empty, rather than the rank-zero singleton.

Every outside index R is an actual finset of O_i. Fiber(R) consists of inside finsets A with card(R)+card(A)=r. PreviousFiber(R) instead requires card(R)+card(A)+1=r. Invalid source ranks therefore give empty fibers automatically. In particular, an outside set of cardinality greater than r does not acquire a spurious rank-zero state through truncated subtraction. Distinct outside sets of the same size remain distinct summands.

**Definition 1.1 (The original vertex partition).**

$$\forall (m: \operatorname{Nat}), (\forall (s: \operatorname{Nat}), (\forall (i: \operatorname{Fin}\left(m\right)), (\operatorname{siteSplit}\left(m, s, i\right): \operatorname{Equiv}\left(\operatorname{SumType}\left(\operatorname{Outside}\left(m, s, i\right), \operatorname{Fin}\left(s\right)\right), \operatorname{Sites}\left(m, s\right)\right))))$$

*Formalization.* `D5/S3/Quantum/SpinChains/TokenBlockLocalDefect.siteSplit` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

All subtype proof fields are suppressed; the additive cardinality predicates are part of the displayed carriers.

**Definition 1.2 (All occupied subsets).**

$$\forall (m: \operatorname{Nat}), (\forall (s: \operatorname{Nat}), (\forall (r: \operatorname{Nat}), (\forall (i: \operatorname{Fin}\left(m\right)), (\operatorname{rankSplit}\left(m, s, r, i\right): \operatorname{Equiv}\left(\operatorname{Rank}\left(m, s, r\right), \operatorname{Sigma}\left(\operatorname{Finset}\left(\operatorname{Outside}\left(m, s, i\right)\right), R\mapsto\operatorname{Fiber}\left(m, s, r, i, R\right)\right)\right)))))$$

*Formalization.* `D5/S3/Quantum/SpinChains/TokenBlockLocalDefect.rankSplit` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

All subtype proof fields are suppressed; the additive cardinality predicates are part of the displayed carriers.

**Definition 1.3 (All predecessor subsets).**

$$\forall (m: \operatorname{Nat}), (\forall (s: \operatorname{Nat}), (\forall (r: \operatorname{Nat}), (\forall (i: \operatorname{Fin}\left(m\right)), (\operatorname{previousSplit}\left(m, s, r, i\right): \operatorname{Equiv}\left(\operatorname{PreviousRank}\left(m, s, r\right), \operatorname{Sigma}\left(\operatorname{Finset}\left(\operatorname{Outside}\left(m, s, i\right)\right), R\mapsto\operatorname{PreviousFiber}\left(m, s, r, i, R\right)\right)\right)))))$$

*Formalization.* `D5/S3/Quantum/SpinChains/TokenBlockLocalDefect.previousSplit` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

All subtype proof fields are suppressed; the additive cardinality predicates are part of the displayed carriers.

**Definition 1.4 (The counting isometry).**

$$\forall (m: \operatorname{Nat}), (\forall (s: \operatorname{Nat}), (\forall (r: \operatorname{Nat}), (\forall (i: \operatorname{Fin}\left(m\right)), (\operatorname{split}\left(m, s, r, i\right): \operatorname{LinearIsometryEquivC}\left(\operatorname{Space}\left(m, s, r\right), \operatorname{PiLp}\left(2, R\mapsto\operatorname{FiberSpace}\left(m, s, r, i, R\right)\right)\right)))))$$

*Formalization.* `D5/S3/Quantum/SpinChains/TokenBlockLocalDefect.split` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

All subtype proof fields are suppressed; the additive cardinality predicates are part of the displayed carriers.

**Definition 1.5 (The predecessor counting isometry).**

$$\forall (m: \operatorname{Nat}), (\forall (s: \operatorname{Nat}), (\forall (r: \operatorname{Nat}), (\forall (i: \operatorname{Fin}\left(m\right)), (\operatorname{previousCountingSplit}\left(m, s, r, i\right): \operatorname{LinearIsometryEquivC}\left(\operatorname{PreviousSpace}\left(m, s, r\right), \operatorname{PiLp}\left(2, R\mapsto\operatorname{PreviousFiberSpace}\left(m, s, r, i, R\right)\right)\right)))))$$

*Formalization.* `D5/S3/Quantum/SpinChains/TokenBlockLocalDefect.previousCountingSplit` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

All subtype proof fields are suppressed; the additive cardinality predicates are part of the displayed carriers.

**Definition 1.6 (The physical coefficient-one lowering map).**

$$\forall (m: \operatorname{Nat}), (\forall (s: \operatorname{Nat}), (\forall (r: \operatorname{Nat}), (\forall (i: \operatorname{Fin}\left(m\right)), (\forall (f: \operatorname{Space}\left(m, s, r\right)), (\forall (T: \operatorname{PreviousRank}\left(m, s, r\right)), (\operatorname{lower}\left(m, s, r, i, f\right)\left(T\right) = \sum_{a:\operatorname{Fin}\left(s\right)} \operatorname{ite}\left((i,a) \in T, 0, f\left(\operatorname{insert}\left((i,a), T\right)\right)\right)))))))$$

*Formalization.* `D5/S3/Quantum/SpinChains/TokenBlockLocalDefect.lower` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

All subtype proof fields are suppressed; the additive cardinality predicates are part of the displayed carriers.

**Definition 1.7 (The physical block number).**

$$\forall (m: \operatorname{Nat}), (\forall (s: \operatorname{Nat}), (\forall (r: \operatorname{Nat}), (\forall (i: \operatorname{Fin}\left(m\right)), (\forall (f: \operatorname{Space}\left(m, s, r\right)), (\forall (T: \operatorname{Rank}\left(m, s, r\right)), (\operatorname{number}\left(m, s, r, i, f\right)\left(T\right) = \operatorname{ofNatC}\left(\operatorname{card}\left(\operatorname{filterBlock}\left(i, T\right)\right)\right) \cdot f\left(T\right)))))))$$

*Formalization.* `D5/S3/Quantum/SpinChains/TokenBlockLocalDefect.number` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

All subtype proof fields are suppressed; the additive cardinality predicates are part of the displayed carriers.

**Definition 1.8 (The physical local defect).**

$$\forall (m: \operatorname{Nat}), (\forall (s: \operatorname{Nat}), (\forall (r: \operatorname{Nat}), (\forall (i: \operatorname{Fin}\left(m\right)), (\operatorname{defect}\left(m, s, r, i\right) = \operatorname{comp}\left(\operatorname{number}\left(m, s, r, i\right), \left(\operatorname{ofNatC}\left(s\right) + 1\right) \cdot \operatorname{Id}\left(\operatorname{Space}\left(m, s, r\right)\right) - \operatorname{number}\left(m, s, r, i\right)\right) - \operatorname{comp}\left(\operatorname{adjoint}\left(\operatorname{lower}\left(m, s, r, i\right)\right), \operatorname{lower}\left(m, s, r, i\right)\right)))))$$

*Formalization.* `D5/S3/Quantum/SpinChains/TokenBlockLocalDefect.defect` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

All subtype proof fields are suppressed; the additive cardinality predicates are part of the displayed carriers.

**Definition 1.9 (The actual block permutation).**

$$\forall (m: \operatorname{Nat}), (\forall (s: \operatorname{Nat}), (\forall (r: \operatorname{Nat}), (\forall (i: \operatorname{Fin}\left(m\right)), (\forall (pi: \operatorname{Perm}\left(\operatorname{Fin}\left(s\right)\right)), (\operatorname{rankPermutation}\left(m, s, r, i, pi\right): \operatorname{Perm}\left(\operatorname{Rank}\left(m, s, r\right)\right))))))$$

*Formalization.* `D5/S3/Quantum/SpinChains/TokenBlockLocalDefect.rankPermutation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

All subtype proof fields are suppressed; the additive cardinality predicates are part of the displayed carriers.

**Definition 1.10 (The inverse pullback action).**

$$\forall (m: \operatorname{Nat}), (\forall (s: \operatorname{Nat}), (\forall (r: \operatorname{Nat}), (\forall (i: \operatorname{Fin}\left(m\right)), (\forall (pi: \operatorname{Perm}\left(\operatorname{Fin}\left(s\right)\right)), (\operatorname{permutationAction}\left(m, s, r, i, pi\right): \operatorname{LinearIsometryEquivC}\left(\operatorname{Space}\left(m, s, r\right), \operatorname{Space}\left(m, s, r\right)\right))))))$$

*Formalization.* `D5/S3/Quantum/SpinChains/TokenBlockLocalDefect.permutationAction` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

All subtype proof fields are suppressed; the additive cardinality predicates are part of the displayed carriers.

**Definition 1.11 (The independently defined fixed subspace).**

$$\forall (m: \operatorname{Nat}), (\forall (s: \operatorname{Nat}), (\forall (r: \operatorname{Nat}), (\forall (i: \operatorname{Fin}\left(m\right)), (\operatorname{invariantSubspace}\left(m, s, r, i\right) = \{f: \operatorname{Space}\left(m, s, r\right) \mid \forall (pi: \operatorname{Perm}\left(\operatorname{Fin}\left(s\right)\right)), (\operatorname{permutationAction}\left(m, s, r, i, pi, f\right) = f)\}))))$$

*Formalization.* `D5/S3/Quantum/SpinChains/TokenBlockLocalDefect.invariantSubspace` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

All subtype proof fields are suppressed; the additive cardinality predicates are part of the displayed carriers.

**Definition 1.12 (The invariant orthogonal projection).**

$$\forall (m: \operatorname{Nat}), (\forall (s: \operatorname{Nat}), (\forall (r: \operatorname{Nat}), (\forall (i: \operatorname{Fin}\left(m\right)), (\operatorname{projection}\left(m, s, r, i\right) = \operatorname{starProjection}\left(\operatorname{invariantSubspace}\left(m, s, r, i\right)\right)))))$$

*Formalization.* `D5/S3/Quantum/SpinChains/TokenBlockLocalDefect.projection` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

All subtype proof fields are suppressed; the additive cardinality predicates are part of the displayed carriers.

For a permutation pi of Fin(s), rankPermutation maps each occupied subset by prodExtendRight(i,pi): it sends (i,a) to (i,pi(a)) and fixes every outside vertex. permutationAction is the counting linear isometry obtained by pulling coefficients back along the inverse of that subset permutation. invariantSubspace is the fixed subspace of all these actions, and projection is its orthogonal starProjection. This definition imposes no invariance hypothesis on f and uses no averaging formula.

The inverse subset map sends (R,A) to the disjoint union of the outside inclusion of R and {(i,a):a in A}. No coefficient or norm is rescaled. Hence the inner product of f and g is the sum, over all actual R, of the counting inner products of their restrictions; the same identity holds for squared norms. The predecessor decomposition includes the fibers card(R)+s+1=r even though they have no source states. A coefficient-one lowering map must have zero output on these fibers.

The intended local estimate on the complete carrier is s‖f−P_i f‖²≤Re⟨f,D_i f⟩. Here P_i is independently the orthogonal projection onto the vectors fixed by every permutation of block i. In these coordinates a block permutation fixes R and permutes A. Equal-cardinality subset transitivity makes its invariant vectors precisely the functions constant in A separately for each R. Orthogonality to the zero-sum functions identifies P_i with the counting average on each nonempty fiber.

For q=r−card(R) with card(R)≤r and q≤s, the fiber is exactly NativeJohnsonCoercivity.Rank(s,q). Insertion inside the block preserves R, so the physical lowering restricted to this fiber is NativeJohnsonCoercivity.lower(s,q), including its coefficient one. Counting inner products determine the corresponding adjoint. The block number is q on this fiber; consequently the physical defect restricts to NativeJohnsonCoercivity.defect(s,q). NativeJohnsonCoercivity.result then supplies the local estimate on that fiber. Summing uses the same f in every restriction and introduces no probability weights or binomial factors.

A complete identification also requires the equality with the Johnson Laplacian and the sum of I minus each unordered block transposition. The subset partition and physical definitions alone do not establish those identities, the projection identity, or the physical estimate. They do not assert complement covariance, the token-adjacency expansion, global occupancy and norm accounting, tensor spectral positivity, or the variational conclusions. The local objects use no graph, parity, unit-norm, factorization or input-symmetry hypothesis.

## References

- Truth anchor: `D5/S3/Quantum/SpinChains/TokenBlockLocalDefect.defect`
- Truth anchor: `D5/S3/Quantum/SpinChains/TokenBlockLocalDefect.invariantSubspace`
- Truth anchor: `D5/S3/Quantum/SpinChains/TokenBlockLocalDefect.lower`
- Truth anchor: `D5/S3/Quantum/SpinChains/TokenBlockLocalDefect.number`
- Truth anchor: `D5/S3/Quantum/SpinChains/TokenBlockLocalDefect.permutationAction`
- Truth anchor: `D5/S3/Quantum/SpinChains/TokenBlockLocalDefect.previousCountingSplit`
- Truth anchor: `D5/S3/Quantum/SpinChains/TokenBlockLocalDefect.previousSplit`
- Truth anchor: `D5/S3/Quantum/SpinChains/TokenBlockLocalDefect.projection`
- Truth anchor: `D5/S3/Quantum/SpinChains/TokenBlockLocalDefect.rankPermutation`
- Truth anchor: `D5/S3/Quantum/SpinChains/TokenBlockLocalDefect.rankSplit`
- Truth anchor: `D5/S3/Quantum/SpinChains/TokenBlockLocalDefect.siteSplit`
- Truth anchor: `D5/S3/Quantum/SpinChains/TokenBlockLocalDefect.split`
- Dependency: [D5/S3/Quantum/SpinChains/NativeJohnsonCoercivity](NativeJohnsonCoercivity.md)
