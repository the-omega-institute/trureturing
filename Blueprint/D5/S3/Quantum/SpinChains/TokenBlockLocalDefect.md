# Outside-occupancy coordinates for the local Boolean defect

## Abstract

The physical block projection is counting average on each actual outside occupied set, and the coefficient-one local defect controls the complete complex residual.

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

**Theorem 1.13 (Counting slices of the independent projection).**

$$\forall (m: \operatorname{Nat}), (\forall (s: \operatorname{Nat}), (\forall (r: \operatorname{Nat}), (\forall (i: \operatorname{Fin}\left(m\right)), (\forall (f: \operatorname{Space}\left(m, s, r\right)), (\forall (R: \operatorname{Finset}\left(\operatorname{Outside}\left(m, s, i\right)\right)), (\operatorname{split}\left(m, s, r, i, \operatorname{projection}\left(m, s, r, i, f\right), R\right) = \operatorname{toLp}\left(2, A\mapsto\operatorname{invC}\left(\operatorname{ofNatC}\left(\operatorname{card}\left(\operatorname{Fiber}\left(m, s, r, i, R\right)\right)\right)\right) \cdot \sum_{B: \operatorname{Fiber}\left(m, s, r, i, R\right)} \operatorname{split}\left(m, s, r, i, f, R\right)\left(B\right)\right)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/SpinChains/TokenBlockLocalDefect.projection_counting_slices` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In these coordinates a block permutation fixes every vertex of R and maps A by the same inside permutation. Any two equal-cardinality inside subsets are related by a permutation, so the fixed vectors are precisely the functions constant on each entire fiber. The residual from its counting average has zero sum on every fiber and is orthogonal to every such fixed vector, using the complex conjugate in the first inner-product argument. Orthogonal-projection uniqueness identifies the independently defined starProjection. The inverse invC has value zero at zero; empty fibers are zero dimensional and need no nonzero-cardinality assumption.

**Theorem 1.14 (The exact physical energy).**

$$\forall (m: \operatorname{Nat}), (\forall (s: \operatorname{Nat}), (\forall (r: \operatorname{Nat}), (\forall (i: \operatorname{Fin}\left(m\right)), (\forall (f: \operatorname{Space}\left(m, s, r\right)), (\operatorname{re}\left(\operatorname{innerC}\left(f, \operatorname{defect}\left(m, s, r, i, f\right)\right)\right) = \sum_{R: \operatorname{Finset}\left(\operatorname{Outside}\left(m, s, i\right)\right)} \operatorname{ofNatR}\left(\operatorname{tsub}\left(r, \operatorname{card}\left(R\right)\right)\right) \cdot \left(\operatorname{ofNatR}\left(s\right) + 1 - \operatorname{ofNatR}\left(\operatorname{tsub}\left(r, \operatorname{card}\left(R\right)\right)\right)\right) \cdot \operatorname{norm}\left(\operatorname{split}\left(m, s, r, i, f, R\right)\right)^{2} - \operatorname{norm}\left(\operatorname{lower}\left(m, s, r, i, f\right)\right)^{2})))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/SpinChains/TokenBlockLocalDefect.energy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Write q=tsub(r,card(R)), where tsub is natural truncated subtraction. Whenever a source fiber is inhabited its additive rank equation gives card(A)=q, so the original block-number polynomial acts by q(s+1−q). Empty source fibers contribute zero even when this scalar is outside the valid occupancy range. The adjoint identity gives Re⟨f,L_i*L_i f⟩=‖L_i f‖² on the full predecessor counting space. The displayed identity keeps every original predecessor coordinate, with no weights or normalization factors.

**Theorem 1.15 (Physical local coercivity).**

$$\forall (m: \operatorname{Nat}), (\forall (s: \operatorname{Nat}), (\forall (r: \operatorname{Nat}), (\forall (i: \operatorname{Fin}\left(m\right)), (\forall (f: \operatorname{Space}\left(m, s, r\right)), (\operatorname{ofNatR}\left(s\right) \cdot \operatorname{norm}\left(f - \operatorname{projection}\left(m, s, r, i, f\right)\right)^{2} \le \operatorname{re}\left(\operatorname{innerC}\left(f, \operatorname{defect}\left(m, s, r, i, f\right)\right)\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/SpinChains/TokenBlockLocalDefect.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Apply NativeJohnsonCoercivity.result with N=s and rank q separately on each inhabited source fiber. The exact counting equivalence preserves its norm and average, and the coefficient-one insertion formula intertwines its lowering with the physical lowering slice. Empty source fibers have zero lowering slice, including predecessor fibers with card(R)+s+1=r. Summing the native estimates and using the exact energy and projection formulas gives the physical bound for every complex f. It includes odd s, all total-rank endpoints, and nonsymmetric inputs; no graph, parity, unit norm or factorization premise is used.

For q=r−card(R) with card(R)≤r and q≤s, the fiber is exactly NativeJohnsonCoercivity.Rank(s,q). Insertion inside the block preserves R, so the physical lowering restricted to this fiber is NativeJohnsonCoercivity.lower(s,q), including its coefficient one. The block number is q. The exact physical energy therefore sums the native quadratic contributions q(s+1−q)‖f_R‖²−‖lower(s,q)f_R‖². NativeJohnsonCoercivity.result supplies the local estimate on every inhabited fiber. Summing uses the same f in every restriction and introduces no probability weights or binomial factors.

The equality with the independently defined Johnson exchange Laplacian and with the sum of I minus each unordered block transposition requires a separate incidence and exchange correspondence. The local projection, energy and coercivity statements do not assert that correspondence, complement covariance, the token-adjacency expansion, global occupancy accounting, tensor spectral positivity, or the variational conclusions.

## References

- Truth anchor: `D5/S3/Quantum/SpinChains/TokenBlockLocalDefect.defect`
- Truth anchor: `D5/S3/Quantum/SpinChains/TokenBlockLocalDefect.energy`
- Truth anchor: `D5/S3/Quantum/SpinChains/TokenBlockLocalDefect.invariantSubspace`
- Truth anchor: `D5/S3/Quantum/SpinChains/TokenBlockLocalDefect.lower`
- Truth anchor: `D5/S3/Quantum/SpinChains/TokenBlockLocalDefect.number`
- Truth anchor: `D5/S3/Quantum/SpinChains/TokenBlockLocalDefect.permutationAction`
- Truth anchor: `D5/S3/Quantum/SpinChains/TokenBlockLocalDefect.previousCountingSplit`
- Truth anchor: `D5/S3/Quantum/SpinChains/TokenBlockLocalDefect.previousSplit`
- Truth anchor: `D5/S3/Quantum/SpinChains/TokenBlockLocalDefect.projection`
- Truth anchor: `D5/S3/Quantum/SpinChains/TokenBlockLocalDefect.projection_counting_slices`
- Truth anchor: `D5/S3/Quantum/SpinChains/TokenBlockLocalDefect.rankPermutation`
- Truth anchor: `D5/S3/Quantum/SpinChains/TokenBlockLocalDefect.rankSplit`
- Truth anchor: `D5/S3/Quantum/SpinChains/TokenBlockLocalDefect.result`
- Truth anchor: `D5/S3/Quantum/SpinChains/TokenBlockLocalDefect.siteSplit`
- Truth anchor: `D5/S3/Quantum/SpinChains/TokenBlockLocalDefect.split`
- Dependency: [D5/S3/Quantum/SpinChains/NativeJohnsonCoercivity](NativeJohnsonCoercivity.md)
