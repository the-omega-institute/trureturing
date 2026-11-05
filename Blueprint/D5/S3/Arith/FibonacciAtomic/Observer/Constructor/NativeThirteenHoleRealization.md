# Correlated finite realizations of the thirteen-hole rows

## Abstract

NativeThirteenHoleRealization

**Definition 1.1 (The guarded finite constructor).**

$$\forall x, t: Source, (\operatorname{G}\left(x, t\right) = \operatorname{pair}\left(x, \operatorname{pair}\left(\operatorname{substitution}\left(t\right), \operatorname{of}\left(true\right)\right)\right))$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeThirteenHoleRealization.G` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The constructor has two original pair levels. Its recursive argument is transformed by the native substitution, while its rightmost child is the original alpha leaf. The finite tail at parameters x, n and m is the n-fold iterate of this constructor on comb(m). The existing comb has comb(0)=alpha and comb(m+1)=pair(comb(m),alpha).

**Definition 1.2 (One canonical guarded completion).**

$$K = \operatorname{at}\left(\operatorname{canonicalSolution}\left(system, \operatorname{constant}\left(false\right), \operatorname{constant}\left(0\right)\right), 0\right)$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeThirteenHoleRealization.K` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The exact one-coordinate functional system has expression pair(token(0,0),pair(var(1,0),ground(alpha))). Its token has the divergent mode and hence denotes Omega. The supplied symbolic_finite_forcing solution law gives K=node(Omega,node(rho(K),alpha)). This defines the particular canonical tree used here; no standalone theorem named K is assumed. Lambda is the ordered thirteen-hole comb with ten copies of Omega followed by three copies of this same K.

**Definition 1.3 (Two fillings of the same finite tuple).**

$$\forall s: Bool, (\forall h: Nat, (\operatorname{theta}\left(s, h\right) = \operatorname{B}\left(12, \operatorname{values}\left(s, h\right)\right)))$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeThirteenHoleRealization.theta` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At a supplied h put a=2(h+1) and n=h+1. The shared tuple is x=rho^a(comb(1)), y=rho^(a+3)(comb(1)), z=rho^(a+6)(comb(1)), w=rho^(a+9)(comb(1)), v=G(x)^n(comb(4)). The ten-value table is x,y,z,w,rho(x),rho(y),pair(y,z),pair(x,w),v,G(x,v). Both rows use exactly this table. The false-side class map is [0,1,2,3,4,5,4,5,6,7,8,8,9]; the true-side map is [0,1,2,3,6,7,4,5,6,7,8,9,9]. Thus the false side fills s=rho(x),t=rho(y),c=v, and the true side fills s=pair(y,z),t=pair(x,w),c=G(x,v), in the same thirteen-hole U.

The supplied B_T(12), hole(12), locate, hole_locate and locate_eq retain the original comb geometry. Q is the image of all thirteen hole addresses. The row exterior is the entire comb with a distinct address marker at every hole. Its complete partition contains exactly the ordered Q pairs with equal displayed classes, including every diagonal and both orientations of every unordered bit. Original-present transport is used only after the finite source has been proved to reach the original hole.

**Definition 1.4 (Entire acquired input, complete rows and a common completed prefix).**

$$\forall h: Nat, (\forall u, v: Source, ((\operatorname{SignedJoint}\left(h, u, v\right)) \iff ((\operatorname{Acquired}\left(u\right)) \land ((\operatorname{Acquired}\left(v\right)) \land ((\operatorname{literalRecord}\left(Q, u\right) = \operatorname{row}\left(false\right)) \land ((\operatorname{literalRecord}\left(Q, v\right) = \operatorname{row}\left(true\right)) \land ((\forall i: \operatorname{Fin}\left(13\right), ((\operatorname{isSome}\left(\operatorname{subtree}\left(\operatorname{position}\left(i\right), u\right)\right)) \land (\operatorname{isSome}\left(\operatorname{subtree}\left(\operatorname{position}\left(i\right), v\right)\right)))) \land ((\operatorname{canonicalRow}\left(Q, u\right) = \operatorname{canonicalRow}\left(Q, \operatorname{theta}\left(false, 0\right)\right)) \land ((\operatorname{canonicalRow}\left(Q, v\right) = \operatorname{canonicalRow}\left(Q, \operatorname{theta}\left(true, 0\right)\right)) \land ((u \neq v) \land (\forall p: Address, ((\operatorname{length}\left(p\right) \le h) \implies ((\operatorname{readout}\left(p, u\right) = \operatorname{completionReadout}\left(p, Lambda\right)) \land (\operatorname{readout}\left(p, v\right) = \operatorname{completionReadout}\left(p, Lambda\right)))))))))))))))$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeThirteenHoleRealization.SignedJoint` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Acquired includes the attained complete one-root-hole row. Its literal list contains epoch-zero branch replies at R^j for j=0 through 11, at holes 9,10,13 and at hole 13 followed by R, together with the alpha reply at hole 13 followed by RR. The positive list is exactly (0,q7,1,q1), (0,q8,1,q2), (0,q9L,0,q2), (0,q9R,0,q3), (0,q10L,0,q1), (0,q10R,0,q4), (0,q13L,0,q1), (0,q13RL,1,q11). Every positive retains both reached guards. The negative list ranges over all unordered distinct pairs among holes 1,2,3,4,7,8,9,10,11,13, at epoch zero, with both reached guards.

The two literalRecord equalities specify the entire comb exterior and every partition bit. All thirteen holes are reached in each source. canonicalRow_record_iff also identifies each canonical row with its attained reference at h=0. The two originals differ because their full partitions differ. Agreement quantifies every address through the inclusive depth, including alpha and beta leaves and absent descendants below early leaves. No equality of cross-source finite feedback is required.

**Theorem 1.5 (Actual signed finite realizations at every inclusive depth).**

$$\forall h: Nat, (\operatorname{SignedJoint}\left(h, \operatorname{theta}\left(false, h\right), \operatorname{theta}\left(true, h\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeThirteenHoleRealization.actual_joint_realization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The guarded-prefix induction is uniform in prefix depth d, iterate count n, and comb seed m. If x and Omega have the same cutoff d and d is at most 2n, then G(x)^n(comb(m)) and K have the same cutoff d. At positive depth one constructor gives the branch root. At depth d+2 the two original pair levels reduce the recursive comparison to depth d, and the existing native cutoff transport preserves that comparison under rho. The alpha child is exact at every stage. The induction keeps the same x throughout.

Native iteration through 2(h+1) makes x full to cutoff h+1; the three offset iterates preserve its agreement with Omega. Applying the guarded-prefix induction at n=h+1 gives v the required prefix of K. Pair locality and the exact K equation then give both entire Theta outputs the prefix of the same Lambda. The convention cutoff(h+1) is required for inclusive h.

Mass distinguishes the six first values, the two pair helpers, and the two guarded values into groups of masses 1, 3, 4+3(h+1), and 4+3(h+2). Within the mass-one group the clocks are a+2,a+5,a+8,a+11,a+3,a+6; the mass-three clocks are a+10,a+13. Thus all ten values are distinct simultaneously. Every negative and all complete row bits follow for the same tuple. All finite outputs are computed by bounded native iteration and the fixed finite comb.

This establishes the forward actual-realization part of the signed thirteen-hole construction. It makes no claim of reverse classification on arbitrary original sources, uniqueness of a common closure point, non-rationality, a general recognizer, extraction algorithm, or resource bound.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeThirteenHoleRealization.G`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeThirteenHoleRealization.K`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeThirteenHoleRealization.SignedJoint`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeThirteenHoleRealization.actual_joint_realization`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeThirteenHoleRealization.theta`
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeFunctionalEffectivePrefix](NativeFunctionalEffectivePrefix.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/NativePayloadHistoryInstallation](../NativePayloadHistoryInstallation.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/NativeSharpPredecessorFiber](../NativeSharpPredecessorFiber.md)
