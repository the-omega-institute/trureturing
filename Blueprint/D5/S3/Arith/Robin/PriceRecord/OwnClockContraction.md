# The actual scalar own-clock: strict decrease of response minus identity

## Abstract

The actual scalar own-clock: strict decrease of response minus identity

Let S be a finite nonempty set of distinct naturals p>=2, theta=sum_S log p>1. For the actual Robin cutoff write c(L)=log(1+L log L) and T(L)=sum_S max(log p,c(L)-log p), on the whole closed ray L>=theta. The literal Phi is imported unchanged from OwnClockFixedSupport. The response estimate applies to every ray with arbitrary lower endpoint H>1; theta>1 is needed for the later minimum theorem.

Since theta>1, the ray is nonempty and every L>=theta satisfies L>1 and log L>0. The derivative of c is positive. Put R(L)=sqrt(1+L log L). The active set {p: p<=R(L)} has cardinal at most floor(R(L))-1<=R(L)-1, including the 1<R<2 case. The logarithmic estimate log L<2R(L)/3 gives 36(R-1)(1+log L)<=24R^2+12R-36<=25R^2, with final square (R-6)^2, so the right derivative is globally bounded by 25/36. At an exact max tie, c is increasing on the right ray and the active branch is used.

Supplier audit: the pinned image_le_of_deriv_right_le_deriv_boundary in Analysis/Calculus/MeanValue.lean consumes response continuity, right derivatives, the left endpoint comparison, affine-boundary continuity, affine-boundary right derivatives, and the derivative bound, in that order. HasDerivWithinAt.congr_of_mem handles the active branch on Ici L; congr_of_eventuallyEq handles the inactive branch with target=source eventual equality and equality at L. HasDerivWithinAt.fun_sum combines exactly the finite support. Nat.card_Ico is used before converting the cardinal inequality to reals. The upper IVT endpoint uses log(r^2)<=r^2-1 and an explicit algebraic bound at r=theta+4 card S; this 4 is an endpoint choice, not a support hypothesis. The max ties remain part of the closed-ray statement.

**Theorem 1.1 (The literal clock dominates theta).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/OwnClockContraction.theta_le_clock_of_naturalSupport`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/OwnClockContraction.theta_le_clock_of_naturalSupport` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every admissible original vector, each coordinate is at least one and every log p is positive, hence theta S<=clock S x. Only naturalSupport is required. This helper supplies the valid clock ray for attainment and KKT.

**Theorem 1.2 (The valid clock domain).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/OwnClockContraction.ray_bounds`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/OwnClockContraction.ray_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The theta>1 assumption pays nonemptiness and gives L>1 and log L>0 for every point of the ray. This helper is consumed by the actual derivative, continuity and KKT arguments.

**Theorem 1.3 (Invariance of the full closed ray).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/OwnClockContraction.response_selfmap`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/OwnClockContraction.response_selfmap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every max term is at least log p, so theta<=T(L). This fact needs no smoothness or primality and supplies the ray endpoint inequality.

**Theorem 1.4 (Strict decrease of T(L)-L on each compact interval, with all active-set ties retained).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/OwnClockContraction.response_strictAntiOn`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/OwnClockContraction.response_strictAntiOn` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On every compact interval [u,v] with 1<u<v, the global slope bound 25/36<1 and the right-derivative fence give responseClock(v)-v < responseClock(u)-u. The max inequality at ties is replaced by the increasing-right-branch derivative, so the proof does not differentiate through a kink.

**Theorem 1.5 (Global 25/36 response Lipschitz estimate).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/OwnClockContraction.response_global_lipschitz`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/OwnClockContraction.response_global_lipschitz` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every naturalSupport S and every pair of points on a ray with arbitrary lower endpoint H>1, the literal max response satisfies |T(t)-T(s)| <= (25/36)|t-s|. The proof uses the six-argument right-derivative fence with ties counted in the active branch and the scalar radius inequality above. This bound is consumed by the finite residual certificate.

**Theorem 1.6 (The scalar clock is constructed).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/OwnClockContraction.exists_unique_clock`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/OwnClockContraction.exists_unique_clock` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

There exists exactly one real Lstar>=theta satisfying T(Lstar)=Lstar. The proof uses the active-count bound, right derivatives on the closed ray at ties, the global envelope 25/36<1, IVT, and strict decrease of T(L)-L. OwnClockUniqueMinimum consumes this result.

## References

- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/OwnClockContraction.exists_unique_clock`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/OwnClockContraction.ray_bounds`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/OwnClockContraction.response_global_lipschitz`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/OwnClockContraction.response_selfmap`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/OwnClockContraction.response_strictAntiOn`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/OwnClockContraction.theta_le_clock_of_naturalSupport`
- Dependency: [D5/S3/Arith/Robin/PriceRecord/OwnClockFixedSupport](OwnClockFixedSupport.md)
