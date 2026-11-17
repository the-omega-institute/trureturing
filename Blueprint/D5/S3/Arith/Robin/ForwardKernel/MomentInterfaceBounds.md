# Normalized even-moment bounds

## Abstract

Even-moment increment estimates give uniform normalized moments under logarithmic dyadic sampling.

**Theorem 1.1 (Normalization of a raw even moment).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/MomentInterfaceBounds.normalized_even_moment_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/MomentInterfaceBounds.normalized_even_moment_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let E be Borel measurable and bounded on compact intervals, theta>=0, K>=0, and m a natural number. Suppose that for all sufficiently large X, uniformly for s in [0,1], the integral of |E(x+s*x^theta)-E(x)|^(2*m) over [X,2X] is at most K*X*(X^theta*log(X))^m. Then the 2*m-th absolute moment of (E(x+s*x^theta)-E(x))/sqrt(x^theta*log(x)) under dx/(x*log(2)) on [X,2X] is eventually at most K/log(2), uniformly for s in [0,1]. The conclusion also includes m=0 and theta=0.

For X>1 and x in [X,2X], the inequalities x>=X and x^theta*log(x)>=X^theta*log(X)>0 bound the full denominator below by X*(X^theta*log(X))^m. Local boundedness and measurability of E along continuous moving endpoints give compact integrability, permitting integration of this comparison. The raw bound cancels the scale, leaving only the probability density factor 1/log(2).

**Theorem 1.2 (Uniform second absolute moments).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/MomentInterfaceBounds.second_moment_bound_interface`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/MomentInterfaceBounds.second_moment_bound_interface` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let E be Borel measurable and bounded on compact intervals, with 0<alpha<theta<beta<1, and assume the cumulative variance asymptotic on [alpha,beta]. There exists C>=0 such that for every sufficiently large X and every s in [0,1], the second absolute moment of the normalized increment under logarithmic dyadic sampling is at most C.

The uniform moving-increment square estimate gives a raw bound K*X*X^theta*log(X). Applying the even-moment normalization with m=1 yields C=K/log(2).

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/MomentInterfaceBounds.normalized_even_moment_bound`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/MomentInterfaceBounds.second_moment_bound_interface`
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/FourthMomentMovingBounds](FourthMomentMovingBounds.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/MomentTransferDefs](MomentTransferDefs.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/MovingIncrementVariance](MovingIncrementVariance.md)
