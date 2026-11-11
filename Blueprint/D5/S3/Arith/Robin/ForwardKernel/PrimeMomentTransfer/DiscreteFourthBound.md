# Discrete fourth moment bound

## Abstract

Discrete interval increments have a uniform fourth moment bound.

**Theorem 1.1 (Uniform discrete fourth power bound).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/DiscreteFourthBound.uniform_discrete_fourth_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/DiscreteFourthBound.uniform_discrete_fourth_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume normalized empty and singleton singular series, the four-point mean-square correlation bound, and the interval correlation estimates. For 0<alpha<beta<1/4 and M>=1, there is a nonnegative constant C such that, for all sufficiently large real N, the sum of |S(H,a,b,n)|^4 over N<n<=2N is at most C*N*(H*log N)^2, uniformly for integer lengths in the polynomial band and 0<=a<=b<=M. One can take C=3+3*M^2. The cutoff indicator of [1,2] has supremum plus total variation at most three, equals one at every discrete sample n/N, and has integral one. Applying the uniform fourth asymptotic with four equal intervals and tolerance one gives the bound because 0<=kappa<=1 and the overlap pairing is at most 3*M^2.

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/DiscreteFourthBound.uniform_discrete_fourth_bound`
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/CutoffWeights](CutoffWeights.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/DiscreteFourthAssembly](DiscreteFourthAssembly.md)
