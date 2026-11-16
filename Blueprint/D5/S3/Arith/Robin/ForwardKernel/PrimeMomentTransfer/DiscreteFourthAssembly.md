# Uniform discrete fourth moments

## Abstract

Discrete fourth moments approach the overlap pairing uniformly on polynomial length bands.

**Theorem 1.1 (Uniform fourth moment asymptotic).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/DiscreteFourthAssembly.eventual_discrete_fourth`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/DiscreteFourthAssembly.eventual_discrete_fourth` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume the empty and singleton singular series equal one, the four-point mean-square correlation bound, and the interval correlation estimates. For 0<alpha<beta<1/4, M>=1 and every delta>0, the discrete fourth mixed moment divided by N*(H*log N)^2 differs from the weight integral times kappa(N,H)^2 times the three overlap pairings by at most B*delta for all sufficiently large N. The threshold is uniform in integer lengths N^alpha<=H<=N^beta, interval endpoints, and weights whose supremum plus total variation is at most B and which vanish outside [1,2]. The normalized arithmetic error, correlation modulus, and inverse logarithm all tend to zero uniformly on this band.

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/DiscreteFourthAssembly.eventual_discrete_fourth`
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/DiscreteMomentAsymptotics](DiscreteMomentAsymptotics.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FourthMainIntegral](FourthMainIntegral.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/NormalizedFormalIntegrals](NormalizedFormalIntegrals.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/UniformRates](UniformRates.md)
