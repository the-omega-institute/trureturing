# The second-order dyadic interface

## Abstract

The variance band gives uniform weighted second moments and the second mixed-moment interface.

Let E be a locally bounded Borel measurable real function and assume 0<alpha<theta<beta<1 and the uniform cumulative variance asymptotic (490.2). These conditional second-order results supply no arithmetic proof for E=psi-id and no higher-order interfaces.

**Theorem 1.1 (Power length bounds).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/SecondOrderInterface.power_length_bounds`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/SecondOrderInterface.power_length_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If 0<theta<1 and 0<=s<=1, the function b(u)=s*u^theta is continuously differentiable on [1,2], takes values in [0,2], and has derivative of absolute value at most one. This supplies the length bounds for the second-order covariance and the higher moment transfer.

**Theorem 1.2 (An explicit second moment bound).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/SecondOrderInterface.explicit_second_moment_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/SecondOrderInterface.explicit_second_moment_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all sufficiently large X and every s in [0,1], the dyadic probability integral of |B_X(s)|^2 is at most 1760/log(2). The macroscopic lengths a(u)=s*u^theta have size at most two and derivative at most one. The uniform bound 880*M with M=2, followed by logarithmic probability normalization, gives the stated constant.

**Theorem 1.3 (A uniform time modulus).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/SecondOrderInterface.time_modulus`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/SecondOrderInterface.time_modulus` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every 0<delta<=1 and eta>0, eventually in X and uniformly for s,t in [0,1] with |s-t|<=delta, the dyadic probability integral of (B_X(s)-B_X(t))^2 is at most 120*delta/log(2)+eta. Apply the local moving-endpoint estimate to x+s*x^theta and x+t*x^theta, with R=2*delta*X^theta, derivative lower bound one and enclosing interval [X,2*X+2*X^theta]. The variance-window error and X^theta/X vanish before any time parameters are chosen.

**Theorem 1.4 (Uniform weighted Brownian covariance).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/SecondOrderInterface.weighted_covariance_uniform`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/SecondOrderInterface.weighted_covariance_uniform` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each continuous real phi on [1,2], the covariance of phi(U_X)*B_X(s)*B_X(t) converges uniformly over (s,t) in [0,1]^2 to kappa*min(s,t) times the integral of phi(u)/u on [1,2], divided by log(2). The macroscopic covariance theorem gives each fixed pair after replacing the local logarithm by log(X); the explicit second moment bound controls that replacement. The time modulus bounds covariance changes by Young's inequality. A finite net in the compact parameter square upgrades the fixed-pair limits to the uniform limit.

**Theorem 1.5 (The second mixed-moment interface).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/SecondOrderInterface.second_moment_interface`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/SecondOrderInterface.second_moment_interface` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The variance band implies MomentInterface at order two, with kernel kappa*dyadicMacroMoment(kappa)*min(s(0),s(1)). Choose phi(u)=u^kappa in the weighted covariance limit. The two-factor product and dyadic scaling exponent are exactly those in dyadicMixedMoment. The coefficient is the second-order dyadic power moment, distinct from the fourth-order moment constant.

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/SecondOrderInterface.explicit_second_moment_bound`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/SecondOrderInterface.power_length_bounds`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/SecondOrderInterface.second_moment_interface`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/SecondOrderInterface.time_modulus`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/SecondOrderInterface.weighted_covariance_uniform`
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/DyadicMacroMoments](DyadicMacroMoments.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/MacroscopicFreezing](MacroscopicFreezing.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/MacroscopicWeightedCovariance](MacroscopicWeightedCovariance.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/MomentInterfaceBounds](MomentInterfaceBounds.md)
