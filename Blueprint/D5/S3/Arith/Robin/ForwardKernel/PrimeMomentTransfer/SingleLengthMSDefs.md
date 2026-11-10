# Single-length prime moments

## Abstract

Single-length prime moments and their correlation hypotheses.

Let E(x)=psi(x)-x and D(v,x)=E(x+v)-E(x). The discrete moment sums D(K,n)^k over 1<=n<=N. The main term has coefficient one for k=2 and three for k=4, and integrates (log(y/v)+B)^(k/2), where B=1-gamma-log(2*pi). MS20 gives the correlation error bound on a specified family of integer lengths. MSThirdTheorem is an explicit hypothesis giving Montgomery–Soundararajan's second and fourth moment estimates, with first error exponents -1/16 and -1/32 respectively.

**Definition 1.1 (Chebyshev error).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SingleLengthMSDefs.chebyshevError`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SingleLengthMSDefs.chebyshevError` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The complete Chebyshev error is E(x)=psi(x)-x.

**Definition 1.2 (Prime increment).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SingleLengthMSDefs.primeIncrement`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SingleLengthMSDefs.primeIncrement` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The centered prime increment of length v at x is E(x+v)-E(x), where E=psi-id.

**Definition 1.3 (Montgomery soundararajan constant).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SingleLengthMSDefs.montgomerySoundararajanConstant`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SingleLengthMSDefs.montgomerySoundararajanConstant` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The logarithmic constant B is one minus the Euler–Mascheroni constant minus log(2 pi).

**Definition 1.4 (Discrete prime moment).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SingleLengthMSDefs.discretePrimeMoment`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SingleLengthMSDefs.discretePrimeMoment` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The discrete moment of order k at integer cutoff N and length K is the sum of the kth powers of E(n+K)-E(n) over 1<=n<=N.

**Definition 1.5 (Continuous prime moment).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SingleLengthMSDefs.continuousPrimeMoment`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SingleLengthMSDefs.continuousPrimeMoment` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The continuous moment of order k is the integral of (E(x+v)-E(x))^k from one to Y.

**Definition 1.6 (Montgomery soundararajan main term).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SingleLengthMSDefs.montgomerySoundararajanMainTerm`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SingleLengthMSDefs.montgomerySoundararajanMainTerm` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For k=2 or k=4, the main term is mu_k v^(k/2) times the integral of (log(y/v)+B)^(k/2) from one to Y, with mu_2=1 and mu_4=3.

**Definition 1.7 (Montgomery soundararajan error).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SingleLengthMSDefs.montgomerySoundararajanError`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SingleLengthMSDefs.montgomerySoundararajanError` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The error envelope is Y (log Y)^(k/2) v^(k/2) (v/log Y)^(-1/(8k)) plus v^k Y^(1/2+epsilon).

**Definition 1.8 (Ms20).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SingleLengthMSDefs.MS20`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SingleLengthMSDefs.MS20` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Equation (20) bounds the correlation error for every order from one through k, every tuple of distinct positive shifts at most K, and every real cutoff between zero and N, by A N^(1/2+epsilon). For each positive epsilon, one positive A works for all sufficiently large N and every K in the specified length family.

**Definition 1.9 (Msthird theorem).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SingleLengthMSDefs.MSThirdTheorem`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SingleLengthMSDefs.MSThirdTheorem` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Montgomery–Soundararajan 2004 Theorem 3 is assumed for k=2 and k=4 under their correlation hypothesis (20), restricted to a specified family of integer lengths. The correlation hypothesis is needed only at each pair (N, K) under consideration, so the same uniform estimate applies on any specified length family. For each positive epsilon, one positive constant bounds the discrete moment minus its logarithmic main term by the explicit error envelope, uniformly for sufficiently large N and log N<=K<=N^(1/k) in that family.

**Definition 1.10 (Polynomial length family).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SingleLengthMSDefs.polynomialLengthFamily`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SingleLengthMSDefs.polynomialLengthFamily` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The polynomial length family consists of natural cutoffs N and lengths K satisfying K<=M N^beta.

**Theorem 1.11 (Restricted correlation errors).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SingleLengthMSDefs.hl4_implies_ms20`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SingleLengthMSDefs.hl4_implies_ms20` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For k<=4 and M>=1, the strong Hardy–Littlewood bound with the concrete singular series implies MS20 uniformly for K<=M*N^beta. The real correlation cutoff is restricted to 0<=y<=N.

**Theorem 1.12 (Integer-length increments).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SingleLengthMSDefs.integer_increment`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SingleLengthMSDefs.integer_increment` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For natural n and K, D(K,n) equals the sum of Lambda(n+d)-1 over the integers 1<=d<=K. This identifies the discrete moments with the interval sums used in cumulative sampling.

**Theorem 1.13 (Flooring the lattice length).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SingleLengthMSDefs.real_length_cell`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SingleLengthMSDefs.real_length_cell` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For v>=0 and natural n, the interval sum S(v,0,1,n) equals D(floor(v),n). The integer shifts and the centering both use the natural floor of v.

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SingleLengthMSDefs.MS20`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SingleLengthMSDefs.MSThirdTheorem`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SingleLengthMSDefs.chebyshevError`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SingleLengthMSDefs.continuousPrimeMoment`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SingleLengthMSDefs.discretePrimeMoment`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SingleLengthMSDefs.hl4_implies_ms20`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SingleLengthMSDefs.integer_increment`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SingleLengthMSDefs.montgomerySoundararajanConstant`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SingleLengthMSDefs.montgomerySoundararajanError`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SingleLengthMSDefs.montgomerySoundararajanMainTerm`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SingleLengthMSDefs.polynomialLengthFamily`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SingleLengthMSDefs.primeIncrement`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SingleLengthMSDefs.real_length_cell`
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/ContinuousSampling](ContinuousSampling.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/VarianceTransferDefs](../VarianceTransferDefs.md)
