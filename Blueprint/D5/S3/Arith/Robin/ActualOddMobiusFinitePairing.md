# Actual Odd Mobius Finite Pairing

## Abstract

Actual odd Mobius coefficients give exact finite dyadic reconstruction and clipped kernel pairing with its terminal payment.

Use the actual arithmetic Mobius function mu, the full positive prefix M(N)=sum from 1 to N of mu(n), and its odd restriction O(N). Every kernel P is a real-valued function on the actual integer inputs, with J(n)=P(n)-P(n+1).

**Theorem 1.1 (The exact odd pairing and terminal remainder).**

Lean statement: `D5/S3/Arith/Robin/ActualOddMobiusFinitePairing.result`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ActualOddMobiusFinitePairing.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural cutoff N, M(N)=O(N)-O(N/2), where natural division supplies the floor. Iteration terminates and gives O(N)=sum over all exponents a with 2^a<=N of M(N/2^a), including the empty sum at N=0.

For every real-valued kernel P and cutoff N, the exact sum of M(n)*J(n) from 1 to N equals the sum over odd m from 1 to N of mu(m)*(P(m)-P(min(2*m,N+1))). The inclusive cutoff, original unit source and final N+1 boundary are retained literally.

Subtracting the untruncated odd pairing sum mu(m)*(P(m)-P(2*m)) gives exactly the terminal sum over odd N/2<m<=N of mu(m)*(P(2*m)-P(N+1)). If 2*m=N+1 its bracket is exactly zero. Both even and odd cutoffs are covered.

Mathlib supplies the actual Mobius function, multiplicativity, squarefree vanishing, prime value, finite sum algebra and telescoping. The consumed parity coefficient and multiples bijection specialize the primeDifference supplier inside the existing FibonacciAtomic.MertensBoundary proof to prime 2 and modulus 1. The finite clipped pairing and terminal payment implement actual-prefix theory section 453.

These are finite identities that specialize directly to the original factorial-tail kernel. Passing to an infinite odd pairing requires a separate vanishing terminal estimate; no convergence, critical tail bound or RH conclusion is asserted.

## References

- Truth anchor: `D5/S3/Arith/Robin/ActualOddMobiusFinitePairing.result`
