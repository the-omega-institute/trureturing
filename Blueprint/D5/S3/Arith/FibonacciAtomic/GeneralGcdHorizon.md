# Arbitrary-Modulus Fibonacci Gcd Prefixes

## Abstract

Prime-power Fibonacci gcd horizons combine into an arbitrary-modulus consecutive-prefix theorem.

**Definition 1.1 (Local prime-power threshold).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/GeneralGcdHorizon.localHorizon`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/GeneralGcdHorizon.localHorizon` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For e=1 this is the sharp prime horizon. For e>=2 it is the stagnant rank or the growth value (p-1) times the parent rank. The e=0 value is zero.

**Definition 1.2 (Global modulus threshold).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/GeneralGcdHorizon.globalHorizon`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/GeneralGcdHorizon.globalHorizon` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The threshold for H is the finite supremum of localHorizon(p,H.factorization p) over the prime divisors of H. It is zero for H=1.

**Theorem 1.3 (Signed arbitrary-modulus prefix transport).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/GeneralGcdHorizon.gcd_value_consecutive_prefix`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/GeneralGcdHorizon.gcd_value_consecutive_prefix` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If a positive prefix reaches every local threshold of a positive modulus H, equality of signed gcd readings on that prefix determines equality at every positive time. The proof recombines the prime-power gcd components by unique factorization.

**Theorem 1.4 (Natural-source prefix transport).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/GeneralGcdHorizon.actual_gcd_consecutive_prefix`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/GeneralGcdHorizon.actual_gcd_consecutive_prefix` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The same prefix condition determines all actual natural-source gcd futures, using the verified observation bridge from source coordinates to signed recurrence states.

**Theorem 1.5 (Finite supremum prefix theorem).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/GeneralGcdHorizon.actual_gcd_global_prefix`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/GeneralGcdHorizon.actual_gcd_global_prefix` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A prefix of length at least globalHorizon(H) determines every positive actual natural-source gcd reading for H. No initial quantity, primitive state, or residue-value observation is supplied for free.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/GeneralGcdHorizon.actual_gcd_consecutive_prefix`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/GeneralGcdHorizon.actual_gcd_global_prefix`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/GeneralGcdHorizon.gcd_value_consecutive_prefix`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/GeneralGcdHorizon.globalHorizon`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/GeneralGcdHorizon.localHorizon`
- Dependency: [D5/S3/Arith/FibonacciAtomic/GlobalGcdSampling](GlobalGcdSampling.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/PrimeGcdHorizon](PrimeGcdHorizon.md)
