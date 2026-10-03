# Original odd-depth support

## Abstract

Under the prime-index odd-factor input, odd original depth bounds Fibonacci index and squarefree-kernel support.

Fix a positive index n, a finite set S of primes greater than five, and its Fibonacci rank closure H(S). Assume that each prime ell greater than five dividing n has a prime factor of F_ell with odd valuation. The prime-to-index valuation equality applies to factors p that do not divide n.

**Definition 1.1 (Prime-index input).**

Lean statement: `D5/S3/Arith/Primes/OriginalOddDepthSupport.PrimeIndexOddFactor`

*Formalization.* `D5/S3/Arith/Primes/OriginalOddDepthSupport.PrimeIndexOddFactor` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For each prime ell greater than five dividing n, some prime factor of the original F_ell has odd valuation.

**Definition 1.2 (Odd-depth squarefree kernel).**

Lean statement: `D5/S3/Arith/Primes/OriginalOddDepthSupport.oddDepthKernel`

*Formalization.* `D5/S3/Arith/Primes/OriginalOddDepthSupport.oddDepthKernel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The product of the distinct prime factors occurring to odd multiplicity in the original Fibonacci value F_n.

**Theorem 1.3 (Index and kernel support).**

Lean statement: `D5/S3/Arith/Primes/OriginalOddDepthSupport.original_odd_depth_support`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Primes/OriginalOddDepthSupport.original_odd_depth_support` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Suppose every prime factor p greater than five of F_n that does not divide n and has odd valuation at its first Fibonacci zero belongs to S. Then every prime factor of n belongs to H(S). The proof chooses the largest index prime outside H(S). A prime factor of its Fibonacci block is larger than that index prime and has that exact first-zero rank. If it divided n, maximality and closure would give a contradiction. It is therefore an external odd-depth factor, giving the same contradiction through S. Small primes belong to H(S) by definition, and factors dividing n belong to it by index support. The remaining odd-exponent factors belong to H(S) by the original-depth condition and the prime-to-index valuation formula. Thus the squarefree kernel divides the product of the primes in H(S).

## References

- Truth anchor: `D5/S3/Arith/Primes/OriginalOddDepthSupport.PrimeIndexOddFactor`
- Truth anchor: `D5/S3/Arith/Primes/OriginalOddDepthSupport.oddDepthKernel`
- Truth anchor: `D5/S3/Arith/Primes/OriginalOddDepthSupport.original_odd_depth_support`
- Dependency: [D5/S3/Arith/Primes/FibonacciPrimeToIndexValuation](FibonacciPrimeToIndexValuation.md)
