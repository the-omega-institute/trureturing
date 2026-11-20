# Exponent-one primes in cubic golden blocks

## Abstract

Ten actual cubic golden blocks have certified primes of initial Fibonacci depth one.

**Theorem 1.1 (Non-powerful Lucas blocks and exact Fibonacci ranks).**

Lean statement: `D5/S3/Arith/Primes/GoldenCubicBlockExponentOne.checked_block_and_rank`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Primes/GoldenCubicBlockExponentOne.checked_block_and_rank` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For ten selected positive levels j, reduce the actual Lucas recurrence modulo the square of a proposed prime p. The residue of L_(3^j)^2 + 3 is a nonzero multiple of p. A factored p - 1 and modular order tests certify primality. Each block is therefore non-powerful, and the chosen prime has exact Fibonacci rank 2 * 3^(j + 1) and valuation one at that rank.

**Theorem 1.2 (Independent original Fibonacci test).**

Lean statement: `D5/S3/Arith/Primes/GoldenCubicBlockExponentOne.checked_wss_test`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Primes/GoldenCubicBlockExponentOne.checked_wss_test` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each chosen prime is one or four modulo five. A separate fast-doubling calculation gives a nonzero multiple of p for F_(p - 1) modulo p squared. Thus p divides the original split-prime test value but p squared does not.

The levels are 6, 7, 10, 15, 16, 17, 23, 26, 27 and 29. The calculation uses bounded residues, not complete block factorization. It neither excludes all-WSS blocks at other levels nor settles the existence of a Wall–Sun–Sun prime.

## References

- Truth anchor: `D5/S3/Arith/Primes/GoldenCubicBlockExponentOne.checked_block_and_rank`
- Truth anchor: `D5/S3/Arith/Primes/GoldenCubicBlockExponentOne.checked_wss_test`
- Dependency: [D5/S3/Arith/Powerful/PowerfulNumber](../Powerful/PowerfulNumber.md)
- Dependency: [D5/S3/Arith/Primes/GoldenCubicBlockRanks](GoldenCubicBlockRanks.md)
